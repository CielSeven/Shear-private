# guardgen/registry.py
from dataclasses import dataclass, field
import json
import os
import re
from typing import Any, Callable, Dict, List, Literal, Optional

PredKind = Literal["root", "segment"]

@dataclass
class PredicateSpec:
    name: str
    kind: PredKind            # "root" | "segment"
    arity: int
    parse_args: Callable[[list[str]], dict]
    to_coq_root_null: Optional[Callable[[dict, bool], str]] = None
    to_coq_segment_eq: Optional[Callable[[dict, bool, bool], str]] = None
    # Translate a ``<root>-><field> == null`` / ``!= null`` check to Coq.
    # Args: (payload, field_name, is_eq).  Raise to indicate the field deref
    # is not supported on this predicate.
    to_coq_field_deref_null: Optional[Callable[[dict, str, bool], str]] = None
    abs_names: Callable[[dict], list[str]] = lambda payload: []

PREDICATES: dict[str, PredicateSpec] = {}

# Trigger names used by ``translate.py`` to look up composition rules.
# Currently only ``root_null`` is consumed; adding more (``segment_eq``,
# ``field_deref_null``, ...) is a translator-side wiring change.
CompositionTrigger = Literal["root_null"]


@dataclass
class CompositionRule:
    """A cross-predicate rule that combines two or more spatial predicates
    into a single Coq guard expression.

    Loaded from the ``_composition_rules`` section of
    ``guard_predicates.json``.  Each rule specifies:

    - ``match``: an ordered list of clauses, each binding a *role name*
      (e.g. ``"S"``) to an atom of a given ``kind`` (``"segment"`` or
      ``"root"``) whose payload satisfies a ``where`` constraint.
      Constraint values may be literals or reference the running
      bindings via ``"$ptr"`` (the initial query pointer) or
      ``"$<role>.<field>"`` (another matched atom's payload field).
    - ``emit``: ``eq`` / ``ne`` format strings for the two polarities.
      Substitutions of the form ``{<role>.<field>}`` are replaced with
      the matched atom's payload field.
    """
    name: str
    description: str
    match: List[Dict[str, Any]]
    emit_eq: str
    emit_ne: str


COMPOSITION_RULES: Dict[CompositionTrigger, List[CompositionRule]] = {
    "root_null": [],
}


def register_predicate(spec: PredicateSpec) -> None:
    if spec.name in PREDICATES:
        raise ValueError(f"Predicate {spec.name} already registered")
    PREDICATES[spec.name] = spec


def register_composition_rule(trigger: CompositionTrigger, rule: CompositionRule) -> None:
    COMPOSITION_RULES.setdefault(trigger, []).append(rule)


# ---------------------------------------------------------------------------
# Composition-rule matcher
# ---------------------------------------------------------------------------


_SUB_RE = re.compile(r"\{([A-Za-z_]\w*\.[A-Za-z_]\w*)\}")
_REF_RE = re.compile(r"^\$([A-Za-z_]\w*)(?:\.([A-Za-z_]\w*))?$")


def _resolve_ref(expr: Any, bindings: Dict[str, Any], normalize_ptr) -> Any:
    """Resolve a JSON value to a comparable pointer/literal.

    Supports literal strings/numbers and the mini-DSL ``$name`` /
    ``$role.field`` references against the running bindings.
    """
    if not isinstance(expr, str):
        return expr
    m = _REF_RE.match(expr)
    if not m:
        return expr
    name, sub_field = m.group(1), m.group(2)
    if sub_field is None:
        val = bindings.get(name)
        return normalize_ptr(val) if isinstance(val, str) else val
    atom = bindings.get(name)
    if atom is None:
        return None
    val = atom.payload.get(sub_field)
    return normalize_ptr(val) if isinstance(val, str) else val


def _clause_matches(atom, where: Dict[str, Any], bindings: Dict[str, Any], normalize_ptr) -> bool:
    for payload_key, ref in where.items():
        expected = _resolve_ref(ref, bindings, normalize_ptr)
        actual = atom.payload.get(payload_key)
        if isinstance(actual, str):
            actual = normalize_ptr(actual)
        if expected is None or actual != expected:
            return False
    return True


def _match_rule(
    rule: CompositionRule,
    atoms_by_kind: Dict[str, list],
    initial_bindings: Dict[str, Any],
    normalize_ptr,
) -> Optional[Dict[str, Any]]:
    """Try to bind *rule*'s clauses against the atom pool.  Returns the
    role→atom binding dict on success, or ``None`` if no assignment
    satisfies all clauses.

    Uses depth-first search with role-binding backtracking — small
    pattern sets, small atom pools, so plain DFS is plenty.
    """
    def go(i: int, bindings: Dict[str, Any]) -> Optional[Dict[str, Any]]:
        if i >= len(rule.match):
            return bindings
        clause = rule.match[i]
        kind = clause["kind"]
        role = clause["role"]
        where = clause.get("where", {})
        for atom in atoms_by_kind.get(kind, []):
            if not _clause_matches(atom, where, bindings, normalize_ptr):
                continue
            next_bindings = dict(bindings)
            next_bindings[role] = atom
            result = go(i + 1, next_bindings)
            if result is not None:
                return result
        return None

    return go(0, dict(initial_bindings))


def render_composition_emit(rule: CompositionRule, bindings: Dict[str, Any], is_eq: bool) -> str:
    template = rule.emit_eq if is_eq else rule.emit_ne

    def sub(m: re.Match) -> str:
        role, field = m.group(1).split(".")
        atom = bindings[role]
        val = atom.payload.get(field)
        return str(val)

    return _SUB_RE.sub(sub, template)


_DATA_DIR = os.path.normpath(os.path.join(os.path.dirname(__file__), "..", "data"))
_GUARD_PREDICATE_FILE = os.path.join(_DATA_DIR, "guard_predicates.json")


def _make_parse_args(payload_map: dict[str, int], arity: int) -> Callable[[list[str]], dict]:
    def _parse(args: list[str]) -> dict:
        if len(args) != arity:
            raise ValueError(f"Expected {arity} args, got {args}")
        payload = {}
        for key, index in payload_map.items():
            payload[key] = args[index]
        return payload
    return _parse


def _make_root_null_handler(eq_template: str, ne_template: str) -> Callable[[dict, bool], str]:
    def _handler(payload: dict, is_eq: bool) -> str:
        template = eq_template if is_eq else ne_template
        return template.format(**payload)
    return _handler


def _make_segment_eq_handler(eq_template: str, ne_template: str) -> Callable[[dict, bool, bool], str]:
    def _handler(payload: dict, is_eq: bool, reversed_match: bool) -> str:
        template = eq_template if is_eq else ne_template
        return template.format(**payload)
    return _handler


def _make_field_deref_null_handler(
    spec_name: str, field_specs: dict
) -> Callable[[dict, str, bool], str]:
    """Build a handler that translates ``<root>-><field>`` null comparisons.

    *field_specs* maps each supported field name to a dict with ``eq`` and
    ``ne`` Python-format-string templates referencing the predicate's payload
    keys.
    """
    def _handler(payload: dict, field: str, is_eq: bool) -> str:
        templates = field_specs.get(field)
        if templates is None:
            supported = ", ".join(sorted(field_specs)) or "(none)"
            raise ValueError(
                f"{spec_name}: field deref '->{field}' is not supported "
                f"(supported fields: {supported})"
            )
        template = templates["eq"] if is_eq else templates["ne"]
        return template.format(**payload)

    return _handler


def _make_abs_names(abs_fields: list[str]) -> Callable[[dict], list[str]]:
    def _abs(payload: dict) -> list[str]:
        return [payload[field] for field in abs_fields]
    return _abs


def load_predicates_from_json(config_path: str = _GUARD_PREDICATE_FILE) -> None:
    with open(config_path, "r", encoding="utf-8") as f:
        data = json.load(f)

    # Composition rules live under a leading-underscore key so the existing
    # per-predicate loop below skips them transparently.
    composition = data.pop("_composition_rules", {})
    for trigger, rule_list in composition.items():
        for raw in rule_list:
            register_composition_rule(
                trigger,
                CompositionRule(
                    name=raw.get("name", "<unnamed>"),
                    description=raw.get("description", ""),
                    match=raw["match"],
                    emit_eq=raw["emit"]["eq"],
                    emit_ne=raw["emit"]["ne"],
                ),
            )

    for name, raw_spec in data.items():
        if name.startswith("_"):
            continue
        kind = raw_spec["kind"]
        arity = raw_spec["arity"]
        payload_map = {k: int(v) for k, v in raw_spec["payload"].items()}
        abs_fields = list(raw_spec.get("abs_names", []))

        root_null = raw_spec.get("root_null")
        segment_eq = raw_spec.get("segment_eq")
        field_deref_null = raw_spec.get("field_deref_null")

        register_predicate(PredicateSpec(
            name=name,
            kind=kind,
            arity=arity,
            parse_args=_make_parse_args(payload_map, arity),
            to_coq_root_null=(
                _make_root_null_handler(root_null["eq"], root_null["ne"])
                if root_null else None
            ),
            to_coq_segment_eq=(
                _make_segment_eq_handler(segment_eq["eq"], segment_eq["ne"])
                if segment_eq else None
            ),
            to_coq_field_deref_null=(
                _make_field_deref_null_handler(name, field_deref_null)
                if field_deref_null else None
            ),
            abs_names=_make_abs_names(abs_fields),
        ))
