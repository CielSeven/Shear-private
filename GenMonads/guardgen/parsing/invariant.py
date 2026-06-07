# guardgen/parsing/invariant.py
import re
from dataclasses import dataclass
from ..registry import PredicateSpec, PREDICATES

@dataclass
class ShAtom:
    spec: PredicateSpec
    payload: dict

def normalize_inv(inv: str) -> str:
    s = re.sub(r"\s+", " ", inv).strip()
    s = re.sub(r"\(\s*", "(", s)
    s = re.sub(r"\s*\)", ")", s)
    s = re.sub(r"\s*,\s*", ",", s)
    return s

_PRED_CALL_RE = re.compile(r'^([A-Za-z_][A-Za-z0-9_]*)\((.*)\)$')

# Memory-state predicates describe raw allocator state (e.g. ``store(&v, T, x)``,
# ``undef_data_at(&v, T)``), not list/tree shape.  They never root at the loop
# pointer, so they are irrelevant to the guard — skip them rather than treating
# them as unknown shape predicates.
_MEMORY_STATE_PREDICATES = {"store", "undef_data_at"}

# Matches pure equalities like "u -> next == w", "t == p", "x != 0"
_PURE_EQ_RE = re.compile(
    r'^([\w][\w\s]*(?:\s*->\s*\w+)?)\s*==\s*([\w][\w\s]*(?:\s*->\s*\w+)?)$'
)

def _split_args(argstr: str) -> list[str]:
    if argstr.strip() == "":
        return []
    return [a.strip() for a in argstr.split(",")]

def _strip_exists(inv: str) -> str:
    """Remove leading 'exists x y z,' prefix from invariant string."""
    m = re.match(r'^exists\s+[\w\s,]+,\s*', inv)
    return inv[m.end():] if m else inv


def parse_invariant(inv: str) -> list[ShAtom]:
    inv = _strip_exists(inv)
    chunks = re.split(r'\s*(?:&&|\*)\s*', inv)
    atoms: list[ShAtom] = []
    for chunk in chunks:
        s = chunk.strip()
        if not s:
            continue
        m = _PRED_CALL_RE.match(s)
        if not m:
            # pure part like "x=3" — ignore
            continue
        name, inner = m.group(1), m.group(2)
        if name in _MEMORY_STATE_PREDICATES:
            # Not a shape predicate; irrelevant to the loop guard.
            continue
        spec = PREDICATES.get(name)
        if spec is None:
            raise ValueError(f"Unknown predicate '{name}' (not registered)")
        args = _split_args(inner)
        if len(args) != spec.arity:
            raise ValueError(f"{name}(...) expects {spec.arity} args, got {args}")
        payload = spec.parse_args(args)
        atoms.append(ShAtom(spec=spec, payload=payload))
    return atoms


_STORE_CALL_RE = re.compile(
    r"store\(\s*&\s*(.+?)\s*,\s*[^,]+?\s*,\s*([A-Za-z_]\w*)\s*\)"
)


def extract_store_bindings(inv: str) -> dict[str, str]:
    """Map each C lvalue stored in the invariant to its abstract scalar var.

    ``store(&i, int, vi)``        -> ``{"i": "vi"}``
    ``store(&sum, long, s)``      -> ``{"sum": "s"}``
    ``store(&(p->data), int, v)`` -> ``{"p->data": "v"}``

    The lvalue is normalised: surrounding parens stripped and ``->`` spacing
    collapsed, matching the keys produced by the condition parser.
    """
    bindings: dict[str, str] = {}
    for m in _STORE_CALL_RE.finditer(inv):
        lvalue = m.group(1).strip()
        while lvalue.startswith("(") and lvalue.endswith(")"):
            lvalue = lvalue[1:-1].strip()
        lvalue = re.sub(r"\s*->\s*", "->", lvalue)
        bindings[lvalue] = m.group(2).strip()
    return bindings


def extract_pure_aliases(inv: str) -> dict[str, str]:
    """Extract pure equalities from invariant and build a normalized alias map.

    For an invariant like "exists w, u -> next == w && sll(w, l1)",
    returns {"u->next": "w", "w": "u->next"} (bidirectional, normalized).

    Only includes equalities between identifiers/field accesses (not numeric
    constants like "t != 0").
    """
    inv_body = _strip_exists(normalize_inv(inv))
    chunks = re.split(r'\s*(?:&&|\*)\s*', inv_body)
    aliases: dict[str, str] = {}
    for chunk in chunks:
        s = chunk.strip()
        m = _PURE_EQ_RE.match(s)
        if not m:
            continue
        lhs, rhs = m.group(1).strip(), m.group(2).strip()
        # Skip numeric constants (e.g., "t == 0")
        if lhs.isdigit() or rhs.isdigit():
            continue
        # Skip if either side is a known keyword like "null", "nullptr"
        if lhs.lower() in ("null", "nullptr") or rhs.lower() in ("null", "nullptr"):
            continue
        # Normalize -> spacing
        nlhs = re.sub(r'\s*->\s*', '->', lhs)
        nrhs = re.sub(r'\s*->\s*', '->', rhs)
        aliases[nlhs] = nrhs
        aliases[nrhs] = nlhs
    return aliases
