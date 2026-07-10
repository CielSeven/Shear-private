"""
Translator for shape predicates to data predicates.

This module translates mapped shape predicates by appending augmented data
variables according to the predicate mapping schema.
"""

import re
from typing import Dict, List, Optional, Tuple
from .parser import (
    Formula, Expr, CallExpr, SpatialPred, SepConj, AndConj, Exists, BinOp,
    Var, FieldAccess, Implies, RawFormula, parse_assertion, recover_assertion
)
from .c_types import resolve_field_type
import copy

from GenMonads.predicate_mapping import PredicateMapping, get_predicate_mappings


# Memory-state predicates that describe raw allocator state, not shape.  The
# shape-assertion parser can't tokenize their argument syntax (``&var`` and
# ``struct T*``), so they are extracted verbatim before parsing and spliced
# back into the translated body so they survive into ``_rel.c`` unchanged.
_MEMORY_STATE_PREDICATES = ("undef_data_at", "store", "store_string")


_FIELD_EQ_RE = re.compile(
    r"(?P<expr>\w+)\s*->\s*(?P<field>\w+)\s*==\s*(?P<var>\w+)"
)
_FIELD_EQ_REVERSE_RE = re.compile(
    r"(?P<var>\w+)\s*==\s*(?P<expr>\w+)\s*->\s*(?P<field>\w+)"
)


def _desugar_field_equalities(
    assertion: str,
    type_env: Optional[Dict[str, str]],
    struct_decls: Optional[Dict[str, Dict[str, str]]],
) -> str:
    """Rewrite ``EXPR -> FIELD == VAR`` conjuncts into typed ``store(...)``
    predicates so the unified memory-state pipeline handles them.

    When the field's C type can be resolved via *type_env* + *struct_decls*,
    the conjunct is replaced with ``store(&(EXPR->FIELD), <c_type>, VAR)``.
    If type resolution fails, the original text is left untouched.  Existing
    explicit ``store(&(EXPR->FIELD), ...)`` calls suppress desugaring of the
    same field equality (avoid duplicate splice).
    """
    if not type_env or not struct_decls:
        return assertion

    explicit_targets = set()
    for m in re.finditer(
        r"store\(\s*&\s*\(?\s*(\w+)\s*->\s*(\w+)\s*\)?\s*,",
        assertion,
    ):
        explicit_targets.add((m.group(1), m.group(2)))

    def _replace(match: "re.Match[str]") -> str:
        expr = match.group("expr")
        field = match.group("field")
        var = match.group("var")
        if (expr, field) in explicit_targets:
            return match.group(0)
        c_type = resolve_field_type(expr, field, type_env, struct_decls)
        if not c_type:
            return match.group(0)
        return f"store(&({expr}->{field}), {c_type}, {var})"

    assertion = _FIELD_EQ_RE.sub(_replace, assertion)
    assertion = _FIELD_EQ_REVERSE_RE.sub(_replace, assertion)
    return assertion


_STORE_CALL_RE = re.compile(
    r"store\(\s*([^,]+?)\s*,\s*([^,]+?)\s*,\s*([^)]+?)\s*\)"
)


def parse_store_predicates(text: str) -> List[Tuple[str, str, str]]:
    """Return ``[(addr, c_type, var)]`` for each ``store(...)`` call in
    *text*, in left-to-right order.  No deduplication."""
    return [(m.group(1).strip(), m.group(2).strip(), m.group(3).strip())
            for m in _STORE_CALL_RE.finditer(text)]


def _find_balanced_call(text: str, name: str, start: int = 0) -> Optional[Tuple[int, int]]:
    """Find ``name(...)`` with balanced parentheses at or after *start*.
    Returns ``(call_start, call_end_exclusive)`` or ``None``."""
    pat = re.compile(rf"\b{re.escape(name)}\s*\(")
    m = pat.search(text, start)
    if not m:
        return None
    i = m.end()
    depth = 1
    while i < len(text) and depth > 0:
        ch = text[i]
        if ch == '(':
            depth += 1
        elif ch == ')':
            depth -= 1
        i += 1
    if depth != 0:
        return None
    return m.start(), i


def _extract_memory_state_predicates(assertion: str) -> Tuple[str, List[str]]:
    """Return ``(cleaned_assertion, kept_clauses)`` where ``kept_clauses`` is
    the list of memory-state predicate calls extracted verbatim from
    ``assertion``.  The connecting ``*`` / ``&&`` operator on either side is
    removed from ``cleaned_assertion`` so the result still parses."""
    kept: List[str] = []
    for name in _MEMORY_STATE_PREDICATES:
        pos = 0
        while True:
            found = _find_balanced_call(assertion, name, pos)
            if not found:
                break
            call_start, call_end = found
            kept.append(assertion[call_start:call_end])
            # Trim one neighbouring `*` / `&&` separator so the assertion stays
            # syntactically valid.
            trail = re.match(r"\s*(?:\*|&&)\s*", assertion[call_end:])
            if trail:
                end_cut = call_end + trail.end()
                start_cut = call_start
            else:
                lead = re.search(r"(?:\*|&&)\s*$", assertion[:call_start])
                if lead:
                    start_cut = lead.start()
                    end_cut = call_end
                else:
                    start_cut = call_start
                    end_cut = call_end
            assertion = assertion[:start_cut] + assertion[end_cut:]
            pos = start_cut
    return assertion.strip(), kept


def _splice_kept_clauses(translated: str, kept: List[str]) -> str:
    """Re-insert ``kept`` predicate calls into the translated body at the
    boundary between ``&&``-joined boolean conjuncts and ``*``-joined shape
    predicates — which is where they naturally lived in the source.

    For e.g. ``src == src@pre && sllseg(...) * sll(...)`` plus a kept
    ``undef_data_at(...)``, the result is
    ``src == src@pre && undef_data_at(...) * sllseg(...) * sll(...)``.
    """
    if not kept:
        return translated
    kept_str = " * ".join(kept)

    m = re.match(r"(exists\s+[^,]+,\s*)", translated)
    head, body = (m.group(1), translated[m.end():]) if m else ("", translated)

    # Find the first top-level `*` (outside parens).
    depth = 0
    first_star = -1
    for i, ch in enumerate(body):
        if ch == '(':
            depth += 1
        elif ch == ')':
            depth -= 1
        elif ch == '*' and depth == 0:
            first_star = i
            break

    search_end = first_star if first_star != -1 else len(body)
    # Find the rightmost top-level ``&&`` strictly inside [0, search_end).
    last_amp = -1
    depth = 0
    i = 0
    while i < search_end - 1:
        ch = body[i]
        if ch == '(':
            depth += 1
        elif ch == ')':
            depth -= 1
        elif depth == 0 and ch == '&' and body[i + 1] == '&':
            last_amp = i
            i += 2
            continue
        i += 1

    # ``last_amp`` marks a top-level ``&&`` boundary.  Splice kept after it
    # (joined to the spatial suffix with ``*``) when the suffix is actually
    # spatial — either it has a later top-level ``*`` or it contains a
    # predicate call.  Otherwise (pure suffix) fall through and let the
    # body decide its own treatment.
    def _is_spatial(text: str) -> bool:
        return bool(re.search(r'\b\w+\s*\(', text))
    if last_amp != -1:
        suffix = body[last_amp + 2:]
        if first_star != -1 or _is_spatial(suffix):
            pos = last_amp + 2
            while pos < len(body) and body[pos] == ' ':
                pos += 1
            return head + body[:pos] + kept_str + " * " + body[pos:]
    if not body:
        return head + kept_str
    # No spatial boundary found in body.  Single spatial conjunct →
    # prepend kept with ``*``.  Otherwise it's a chain of pure conjuncts
    # → append kept with ``&&``.
    if _is_spatial(body):
        return head + kept_str + " * " + body
    return head + body + " && " + kept_str


class ShapeTranslator:
    """Translator for shape predicates to data predicates."""

    def __init__(self):
        """Initialize the translator with predicate mappings."""
        self.predicate_mappings: Dict[str, PredicateMapping] = get_predicate_mappings()
        self.var_counter = 0
        self.generated_vars: List[str] = []
        self.generated_var_types: List[str] = []
        self.last_generated_var_types: List[str] = []
        self.var_prefix = ""  # For nested loops like ?l_outer1, ?l_inner1

    def reset_var_counter(self, start_from: int = 0, prefix: str = ""):
        """Reset the variable counter and set prefix."""
        self.var_counter = start_from
        self.generated_vars = []
        self.generated_var_types = []
        self.last_generated_var_types = []
        self.var_prefix = prefix

    def generate_list_var(self, var_type: str = "list Z") -> str:
        """Generate a unique existential variable for an augmented data argument."""
        self.var_counter += 1
        prefix_sep = "_" if self.var_prefix else ""
        var_name = f"?l{self.var_prefix}{prefix_sep}{self.var_counter}"
        self.generated_vars.append(var_name)
        self.generated_var_types.append(var_type)
        return var_name

    def translate_expr(self, expr: Expr) -> Expr:
        if isinstance(expr, BinOp):
            return BinOp(
                expr.op,
                self.translate_expr(expr.left),
                self.translate_expr(expr.right),
            )
        if isinstance(expr, CallExpr):
            return CallExpr(expr.name, [self.translate_expr(arg) for arg in expr.args])
        return copy.deepcopy(expr)

    def translate_spatial_predicate(self, pred: SpatialPred) -> SpatialPred:
        if pred.name in self.predicate_mappings:
            mapping = self.predicate_mappings[pred.name]
            if mapping.shape_arity >= 0 and len(pred.args) != mapping.shape_arity:
                raise ValueError(
                    f"Predicate {pred.name} expected {mapping.shape_arity} shape args, "
                    f"got {len(pred.args)}"
                )
            new_args = [self.translate_expr(arg) for arg in pred.args]
            for var_type in mapping.data_var_types:
                list_var = self.generate_list_var(var_type)
                new_args.append(Var(list_var))
            return SpatialPred(mapping.data_name, new_args)
        else:
            return SpatialPred(pred.name, [self.translate_expr(arg) for arg in pred.args])

    def translate_formula(self, formula: Formula) -> Formula:
        if isinstance(formula, BinOp):
            return BinOp(
                formula.op,
                self.translate_expr(formula.left),
                self.translate_expr(formula.right)
            )
        elif isinstance(formula, SpatialPred):
            return self.translate_spatial_predicate(formula)
        elif isinstance(formula, AndConj):
            return AndConj([self.translate_formula(f) for f in formula.formulas])
        elif isinstance(formula, SepConj):
            return SepConj([self.translate_formula(f) for f in formula.formulas])
        elif isinstance(formula, Implies):
            return Implies(
                self.translate_formula(formula.left),
                self.translate_formula(formula.right),
            )
        elif isinstance(formula, RawFormula):
            return copy.deepcopy(formula)
        elif isinstance(formula, Exists):
            translated_body = self.translate_formula(formula.body)
            return Exists(formula.vars[:], translated_body)
        else:
            raise ValueError(f"Unknown formula type: {type(formula)}")

    def translate_assertion(
        self,
        assertion: str,
        reset: bool = True,
        prefix: str = "",
        type_env: Optional[Dict[str, str]] = None,
        struct_decls: Optional[Dict[str, Dict[str, str]]] = None,
    ) -> Tuple[str, List[str]]:
        """Translate an assertion string."""
        vars_before = len(self.generated_vars)
        types_before = len(self.generated_var_types)
        if reset:
            self.reset_var_counter(prefix=prefix)
            vars_before = 0
            types_before = 0

        assertion = _desugar_field_equalities(assertion, type_env, struct_decls)
        assertion, kept = _extract_memory_state_predicates(assertion)
        if not assertion.strip() and kept:
            # Every conjunct extracted into ``kept`` — there's nothing left
            # for the parser, so join the memory predicates directly with
            # ``*`` (the separating conjunction).
            translated_str = " * ".join(kept)
            new_vars = self.generated_vars[vars_before:]
            self.last_generated_var_types = self.generated_var_types[types_before:]
            return translated_str, new_vars
        ast = parse_assertion(assertion)
        translated_ast = self.translate_formula(ast)
        translated_str = recover_assertion(translated_ast)
        translated_str = _splice_kept_clauses(translated_str, kept)
        new_vars = self.generated_vars[vars_before:]
        self.last_generated_var_types = self.generated_var_types[types_before:]
        return translated_str, new_vars

    def translate_assertion_with_exists(
        self,
        assertion: str,
        prefix: str = "",
        type_env: Optional[Dict[str, str]] = None,
        struct_decls: Optional[Dict[str, Dict[str, str]]] = None,
    ) -> Tuple[str, List[str]]:
        """Translate and wrap with exists."""
        self.reset_var_counter(prefix=prefix)
        assertion = _desugar_field_equalities(assertion, type_env, struct_decls)
        assertion, kept = _extract_memory_state_predicates(assertion)
        if not assertion.strip() and kept:
            translated_str = " * ".join(kept)
            self.last_generated_var_types = self.generated_var_types[:]
            return translated_str, []
        ast = parse_assertion(assertion)
        translated_ast = self.translate_formula(ast)
        generated_vars = self.generated_vars[:]
        var_names_without_question = [v[1:] for v in generated_vars]

        if isinstance(translated_ast, Exists):
            existing_vars = translated_ast.vars
            all_vars = existing_vars + var_names_without_question
            body = translated_ast.body
            new_ast = Exists(all_vars, body)
        else:
            if var_names_without_question:
                new_ast = Exists(var_names_without_question, translated_ast)
            else:
                new_ast = translated_ast

        translated_str = recover_assertion(new_ast)
        self.last_generated_var_types = self.generated_var_types[:]
        for var in generated_vars:
            var_without_question = var[1:]
            translated_str = translated_str.replace(var, var_without_question)

        translated_str = _splice_kept_clauses(translated_str, kept)
        return translated_str, var_names_without_question

def translate(assertion: str, translator: ShapeTranslator = None) -> Tuple[str, List[str]]:
    if translator is None:
        translator = ShapeTranslator()
    return translator.translate_assertion(assertion)

def translate_file(input_file: str, output_file: str, translator: ShapeTranslator = None):
    if translator is None:
        translator = ShapeTranslator()
    with open(input_file, 'r') as f:
        assertions = [line.strip() for line in f if line.strip()]
    results = []
    for assertion in assertions:
        try:
            translated, vars = translator.translate_assertion(assertion)
            results.append(f"Original: {assertion}")
            results.append(f"Translated: {translated}")
            results.append(f"Generated variables: {', '.join(vars)}")
            results.append("")
        except Exception as e:
            results.append(f"Error translating: {assertion}")
            results.append(f"Error: {str(e)}")
            results.append("")
    with open(output_file, 'w') as f:
        f.write('\n'.join(results))
