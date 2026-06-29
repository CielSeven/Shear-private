# guardgen/translate.py
import re
from .parsing.invariant import (
    normalize_inv, parse_invariant, extract_pure_aliases, extract_store_bindings,
)
from .cond.parser import parse_cond_full
from .cond.ast import BoolNode, AtomKind
from .parsing.invariant import ShAtom
from .registry import COMPOSITION_RULES, _match_rule, render_composition_emit


# Names of payload fields that hold a *spatial pointer* for each predicate
# kind.  Single source of truth for "which payload values count as spatial
# pointers" — used by the alias-chase classifier and the ``_render_*``
# helpers downstream.  Adding a new predicate kind only requires extending
# this mapping; no other code touches kind-specific knowledge.
_KIND_POINTER_FIELDS: dict[str, tuple[str, ...]] = {
    "root":    ("ptr",),
    "segment": ("start", "end"),
}


def _pointer_payload_fields(kind: str) -> tuple[str, ...]:
    return _KIND_POINTER_FIELDS.get(kind, ())

def _normalize_ptr(name: str) -> str:
    """Normalize pointer names: strip spaces around '->' for consistent lookup.

    Invariant annotations may have 'u -> next' (with spaces) while
    condition expressions produce 'u->next' (no spaces). This ensures
    they match when used as dictionary keys.
    """
    import re
    return re.sub(r'\s*->\s*', '->', name)


_SCALAR_OP_COQ = {
    "<": "<", "<=": "<=", ">": ">", ">=": ">=", "==": "=", "!=": "<>",
}


def gen_coq_from_bool(ast: BoolNode, atoms: list[ShAtom],
                      aliases: dict[str, str] | None = None,
                      scalar_bindings: dict[str, str] | None = None) -> str:
    """
    Translation with two important behaviors:
      1) Bare 'p' is parsed as 'p == null', and '! p' as 'p != null'.
         We now VALIDATE that 'p' is a spatial pointer:
           - If 'p' is a root pointer: ok → use root-null handler.
           - If 'p' appears only in segments: we currently DO NOT support null checks via segments → error.
           - If 'p' does not appear in any spatial predicate: error (likely a pure/integer var).
      2) Negations of atomic equalities are simplified by flipping handlers
         so '! p' renders as '<> []' instead of '~ ( = [] )'.
    """
    # Index roots and segments; collect pointer sets for validation.
    roots_by_ptr: dict[str, ShAtom] = {}
    segs: list[ShAtom] = []

    for a in atoms:
        if a.spec.kind == "root":
            fields = _pointer_payload_fields("root")
            if not fields:
                continue
            ptr = a.payload.get(fields[0])
            if not isinstance(ptr, str):
                raise ValueError(
                    f"Root predicate '{a.spec.name}' must provide "
                    f"'{fields[0]}' in payload"
                )
            roots_by_ptr[_normalize_ptr(ptr)] = a
        elif a.spec.kind == "segment":
            segs.append(a)

    # Union of all *spatial* pointer values across every atom — used by the
    # alias-chase below.  Kind→pointer-field mapping is centralized in
    # ``_pointer_payload_fields`` so a new predicate kind only needs that one
    # entry, no scattered hardcoding.
    spatial_ptrs: set[str] = set()
    for a in atoms:
        for field in _pointer_payload_fields(a.spec.kind):
            v = a.payload.get(field)
            if isinstance(v, str):
                spatial_ptrs.add(_normalize_ptr(v))

    # ``seg_ptrs`` historically named just the segment endpoints — kept for
    # the diagnostic in ``_render_root_null`` that says "appears only in
    # segment predicates".
    seg_ptrs: set[str] = set()
    for s in segs:
        for field in _pointer_payload_fields("segment"):
            v = s.payload.get(field)
            if isinstance(v, str):
                seg_ptrs.add(_normalize_ptr(v))

    # A field binding ``store(&($base->$field), $val)`` whose value ``$val``
    # is itself a spatial pointer (start of a root, endpoint of a segment,
    # ...) is a POINTER ALIAS, not a scalar.  Reclassify it so a field-deref
    # guard like ``$base->$field != 0`` resolves to the aliased atom's
    # abstract (``l <> []`` instead of an unbound name).  Data-only fields
    # (e.g. ``x->data ↦ x_v`` where ``x_v`` is a ``Z``) stay scalar because
    # ``x_v`` doesn't appear in any spatial predicate.
    aliases = dict(aliases or {})
    scalar_bindings = dict(scalar_bindings or {})
    for k, v in list(scalar_bindings.items()):
        if _normalize_ptr(v) in spatial_ptrs:
            aliases.setdefault(_normalize_ptr(k), v)
            del scalar_bindings[k]

    def _resolve_ptr(ptr: str) -> str:
        """Resolve a pointer name through aliases if not directly in roots/segs."""
        nptr = _normalize_ptr(ptr)
        if nptr in roots_by_ptr or nptr in seg_ptrs:
            return nptr
        if aliases:
            alias = aliases.get(nptr)
            if alias and _normalize_ptr(alias) in roots_by_ptr:
                return _normalize_ptr(alias)
            if alias and _normalize_ptr(alias) in seg_ptrs:
                return _normalize_ptr(alias)
        return nptr

    def _resolve_scalar(operand: str) -> str | None:
        """Resolve a scalar-comparison operand to a Coq term, or None.

        Numeric literals pass through; C lvalues are mapped to their abstract
        scalar variable via *scalar_bindings*.  Returns None when the operand
        is neither (so the caller can fall back to pointer handling)."""
        op = operand.strip()
        if re.fullmatch(r"-?\d+", op):
            return op
        nop = _normalize_ptr(op)
        if scalar_bindings and nop in scalar_bindings:
            return scalar_bindings[nop]
        return None

    def _render_root_null(ptr: str, is_eq: bool) -> str:
        resolved = _resolve_ptr(ptr)
        root_atom = roots_by_ptr.get(resolved)
        if root_atom is None:
            # Scalar fallback: ``i == 0`` / ``i != 0`` where ``i`` is a
            # store-bound scalar, not a list pointer.
            scalar = _resolve_scalar(ptr)
            if scalar is not None:
                return f"{scalar} = 0" if is_eq else f"{scalar} <> 0"
            # Try field-deref: ``<base>-><field>`` may not appear in any
            # spatial predicate directly, but its base might be a root.
            if "->" in resolved:
                base, _, field = resolved.partition("->")
                base = _normalize_ptr(base)
                field = field.strip()
                base = _resolve_ptr(base)
                base_atom = roots_by_ptr.get(base)
                if base_atom is not None and base_atom.spec.to_coq_field_deref_null is not None:
                    return base_atom.spec.to_coq_field_deref_null(
                        base_atom.payload, field, is_eq
                    )
            # Cross-predicate composition rules (JSON-driven).  These
            # combine two or more spatial predicates into a single guard
            # expression — e.g. the "peeled tail" idiom
            # ``lseg(p, q) * listrep(q)`` (segment-then-root concat),
            # which is registered in ``data/guard_predicates.json``
            # under ``_composition_rules.root_null``.  See
            # :class:`CompositionRule` for the schema.
            atoms_by_kind = {"segment": segs, "root": list(roots_by_ptr.values())}
            for rule in COMPOSITION_RULES.get("root_null", []):
                bindings = _match_rule(
                    rule, atoms_by_kind,
                    initial_bindings={"ptr": resolved},
                    normalize_ptr=_normalize_ptr,
                )
                if bindings is not None:
                    return render_composition_emit(rule, bindings, is_eq=is_eq)

            # Improve diagnostics depending on spatial occurrence
            if resolved in seg_ptrs:
                raise ValueError(
                    f"Null-check for '{ptr}' is unsupported: '{ptr}' appears only in segment predicates; "
                    f"add a root predicate (e.g., sll({ptr}, ...)) if you need to relate it to null."
                )
            raise ValueError(
                f"Identifier '{ptr}' does not appear in spatial predicates of the invariant. "
                f"Bare 'p' / '!p' sugar requires a pointer from spatial predicates. "
                f"(We do not handle integer/pure equalities here.)"
            )
        if root_atom.spec.to_coq_root_null is None:
            raise ValueError(f"Predicate '{root_atom.spec.name}' lacks root-null handler")
        return root_atom.spec.to_coq_root_null(root_atom.payload, is_eq=is_eq)

    def _render_seg_eq(x: str, y: str, is_eq: bool) -> str:
        hit = None
        reversed_match = False
        nx, ny = _resolve_ptr(x), _resolve_ptr(y)
        for seg in segs:
            # Pull the two endpoint payload-fields for this segment's
            # kind from the central declaration — ``("start", "end")``
            # for the built-in segment kind, but a future segment-like
            # kind can name its endpoints anything as long as the entry
            # in ``_KIND_POINTER_FIELDS`` lists them in
            # *(first, second)* order.
            fields = _pointer_payload_fields(seg.spec.kind)
            if len(fields) < 2:
                continue
            st = seg.payload.get(fields[0])
            ed = seg.payload.get(fields[1])
            nst = _normalize_ptr(st) if isinstance(st, str) else st
            ned = _normalize_ptr(ed) if isinstance(ed, str) else ed
            if nst == nx and ned == ny:
                hit = seg; reversed_match = False; break
            if nst == ny and ned == nx:
                hit = seg; reversed_match = True; break
        if hit is None:
            # Scalar fallback: ``i == j`` / ``i != j`` between store-bound
            # scalars (or numeric literals), not a list segment.
            sx, sy = _resolve_scalar(x), _resolve_scalar(y)
            if sx is not None and sy is not None:
                return f"{sx} = {sy}" if is_eq else f"{sx} <> {sy}"
            raise ValueError(f"No segment predicate for ({x},{y}) found in invariant")
        if hit.spec.to_coq_segment_eq is None:
            raise ValueError(f"Predicate '{hit.spec.name}' lacks segment-eq handler")
        return hit.spec.to_coq_segment_eq(hit.payload, is_eq=is_eq, reversed_match=reversed_match)

    def go(node: BoolNode) -> str:
        if node.kind == "atom":
            ac = node.atom
            assert ac is not None

            # ptr vs null (includes bare 'p' sugar)
            if ac.kind in (AtomKind.PTR_EQ_NULL, AtomKind.PTR_NE_NULL):
                is_eq = (ac.kind == AtomKind.PTR_EQ_NULL)
                return _render_root_null(ac.ptr1, is_eq)

            # ptr vs ptr → use segments
            elif ac.kind in (AtomKind.PTR_EQ_PTR, AtomKind.PTR_NE_PTR):
                is_eq = (ac.kind == AtomKind.PTR_EQ_PTR)
                return _render_seg_eq(ac.ptr1, ac.ptr2, is_eq)

            # scalar comparison (i < n, i <= n, i == 5, ...)
            elif ac.kind == AtomKind.SCALAR_CMP:
                lhs = _resolve_scalar(ac.ptr1)
                rhs = _resolve_scalar(ac.ptr2)
                if lhs is None:
                    raise ValueError(
                        f"Scalar comparison operand '{ac.ptr1}' is not a "
                        f"store-bound scalar or numeric literal; no `store(&{ac.ptr1}, ...)` "
                        f"binding found in the invariant."
                    )
                if rhs is None:
                    raise ValueError(
                        f"Scalar comparison operand '{ac.ptr2}' is not a "
                        f"store-bound scalar or numeric literal; no `store(&{ac.ptr2}, ...)` "
                        f"binding found in the invariant."
                    )
                coq_op = _SCALAR_OP_COQ[ac.op]
                return f"{lhs} {coq_op} {rhs}"

            else:
                raise ValueError("Unknown atom kind in boolean AST")

        elif node.kind == "not":
            # Simplify negations of atomic comparisons (so '! p' → '<> []')
            c = node.child
            if c and c.kind == "atom" and c.atom is not None:
                ac = c.atom
                if ac.kind in (AtomKind.PTR_EQ_NULL, AtomKind.PTR_NE_NULL):
                    flipped = (ac.kind != AtomKind.PTR_EQ_NULL)  # flip equality
                    return _render_root_null(ac.ptr1, flipped)
                if ac.kind in (AtomKind.PTR_EQ_PTR, AtomKind.PTR_NE_PTR):
                    flipped = (ac.kind != AtomKind.PTR_EQ_PTR)
                    return _render_seg_eq(ac.ptr1, ac.ptr2, flipped)
            # Fallback to syntactic negation
            return f"~ ({go(node.child)})"

        elif node.kind == "and":
            return f"({go(node.left)} /\\ {go(node.right)})"
        elif node.kind == "or":
            return f"({go(node.left)} \\/ {go(node.right)})"
        else:
            raise ValueError(f"Unknown bool node kind: {node.kind}")

    return go(ast)

def gen_coq_guard(inv: str, cond: str, extra_vars: list[str] | None = None) -> str:
    inv_norm = normalize_inv(inv)
    atoms = parse_invariant(inv_norm)
    pure_aliases = extract_pure_aliases(inv)
    scalar_bindings = extract_store_bindings(inv_norm)

    # Normalize (void *)0 to 0 before parsing
    # This handles C null pointer literal: (void *)0 == null
    import re
    cond_normalized = re.sub(r'\(\s*void\s*\*\s*\)\s*0', '0', cond)

    ast = parse_cond_full(cond_normalized)
    body = gen_coq_from_bool(ast, atoms, aliases=pure_aliases,
                             scalar_bindings=scalar_bindings)

    # Bind abstract names in INV order, plus any extra vars (data witnesses)
    abs_names: list[str] = []
    for a in atoms:
        abs_names.extend(a.spec.abs_names(a.payload))
    if extra_vars:
        abs_names.extend(extra_vars)

    if not abs_names:
        return "fun _ => " + body
    if len(abs_names) == 1:
        # Use the variable's name directly as the binder so the body's
        # reference to it (e.g. "l1 <> []") resolves.
        return f"fun {abs_names[0]} =>\n  " + body
    pat = ", ".join(abs_names)
    return "fun a =>\n  let '(" + pat + ") := a in\n  " + body


def guard_structure(inv: str, cond: str, extra_vars: list[str] | None = None) -> dict:
    """Expose the guard as STRUCTURE (so consumers don't re-parse the rendered
    Coq).  Walks the same boolean AST and resolves each atom to its abstract
    `(var, is_zero)`; returns a nested dict:
        {op:'and'|'or', children:[…]} | {op:'not', child:…} |
        {op:'atom', var, is_zero} | {op:'raw', text}
    `is_zero` True ⟺ the atom is `var = []` (empty); False ⟺ `var <> []`."""
    inv_norm = normalize_inv(inv)
    atoms = parse_invariant(inv_norm)
    aliases = extract_pure_aliases(inv)
    scalars = extract_store_bindings(inv_norm)
    ast = parse_cond_full(re.sub(r'\(\s*void\s*\*\s*\)\s*0', '0', cond))

    def walk(node: BoolNode) -> dict:
        if node.kind in ("and", "or"):
            return {"op": node.kind, "children": [walk(node.left), walk(node.right)]}
        if node.kind == "not":
            sub = walk(node.child)
            if sub.get("op") == "atom":               # ¬(var ~ []) -> flip
                return {"op": "atom", "var": sub["var"], "is_zero": not sub["is_zero"]}
            return {"op": "not", "child": sub}
        s = gen_coq_from_bool(node, atoms, aliases=aliases, scalar_bindings=scalars).strip()
        m = re.match(r"\(?\s*(\w+)\s*(<>|=)\s*\[\]\s*\)?$", s)
        if m:
            return {"op": "atom", "var": m.group(1), "is_zero": m.group(2) == "="}
        return {"op": "raw", "text": s}

    return walk(ast)


def serialize_guard_structure(s: dict) -> str:
    """Flat S-expression for the structured guard, e.g. `(or (atom l3 ne) (atom l4 ne))`."""
    op = s["op"]
    if op == "atom":
        return f"(atom {s['var']} {'eq' if s['is_zero'] else 'ne'})"
    if op in ("and", "or"):
        return f"({op} {' '.join(serialize_guard_structure(c) for c in s['children'])})"
    if op == "not":
        return f"(not {serialize_guard_structure(s['child'])})"
    return f"(raw {s.get('text', '')})"
