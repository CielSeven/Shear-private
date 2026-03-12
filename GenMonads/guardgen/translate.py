# guardgen/translate.py
from .parsing.invariant import normalize_inv, parse_invariant
from .cond.parser import parse_cond_full
from .cond.ast import BoolNode, AtomKind
from .parsing.invariant import ShAtom

def gen_coq_from_bool(ast: BoolNode, atoms: list[ShAtom]) -> str:
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
    # Index roots and segments; collect pointer sets for validation
    roots_by_ptr: dict[str, ShAtom] = {}
    segs: list[ShAtom] = []
    seg_ptrs: set[str] = set()

    for a in atoms:
        if a.spec.kind == "root":
            ptr = a.payload.get("ptr")
            if not isinstance(ptr, str):
                raise ValueError(f"Root predicate '{a.spec.name}' must provide 'ptr' in payload")
            roots_by_ptr[ptr] = a
        elif a.spec.kind == "segment":
            segs.append(a)
            st, ed = a.payload.get("start"), a.payload.get("end")
            if isinstance(st, str): seg_ptrs.add(st)
            if isinstance(ed, str): seg_ptrs.add(ed)

    def _render_root_null(ptr: str, is_eq: bool) -> str:
        root_atom = roots_by_ptr.get(ptr)
        if root_atom is None:
            # Improve diagnostics depending on spatial occurrence
            if ptr in seg_ptrs:
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
        for seg in segs:
            st, ed = seg.payload.get("start"), seg.payload.get("end")
            if st == x and ed == y:
                hit = seg; reversed_match = False; break
            if st == y and ed == x:
                hit = seg; reversed_match = True; break
        if hit is None:
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

def gen_coq_guard(inv: str, cond: str) -> str:
    inv_norm = normalize_inv(inv)
    atoms = parse_invariant(inv_norm)

    # Normalize (void *)0 to 0 before parsing
    # This handles C null pointer literal: (void *)0 == null
    import re
    cond_normalized = re.sub(r'\(\s*void\s*\*\s*\)\s*0', '0', cond)

    ast = parse_cond_full(cond_normalized)
    body = gen_coq_from_bool(ast, atoms)

    # Bind abstract names in INV order
    abs_names: list[str] = []
    for a in atoms:
        abs_names.extend(a.spec.abs_names(a.payload))

    if not abs_names:
        return "fun _ => " + body
    if len(abs_names) == 1:
        return "fun a =>\n  " + body
    pat = ", ".join(abs_names)
    return "fun a =>\n  let '(" + pat + ") := a in\n  " + body
