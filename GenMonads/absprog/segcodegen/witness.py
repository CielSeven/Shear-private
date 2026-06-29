"""Resolve a function's existential variables (loop-`Inv` / `Ensure`) into the
**abstract** state's components.

The abstract loop carrier / result tuple holds only *logical* values: the
data-structure lists and the scalar *data witnesses* (e.g. the `Z` value carried
out of a node — `x_v` in `list_tail`).  A `Inv exists` clause, however, also
binds the program's *pointer* existentials (`x_next`, the `next` field), which
belong to the concrete state, not the abstract one — and must be dropped.

Which is which is read **from the registered operator signatures**, never
hardcoded.  A component is classified by the term its `exist_mapping` assigns:

* mapped to a list constructor (`nil`/`cons`/`app`), or to a variable the
  signatures type as `list T` (a `cons`/`app` *list* operand)  -> **list**;
* mapped to a variable the signatures type as an element `T` (a `cons`/`app`
  *elem* operand, e.g. `x_v -> x_427_free` where `cons(Z, x_427_free, …)`)
  -> **witness** (the scalar);
* mapped to a variable with no inferable logical type (it only appears in
  pointer/`store` positions) -> **drop** (a pointer existential).

The witness needs no special synthesis — it is produced exactly like any `cons`
element (`v <- any Z`).  Only the *shape* of the abstract tuple is fixed here;
the surplus over the template's declared component count is dropped, and the
survivors are ordered to the template's slots (`(list Z * list Z * Z)`).
"""

from __future__ import annotations

import re
from typing import Dict, List, Optional, Set

from . import terms
from .synth import base_name
from .terms import Op, Var
from .vcparse import VCBlock


def _strip_outer_parens(s: str) -> str:
    """Remove fully-enclosing parentheses, repeatedly (`((list Z * Z))` -> `list Z * Z`)."""
    s = s.strip()
    while s.startswith("(") and s.endswith(")"):
        depth = 0
        enclosing = True
        for i, c in enumerate(s):
            if c == "(":
                depth += 1
            elif c == ")":
                depth -= 1
                if depth == 0 and i != len(s) - 1:
                    enclosing = False
                    break
        if enclosing:
            s = s[1:-1].strip()
        else:
            break
    return s


def _split_top(s: str, sep: str) -> List[str]:
    out, depth, cur = [], 0, ""
    for c in s:
        if c == "(":
            depth += 1
            cur += c
        elif c == ")":
            depth -= 1
            cur += c
        elif c == sep and depth == 0:
            out.append(cur)
            cur = ""
        else:
            cur += c
    if cur.strip():
        out.append(cur)
    return out


def tuple_kinds(type_expr: str) -> List[str]:
    """Per-component kind of a tuple type: ``(list Z * list Z * Z)`` ->
    ``['list', 'list', 'witness']``."""
    parts = _split_top(_strip_outer_parens(type_expr), "*")
    return ["list" if p.strip().startswith("list") else "witness" for p in parts]


def _var_types(blocks: List[VCBlock]) -> Dict[str, str]:
    """Infer a coq type for every variable that appears inside an operator term,
    from the registered signatures (a `cons` elem -> `Z`, a `cons` list -> `list Z`)."""
    types: Dict[str, str] = {}

    def absorb(term) -> None:
        for v, ty in terms.collect_var_types(term):
            types.setdefault(v, ty)

    for b in blocks:
        for mp in b.exist_mapping:
            absorb(terms.parse_term(mp.rhs))
        for prop in b.leftover_props:
            m = re.match(r"(.+?)\s*[=!]=\s*(.+)", prop)
            if m:
                absorb(terms.parse_term(m.group(2)))
    return types


def _classify(base: str, blocks: List[VCBlock], types: Dict[str, str],
              scalar_bases: Optional[Set[str]] = None) -> str:
    """``'list'`` | ``'witness'`` | ``'unknown'`` for a carrier/ensure component,
    from how every `exist_mapping` that targets it assigns it.

    A component named in `scalar_bases` (stored at a non-pointer C type) is a
    scalar ``Z`` witness outright — this catches a *flag/accumulator* carried as
    a bare literal (`ty -> 1`/`-> 0`), which leaves no operator/type evidence in
    its `exist_mapping` for the inference below to latch onto."""
    if scalar_bases and base in scalar_bases:
        return "witness"
    saw_list = saw_witness = False
    for b in blocks:
        for mp in b.exist_mapping:
            if base_name(mp.lhs) != base:
                continue
            term = terms.parse_term(mp.rhs)
            if isinstance(term, Op):              # classify by the op's result kind
                sig = terms.SIGNATURES.get(term.op)
                if sig is not None and sig.result == "scalar":
                    saw_witness = True            # e.g. `s -> (s + x)` (an `add`)
                else:
                    saw_list = True               # nil/cons/app yield a list
            elif isinstance(term, Var):
                t = types.get(term.name)
                if t and t.strip().startswith("list"):
                    saw_list = True
                elif t:                            # typed, non-list -> element (Z) witness
                    saw_witness = True
    if saw_list:
        return "list"
    if saw_witness:
        return "witness"
    return "unknown"


def _assign_to_slots(vars: List[str], kind: Dict[str, str], kinds: List[str]) -> List[str]:
    """Order the kept vars to the template's slots: witnesses fill ``witness``
    slots, everything else (list / unknown) fills ``list`` slots — each group in
    declared order, so an all-list tuple keeps its original order untouched."""
    witnesses = [v for v in vars if kind[v] == "witness"]
    others = [v for v in vars if kind[v] != "witness"]   # list + unknown, in order
    out: List[str] = []
    for k in kinds:
        primary = witnesses if k == "witness" else others
        fallback = others if k == "witness" else witnesses
        if primary:
            out.append(primary.pop(0))
        elif fallback:
            out.append(fallback.pop(0))
    return out


def refine(vars: List[str], blocks: List[VCBlock], type_expr: str,
           scalar_bases: Optional[Set[str]] = None) -> List[str]:
    """The logical components of `vars` (a `Inv`/`Ensure` existential list),
    ordered to the abstract `type_expr`'s slots, with surplus pointer
    existentials dropped.  For an all-list tuple with no surplus this is the
    identity (so list-only functions are unaffected)."""
    kinds = tuple_kinds(type_expr)
    types = _var_types(blocks)
    kind = {v: _classify(v, blocks, types, scalar_bases) for v in vars}
    if len(vars) > len(kinds):
        # drop the surplus pointer existentials (those with no logical evidence)
        surplus = len(vars) - len(kinds)
        droppable = [v for v in vars if kind[v] == "unknown"]
        drop = set(droppable[:surplus])
        vars = [v for v in vars if v not in drop]
    return _assign_to_slots(vars, kind, kinds)
