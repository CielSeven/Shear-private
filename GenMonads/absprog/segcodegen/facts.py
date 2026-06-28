"""Augment a VC's leftover props with facts derived from its separation-logic
antecedent (the ``SEP[...]`` section).

A heap predicate together with a pointer (dis)equality determines a logical-list
fact.  The rules mirror guardgen's predicate registry, e.g. for ``sll``:

    sll(p, l)   with   p == (Ez_val 0)   ==>   l == nil(Z)     (empty list)
    sll(p, l)   with   p != (Ez_val 0)   ==>   l != nil(Z)     (non-empty list)

Derived facts are appended to ``leftover_props`` in the proof block's own
syntax, skipping any already present (modulo whitespace).  They make a
**Continue** arm's list discriminator explicit: an entailment carrying only the
pointer fact ``p != (Ez_val 0)`` gains ``l != nil(Z)`` directly, instead of
having to be inferred as the complement of the paired early return.
"""

from __future__ import annotations

import re
from typing import Callable, Dict, List, Optional, Tuple

from .vcparse import VCBlock

NULL = "(Ez_val 0)"

# A rule: given the predicate's args and a pointer var asserted null/non-null,
# return the derived logical-list fact (in proof-block syntax) or None.
Rule = Callable[[List[str], str, bool], Optional[str]]


def _sll(args: List[str], ptr: str, is_null: bool) -> Optional[str]:
    if len(args) != 2 or args[0] != ptr:
        return None
    l = args[1]
    return f"{l} == nil(Z)" if is_null else f"{l} != nil(Z)"


# Registry of heap predicate -> root-null rule (extend as needed: sllseg, dll…).
RULES: Dict[str, Rule] = {
    "sll": _sll,
}


def _parse_pred(s: str) -> Optional[Tuple[str, List[str]]]:
    m = re.match(r"(\w+)\((.*)\)\s*$", s.strip())
    if not m:
        return None
    return m.group(1), [a.strip() for a in m.group(2).split(",")]


def _norm(s: str) -> str:
    return re.sub(r"\s+", " ", s).strip()


def derive_facts(vc: VCBlock) -> List[str]:
    """List facts (proof-block syntax) implied by SEP + pointer props that are
    not already among ``leftover_props``."""
    preds = [p for p in (_parse_pred(s) for s in vc.sep_state) if p]
    existing = {_norm(p) for p in vc.leftover_props}
    new: List[str] = []
    for prop in vc.leftover_props:
        m = re.match(r"(.+?)\s*(==|!=)\s*\(Ez_val 0\)\s*$", prop)
        if not m:
            continue
        ptr, is_null = m.group(1).strip(), m.group(2) == "=="
        for name, args in preds:
            rule = RULES.get(name)
            if not rule:
                continue
            fact = rule(args, ptr, is_null)
            if fact and _norm(fact) not in existing:
                existing.add(_norm(fact))
                new.append(fact)
    return new


def augment(blocks: List[VCBlock]) -> None:
    """Append derived facts to each block's ``leftover_props`` in place."""
    for vc in blocks:
        vc.leftover_props.extend(derive_facts(vc))
