"""Associate entail/return VCs with program regions and pick the loop-exit VC.

A VC's path starts at the annotation preceding its program point.  Precondition
``With`` existentials are emitted as ``*_free``; loop-carrier instances are not —
so the *context* tells us the region:

* **before** — context is the ``*_free`` precondition vars (path from the
  precondition, e.g. the loop-entry entailment or an early return before the
  loop);
* **loop** — context is the loop-carrier instances (path from the invariant).

For loop-region ``return`` VCs the loop guard (parsed from the template's
``guard-struct``) splits the **normal loop exit** (guard false → ``M_loop_end``)
from **in-loop early returns** (guard true → an early ``ReturnNow``).
"""

from __future__ import annotations

import re
from typing import List, Optional, Tuple

from .synth import base_name
from .vcparse import VCBlock

Atom = Tuple[str, str]    # (carrier variable, relation e.g. "ne")
Guard = List[Atom]        # disjunction of atoms: the loop runs while ANY holds


def region(vc: VCBlock) -> str:
    ctx = vc.context_exists
    if ctx and all(c.endswith("_free") for c in ctx):
        return "before"
    return "loop"


def parse_guard(template_text: str) -> Optional[Guard]:
    """Read the loop guard from a ``(*@ guard-struct: ... @*)`` comment as a
    *disjunction* of atoms.  ``(atom l3 ne)`` -> ``[("l3","ne")]``;
    ``(or (atom l3 ne) (atom l4 ne))`` -> ``[("l3","ne"), ("l4","ne")]``.  The
    loop continues while ANY atom holds, so it exits only when ALL are false."""
    m = re.search(r"guard-struct:\s*(.+)", template_text)
    if not m:
        return None
    atoms = re.findall(r"\(atom\s+(\w+)\s+(\w+)\)", m.group(1))
    return [(v, r) for v, r in atoms] if atoms else None


def _atom_is_false(vc: VCBlock, atom: Atom) -> bool:
    """True if a leftover prop pins this atom's guard variable to its empty form
    (for ``ne``, ``<guard_var>ᵢ == nil``)."""
    var, rel = atom
    for p in vc.leftover_props:
        m = re.match(r"(\w+)\s*==\s*(.+)", p)
        if not m or base_name(m.group(1)) != var:
            continue
        if rel == "ne" and m.group(2).strip().startswith("nil("):
            return True
    return False


def guard_is_false(vc: VCBlock, guard: Optional[Guard]) -> bool:
    """True if the loop guard is false in this VC — the normal loop exit.  For a
    disjunctive guard every atom must be pinned empty (``l3==nil`` *and*
    ``l4==nil``); a single-atom guard reduces to the obvious case."""
    if not guard:
        return False
    return all(_atom_is_false(vc, a) for a in guard)


def loop_return_vcs(blocks: List[VCBlock]) -> List[VCBlock]:
    return [b for b in blocks if b.kind == "return" and region(b) == "loop"]


def before_return_vcs(blocks: List[VCBlock]) -> List[VCBlock]:
    """Before-region `return` VCs — early returns reached before the loop (e.g.
    ``if (x == 0) return y;``).  They feed ``M_loop_before``'s ReturnNow arm."""
    return [b for b in blocks if b.kind == "return" and region(b) == "before"]


def inloop_early_return_vcs(blocks: List[VCBlock], guard: Optional[Guard]) -> List[VCBlock]:
    """Loop-region `return` VCs that are genuine in-loop early returns (guard
    *true*).  They feed ``M_loop_M2``'s ReturnNow arm.  The selected normal exit
    and every guard-*false* return (multi-path exits reach the same program
    point) are excluded — so a plain loop, whose only loop-region return is its
    exit, yields none, and a multi-path exit does not leak a bogus early-return
    into M2 (regardless of whether that exit pins the guard variable empty)."""
    end = select_end_return(blocks, guard)
    return [b for b in loop_return_vcs(blocks)
            if b is not end and not guard_is_false(b, guard)]


def select_end_return(blocks: List[VCBlock], guard: Optional[Guard]) -> Optional[VCBlock]:
    """The post-loop return VC for ``M_loop_end``: the loop-region return whose
    guard is false (the loop exit).  With a single loop-region return there is no
    ambiguity; with none, fall back to any return (degenerate / no-loop)."""
    loop_returns = loop_return_vcs(blocks)
    if not loop_returns:
        rets = [b for b in blocks if b.kind == "return"]
        return rets[0] if rets else None
    if len(loop_returns) == 1:
        return loop_returns[0]
    exits = [b for b in loop_returns if guard_is_false(b, guard)]
    return exits[0] if exits else loop_returns[0]
