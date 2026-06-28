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

Guard = Tuple[str, str]   # (carrier variable, relation e.g. "ne")


def region(vc: VCBlock) -> str:
    ctx = vc.context_exists
    if ctx and all(c.endswith("_free") for c in ctx):
        return "before"
    return "loop"


def parse_guard(template_text: str) -> Optional[Guard]:
    """Read the guard variable/relation from a ``(*@ guard-struct: (atom l3 ne) @*)``
    comment, e.g. ``("l3", "ne")``."""
    m = re.search(r"guard-struct:\s*\(atom\s+(\w+)\s+(\w+)\)", template_text)
    return (m.group(1), m.group(2)) if m else None


def guard_is_false(vc: VCBlock, guard: Optional[Guard]) -> bool:
    """True if a leftover prop pins the guard variable's instance to its empty
    form (for ``ne`` guards, ``<guard_var>ᵢ == nil``) — i.e. the loop exit."""
    if not guard:
        return False
    var, rel = guard
    for p in vc.leftover_props:
        m = re.match(r"(\w+)\s*==\s*(.+)", p)
        if not m or base_name(m.group(1)) != var:
            continue
        if rel == "ne" and m.group(2).strip().startswith("nil("):
            return True
    return False


def loop_return_vcs(blocks: List[VCBlock]) -> List[VCBlock]:
    return [b for b in blocks if b.kind == "return" and region(b) == "loop"]


def before_return_vcs(blocks: List[VCBlock]) -> List[VCBlock]:
    """Before-region `return` VCs — early returns reached before the loop (e.g.
    ``if (x == 0) return y;``).  They feed ``M_loop_before``'s ReturnNow arm."""
    return [b for b in blocks if b.kind == "return" and region(b) == "before"]


def inloop_early_return_vcs(blocks: List[VCBlock], guard: Optional[Guard]) -> List[VCBlock]:
    """Loop-region `return` VCs other than the normal loop exit — in-loop early
    returns (guard true).  They feed ``M_loop_M2``'s ReturnNow arm."""
    end = select_end_return(blocks, guard)
    return [b for b in loop_return_vcs(blocks) if b is not end]


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
