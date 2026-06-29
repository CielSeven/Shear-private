"""Parse the `*_rel_lib.v` template: locate the `Parameter` holes that this
module must fill, and recover the function name and loop-carrier type.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from typing import List, Optional


@dataclass
class Hole:
    name: str          # full Coq identifier, e.g. glibc..._M_loop_M2
    type_str: str      # the declared type, e.g. "(list Z * list Z * list Z) -> MONAD ..."
    role: str          # before | M1 | M2 | end | M | mretty
    raw: str           # the full `Parameter ... .` text being replaced
    input_arity: int = 1   # number of curried arguments before `MONAD`

    @property
    def curried(self) -> bool:
        return self.input_arity > 1


@dataclass
class Template:
    text: str
    func: str                 # e.g. glibc_slist_clean_copy
    carrier_type: str         # e.g. "(list Z * list Z * list Z)" or "(list Z * Z)"
    holes: List[Hole]


_PARAM_RE = re.compile(r"^[ \t]*Parameter\s+([A-Za-z0-9_']+)\s*:\s*(.+?)\.[ \t]*$",
                       re.MULTILINE | re.DOTALL)


_FOREST_RE = re.compile(r"_M_loop(\d+)_(.+)$")


def _role(name: str) -> Optional[str]:
    if name == "MretTy":
        return "mretty"
    # Loop forest (`_M_loop{k}_*`): several loops, an outer body calling an inner
    # one.  `to_inner`/`after_inner` are the nesting glue (the inner loop behaves
    # like a callee); the rest mirror the single-loop roles, per loop.
    fm = _FOREST_RE.search(name)
    if fm:
        suf = fm.group(2)
        if suf.startswith("to_inner"):
            return "to_inner"
        if suf.startswith("after_inner"):
            return "after_inner"
        if suf == "MretTy":            # per-loop result type, e.g. `_M_loop2_MretTy`
            return "loop_mretty"
        return {"M1": "fM1", "M2": "fM2", "before": "fbefore", "end": "fend"}.get(suf)
    for suffix, role in (
        ("_M_loop_before", "before"),
        ("_M_loop_M1", "M1"),
        ("_M_loop_M2", "M2"),
        ("_M_loop_end", "end"),
        # no-loop function with an early-return decision point: M_before splits
        # into Continue(state)/ReturnNow(early result); M_normal is the post-
        # decision straight-line tail (analogues of M_loop_before / M_loop_end).
        ("_M_before", "before_noloop"),
        ("_M_normal", "normal"),
    ):
        if name.endswith(suffix):
            return role
    if name.endswith("_M"):       # whole-function hole (no-loop, no early return)
        return "M"
    return None


def _input_arity(type_str: str) -> int:
    """Number of curried arguments before `MONAD` (a single tuple counts as 1)."""
    head = type_str.split("MONAD", 1)[0]
    return max(1, head.count("->"))


def _arg_type(type_str: str) -> Optional[str]:
    """The argument type of a `CARRIER -> MONAD _` hole: everything left of the
    top-level (paren-depth 0) `->`, verbatim.  We make no assumption about the
    carrier's shape — `(list Z * list Z)`, `(list Z * list Z * Z)` (a scalar data
    witness), or anything else — it is simply whatever type the template declares."""
    depth = 0
    for i in range(len(type_str) - 1):
        c = type_str[i]
        if c == "(":
            depth += 1
        elif c == ")":
            depth -= 1
        elif depth == 0 and c == "-" and type_str[i + 1] == ">":
            return type_str[:i].strip()
    return None


def parse_template(text: str) -> Template:
    holes: List[Hole] = []
    func: Optional[str] = None
    carrier_type: Optional[str] = None

    m1_type: Optional[str] = None
    has_loop = False
    for m in _PARAM_RE.finditer(text):
        name, type_str = m.group(1), m.group(2).strip()
        role = _role(name)
        if role is None:
            continue
        holes.append(Hole(name=name, type_str=type_str, role=role, raw=m.group(0),
                          input_arity=_input_arity(type_str)))
        if role in ("fM1", "fM2", "fbefore", "fend", "to_inner", "after_inner",
                    "loop_mretty"):
            func = _FOREST_RE.sub("", name)        # strip `_M_loop{k}_...`
            has_loop = True
            # the loop carrier is the argument of a forest step/break hole
            if role in ("fM1", "fM2", "to_inner") and carrier_type is None:
                carrier_type = _arg_type(type_str)
        elif role in ("before", "M1", "M2", "end"):
            func = name.rsplit("_M_loop_", 1)[0]
            has_loop = True
        elif role == "before_noloop":
            func = name[: -len("_M_before")]
        elif role == "normal":
            func = name[: -len("_M_normal")]
        elif role == "M":
            func = name[: -len("_M")]
        # The carrier is the argument type of `M_loop_M2` (or `M_loop_M1`); both
        # take `CARRIER -> MONAD _`.  No concrete-type parsing — just the arg.
        if role == "M2":
            carrier_type = _arg_type(type_str)
        elif role == "M1":
            m1_type = type_str

    if func is None:
        raise ValueError("could not find an _M / _M_loop_* parameter in template")

    if has_loop and carrier_type is None and m1_type is not None:
        carrier_type = _arg_type(m1_type)
    if has_loop and carrier_type is None:
        raise ValueError("could not determine loop-carrier type from template")

    return Template(text=text, func=func, carrier_type=carrier_type or "", holes=holes)
