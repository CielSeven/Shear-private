"""Parse the annotated data-VC C file (`*_data_autovc.c`).

Two things are extracted:

* the function spec (``With`` / ``Inv`` / ``Ensure`` existential orderings),
  which fixes the position of each logical list inside the loop carrier and
  the function result tuple;
* the ``/* !!! ... !!! */`` proof blocks, one per verification condition,
  which tell us how each abstract-program hole transforms its input lists into
  its output lists.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple


# ---- spec ------------------------------------------------------------------

@dataclass
class Spec:
    with_vars: List[str]      # `With l1`          -> ["l1"]
    carrier_vars: List[str]   # `Inv exists l1 l2 l3` -> ["l1","l2","l3"]
    ensure_vars: List[str]    # `Ensure exists l2 l3` -> ["l2","l3"]


def _exists_vars(text: str, keyword: str) -> List[str]:
    """Collect the existential variables after `<keyword>`, across one or more
    consecutive `exists` groups: both `Inv exists v1 v2 v3,` and the split form
    `Ensure exists l2, exists v,` yield every bound variable in order."""
    m = re.search(keyword + r"\b\s*((?:exists\s+[A-Za-z0-9_ ]+?\s*,\s*)+)", text)
    if not m:
        return []
    out: List[str] = []
    for grp in re.findall(r"exists\s+([A-Za-z0-9_ ]+?)\s*,", m.group(1)):
        out.extend(grp.split())
    return out


def parse_spec(text: str) -> Spec:
    with_vars: List[str] = []
    m = re.search(r"\bWith\s+([^\n]+)", text)
    if m:
        with_vars = m.group(1).split()
    return Spec(
        with_vars=with_vars,
        carrier_vars=_exists_vars(text, "Inv"),
        ensure_vars=_exists_vars(text, "Ensure"),
    )


# ---- proof blocks ----------------------------------------------------------

@dataclass
class Mapping:
    """One `lhs -> rhs` line of an exist_mapping, with optional provenance."""
    lhs: str
    rhs: str
    provenance: Optional[str] = None  # callee name if `[x: from call to FN]`


@dataclass
class VCBlock:
    name: str                                   # e.g. glibc..._entail_wit_2
    kind: str                                   # entail | return | funccall | partial_solve | other
    call_target: Optional[str] = None           # for funccall: the callee
    context_exists: List[str] = field(default_factory=list)
    eliminate_local: Dict[str, str] = field(default_factory=dict)
    exist_mapping: List[Mapping] = field(default_factory=list)
    leftover_props: List[str] = field(default_factory=list)
    sep_state: List[str] = field(default_factory=list)               # antecedent SEP predicates
    with_instantiation: Dict[str, str] = field(default_factory=dict)  # funccall
    post_exists: List[str] = field(default_factory=list)              # funccall

    def kind_of(self) -> str:
        return self.kind


_BLOCK_RE = re.compile(r"/\*\s*!!!(.*?)!!!\s*\*/", re.DOTALL)


def _classify(name: str) -> str:
    if "entail_wit" in name:
        return "entail"
    if "return_wit" in name:
        return "return"
    if "funccall_wit" in name:
        return "funccall"
    if "partial_solve" in name:
        return "partial_solve"
    return "other"


def parse_blocks(text: str) -> List[VCBlock]:
    blocks: List[VCBlock] = []
    for m in _BLOCK_RE.finditer(text):
        blocks.append(_parse_one(m.group(1)))
    return blocks


def _parse_one(body: str) -> VCBlock:
    lines = body.splitlines()
    vc = VCBlock(name="", kind="other")
    section: Optional[str] = None
    pending_mapping: Optional[Mapping] = None

    for raw in lines:
        line = raw.strip()
        if not line:
            continue

        m = re.match(r"VC:\s*(\S+)(?:\s+\(call to (\w+)\))?", line)
        if m:
            vc.name = m.group(1)
            vc.kind = _classify(vc.name)
            if m.group(2):
                vc.call_target = m.group(2)
            continue

        # section headers
        if line.startswith("Precondition existentials"):
            section = "context"
            continue
        if line.startswith("Separation-logic state"):
            section = "sep"
            continue
        if line.startswith("EliminateLocal substitutions"):
            section = "elim"
            continue
        if "exist_mapping" in line:
            section = "mapping"
            pending_mapping = None
            continue
        if line.startswith("Leftover left Props"):
            section = "props"
            continue
        if line.startswith("Callee With-variable instantiation"):
            section = "with"
            continue
        if line.startswith("Postcondition existentials"):
            section = "post"
            continue
        if line.startswith("Residual side-condition"):
            section = "mapping"  # residual partial-solve mapping, same shape
            pending_mapping = None
            continue

        # provenance annotation attached to the previous mapping line
        prov = re.match(r"\[(\w+):\s*from call to (\w+)\]", line)
        if prov and pending_mapping is not None:
            pending_mapping.provenance = prov.group(2)
            continue

        if section == "context":
            vc.context_exists.append(line)
        elif section == "elim":
            mm = re.match(r"(.+?)\s*->\s*(.+)", line)
            if mm:
                vc.eliminate_local[mm.group(1).strip()] = mm.group(2).strip()
        elif section == "mapping":
            if line in ("(empty)", "PROP[", "]"):
                continue
            mm = re.match(r"(.+?)\s*->\s*(.+)", line)
            if mm:
                pending_mapping = Mapping(mm.group(1).strip(), mm.group(2).strip())
                vc.exist_mapping.append(pending_mapping)
        elif section == "props":
            if line in ("(empty)", "PROP["):
                continue
            cleaned = line.rstrip(";").rstrip("]").strip().rstrip(";")
            if cleaned and cleaned != "]":
                vc.leftover_props.append(cleaned)
        elif section == "sep":
            if line in ("(empty)", "SEP["):
                continue
            cleaned = line.rstrip(";").rstrip("]").strip().rstrip(";")
            if cleaned and cleaned != "]":
                vc.sep_state.append(cleaned)
        elif section == "with":
            mm = re.match(r"(.+?)\s*->\s*(.+)", line)
            if mm:
                vc.with_instantiation[mm.group(1).strip()] = mm.group(2).strip()
        elif section == "post":
            vc.post_exists.append(line)

    return vc


def find_funccall(blocks: List[VCBlock], callee: str, result_var: str) -> Optional[VCBlock]:
    """The funccall block for `callee` that introduces `result_var`."""
    for b in blocks:
        if b.kind == "funccall" and b.call_target == callee and result_var in b.post_exists:
            return b
    # fall back to callee match alone
    for b in blocks:
        if b.kind == "funccall" and b.call_target == callee:
            return b
    return None
