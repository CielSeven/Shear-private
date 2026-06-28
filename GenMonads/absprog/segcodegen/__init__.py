"""segcodegen — fill the LLM-parameter holes of a `*_rel_lib.v` template by
reading the matching annotated data-VC file (`*_data_autovc.c`).

Convention (loop-carrier MretTy):

* ``MretTy`` is the loop-carrier tuple type.
* ``M_loop_before`` maps the precondition list to the initial carrier
  (from ``entail_wit`` at loop entry).
* ``M_loop_M2`` is the loop-body step (from the inductive ``entail_wit``).
* ``M_loop_M1`` is the break branch, currently the identity ``fun r => return r``.
* ``M_loop_end`` projects the carrier to the result tuple (from ``return_wit``).

Public entry point: :func:`fill_template`.
"""

from __future__ import annotations

from pathlib import Path
import re
from typing import Dict, List, Optional, Tuple

from . import facts, regions, witness
from .synth import base_name, referenced_funccalls, synth_branched
from .template import Hole, Template, parse_template
from .vcparse import Mapping, Spec, VCBlock, parse_blocks, parse_spec

__all__ = ["fill_template", "fill_from_paths"]


def _natural_key(s: str):
    return [int(t) if t.isdigit() else t for t in re.split(r"(\d+)", s)]


def _entail_groups(blocks: List[VCBlock]) -> Dict[int, List[VCBlock]]:
    """Group entailment VCs by their leading wit number.  Branches of one
    program point share it: `entail_wit_2_1` and `entail_wit_2_2` -> group 2."""
    groups: Dict[int, List[VCBlock]] = {}
    for b in blocks:
        if b.kind != "entail":
            continue
        m = re.search(r"entail_wit_(\d+)", b.name)
        if m:
            groups.setdefault(int(m.group(1)), []).append(b)
    for g in groups.values():
        g.sort(key=lambda b: _natural_key(b.name))
    return groups


def _classify_entails(blocks: List[VCBlock], spec: Spec):
    """Return (before_vc, step_vcs): the loop-entry entailment and the (possibly
    branched) loop-step entailments.  By the proof convention the lowest wit
    number is the loop entry; the next is the loop body."""
    groups = _entail_groups(blocks)
    nums = sorted(groups)
    before = groups[nums[0]][0] if nums else None
    step_vcs = groups[nums[1]] if len(nums) > 1 else []
    return before, step_vcs


def _definition(hole: Hole, body: str) -> str:
    lines = body.split("\n")
    lines[0] = "  " + lines[0]
    indented = "\n".join(lines)
    return f"Definition {hole.name} : {hole.type_str} :=\n{indented}"


_HOLE_SUFFIXES = ("_M_loop_before", "_M_loop_M1", "_M_loop_M2", "_M_loop_end", "_M")


def _hole_func(name: str) -> str:
    """The function a hole belongs to, e.g. `rev_append_local_M_loop_M2` ->
    `rev_append_local`.  In a multi-function file this scopes a hole to its own
    VCs (whose names share the prefix), so one function's returns never leak into
    another's loop body."""
    for suf in _HOLE_SUFFIXES:
        if name.endswith(suf):
            return name[: -len(suf)]
    return name


def _segment_arms(hole: Hole, blocks: List[VCBlock], spec: Spec, guard) -> Tuple[List[str], list]:
    """The (input group, arms) for a VC-driven hole.  This is the *only*
    role-specific logic — picking which VCs are relevant.  An arm is
    ``(vc, funccalls, output_group, wrap)``: *entail* arms re-establish state
    (→ carrier, ``Continue`` when the hole is `early_result`); *return* arms are
    early/normal returns (→ result, ``ReturnNow`` when `early_result`).  The two
    sets and the input group are all the role decides; whatever comes back is
    synthesized identically by :func:`synth_branched` — single arm or many,
    curried or tupled, wrapped or not.

    Relevant VCs are scoped to the hole's own function (multi-function files
    interleave several functions' VCs in one autovc).  The region helpers then
    yield *no* return arms when that function has no early return
    (`before_return_vcs`/`inloop_early_return_vcs` are empty), so a plain loop
    needs no special-casing — `early_result` only adds the wrap."""
    func = _hole_func(hole.name)
    fblocks = [b for b in blocks if b.name.startswith(func + "_")]
    before_vc, step_vcs = _classify_entails(fblocks, spec)
    end_vc = regions.select_end_return(fblocks, guard)   # loop-exit return (multi-return safe)

    early = "early_result" in hole.type_str
    cont_wrap = "Continue" if early else None
    ret_wrap = "ReturnNow" if early else None

    if hole.role == "before":
        input_group = spec.with_vars
        entail_vcs, return_vcs = [before_vc], regions.before_return_vcs(fblocks)
    elif hole.role == "M2":
        input_group = spec.carrier_vars
        entail_vcs, return_vcs = list(step_vcs), regions.inloop_early_return_vcs(fblocks, guard)
    elif hole.role == "end":
        input_group = spec.carrier_vars
        entail_vcs, return_vcs = [], [end_vc]
    else:   # "M" — no-loop whole function: every return is a result path
        input_group = spec.with_vars
        entail_vcs, return_vcs = [], [b for b in fblocks if b.kind == "return"]

    if any(v is None for v in entail_vcs + return_vcs) or not (entail_vcs or return_vcs):
        raise ValueError(f"no source VC found for hole {hole.name}")

    arms = [(vc, referenced_funccalls(vc, fblocks), spec.carrier_vars, cont_wrap)
            for vc in entail_vcs]
    arms += [(vc, referenced_funccalls(vc, fblocks), spec.ensure_vars, ret_wrap)
             for vc in return_vcs]
    return input_group, arms


def _result_type(holes: List[Hole]) -> Optional[str]:
    """The `MONAD <R>` result type of the hole that produces the function result
    (`end` / `M` / `normal`), used to shape the `Ensure` tuple."""
    for role in ("end", "M", "normal"):
        for h in holes:
            if h.role == role:
                m = re.search(r"MONAD\s*(.+?)\s*$", h.type_str)
                if m:
                    return m.group(1)
    return None


def _strip_ezval(v: str) -> str:
    """In a scalar (witness) context the val-coercion `(Ez_val e)` is just `e`
    (`(Ez_val 0)` -> `0`)."""
    m = re.match(r"\(\s*Ez_val\s+(.+?)\s*\)\s*$", v.strip())
    return m.group(1) if m else v


def _merge_witness_substitutions(blocks: List[VCBlock], logical_bases: set) -> None:
    """A scalar data witness's value lives in a VC's `EliminateLocal` section
    (`s_406 -> (s_410 + x_413_free)`), not its `exist_mapping`.  Lift each such
    substitution whose base name is a logical carrier/ensure component into the
    `exist_mapping` the synthesizer reads, so witnesses are produced uniformly
    (no synthesis change).  List components stay where they are."""
    for b in blocks:
        present = {base_name(m.lhs) for m in b.exist_mapping}
        for lhs, val in b.eliminate_local.items():
            base = base_name(lhs)
            if base in logical_bases and base not in present:
                b.exist_mapping.append(Mapping(lhs, _strip_ezval(val)))
                present.add(base)


def fill_template(template_text: str, autovc_text: str) -> str:
    tmpl = parse_template(template_text)
    spec = parse_spec(autovc_text)
    blocks = parse_blocks(autovc_text)
    # surface scalar data-witness substitutions (EliminateLocal) as mappings
    _merge_witness_substitutions(blocks, set(spec.carrier_vars + spec.ensure_vars))
    facts.augment(blocks)   # derive list facts from SEP + pointer props (e.g. l != nil)

    # Resolve the abstract carrier / result to their *logical* components: drop
    # pointer existentials, keep lists + data witnesses, ordered to the template
    # (registry-driven — see witness.py).  List-only functions are unchanged.
    carrier_vars = spec.carrier_vars
    if tmpl.carrier_type:
        carrier_vars = witness.refine(spec.carrier_vars, blocks, tmpl.carrier_type)
    ensure_vars = spec.ensure_vars
    res_ty = _result_type(tmpl.holes)
    if res_ty:
        ensure_vars = witness.refine(spec.ensure_vars, blocks, res_ty)
    spec = Spec(with_vars=spec.with_vars, carrier_vars=carrier_vars, ensure_vars=ensure_vars)

    guard = regions.parse_guard(tmpl.text)

    out = tmpl.text
    for hole in tmpl.holes:
        if hole.role == "mretty":                       # type definition, not a segment
            replacement = f"Definition MretTy : Type := {tmpl.carrier_type}."
        elif hole.role == "M1":                          # fixed break branch (no VC drives it)
            replacement = _definition(hole, "fun r => return r.")
        elif hole.role in ("before", "M2", "end", "M"):  # VC-driven: one uniform path
            input_group, arms = _segment_arms(hole, blocks, spec, guard)
            body = synth_branched(arms, input_group, curried=hole.curried)
            replacement = _definition(hole, body)
        else:
            continue
        out = out.replace(hole.raw, replacement, 1)
    return out


def fill_from_paths(template_path: str, autovc_path: str,
                    out_path: Optional[str] = None) -> str:
    template_text = Path(template_path).read_text()
    autovc_text = Path(autovc_path).read_text()
    result = fill_template(template_text, autovc_text)
    if out_path is not None:
        Path(out_path).write_text(result)
    return result
