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
from .synth import base_name, referenced_funccalls, synth_branched, synth_recursive
from .template import Hole, Template, parse_template, _arg_type
from .vcparse import (Mapping, Spec, VCBlock, parse_all_invs, parse_blocks,
                      parse_spec, scalar_witness_bases)

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


def _result_after_arrow(type_str: str) -> str:
    """The result type of ``ARG -> RESULT`` (everything right of the top-level
    ``->``)."""
    arg = _arg_type(type_str)
    return type_str[len(arg):].lstrip()[2:].strip() if arg else type_str


def _recursive_definition(hole: Hole, arg_name: str, body: str) -> str:
    """Emit a `Fixpoint` for a self-recursive whole-function hole: the argument
    is named (so the `match` body can recurse on its subterms) and the result
    type follows the colon — ``Fixpoint f (l1 : list Z) : MONAD (list Z) := …``."""
    arg_type = _arg_type(hole.type_str)
    result = _result_after_arrow(hole.type_str)
    indented = "\n".join("  " + l for l in body.split("\n"))
    return f"Fixpoint {hole.name} ({arg_name} : {arg_type}) : {result} :=\n{indented}."


_HOLE_SUFFIXES = ("_M_loop_before", "_M_loop_M1", "_M_loop_M2", "_M_loop_end",
                  "_M_before", "_M_normal", "_M")


_FOREST_SUFFIX_RE = re.compile(r"_M_loop\d+_.+$")


def _hole_func(name: str) -> str:
    """The function a hole belongs to, e.g. `rev_append_local_M_loop_M2` ->
    `rev_append_local`.  In a multi-function file this scopes a hole to its own
    VCs (whose names share the prefix), so one function's returns never leak into
    another's loop body."""
    forest = _FOREST_SUFFIX_RE.sub("", name)       # `..._M_loop2_M1` -> `...`
    if forest != name:
        return forest
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

    if hole.role in ("before", "fbefore"):
        # `fbefore` is the outermost loop's entry in a loop forest — same shape as
        # a single loop's `before` (initial carrier from the loop-entry entail).
        input_group = spec.with_vars
        entail_vcs, return_vcs = [before_vc], regions.before_return_vcs(fblocks)
    elif hole.role == "M2":
        input_group = spec.carrier_vars
        entail_vcs, return_vcs = list(step_vcs), regions.inloop_early_return_vcs(fblocks, guard)
    elif hole.role == "end":
        input_group = spec.carrier_vars
        entail_vcs, return_vcs = [], [end_vc]
    elif hole.role == "before_noloop":
        # no-loop early-return prelude: the Continue arm threads the inputs
        # through unchanged (a synthetic identity entail, guarded by the negated
        # early-return discriminator); the ReturnNow arms are the early returns.
        input_group = spec.with_vars
        before_rets = regions.before_return_vcs(fblocks)
        entail_vcs = [_noloop_continue_vc(spec.carrier_vars, before_rets)]
        return_vcs = before_rets
    elif hole.role == "normal":
        # the straight-line tail after the decision point: input is the carrier
        # (= the threaded inputs), output is the function result.
        input_group = spec.carrier_vars
        entail_vcs = []
        return_vcs = [b for b in fblocks
                      if b.kind == "return" and regions.region(b) != "before"]
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


def _noloop_continue_vc(carrier_vars: List[str], before_returns: List[VCBlock]) -> VCBlock:
    """A synthetic entail VC for a no-loop ``M_before``'s Continue arm: it maps
    the carrier to itself (the inputs pass through untouched) and guards on the
    negation of each early return's list discriminator (``l1 == nil`` becomes the
    pure guard ``l1 != nil``), so Continue and the ReturnNow arms are mutually
    exclusive.  No real VC describes the fall-through, so we build it here rather
    than special-casing the synthesizer."""
    from .synth import base_name
    vc = VCBlock(name="__noloop_continue", kind="entail")
    vc.exist_mapping = [Mapping(v, v) for v in carrier_vars]      # identity
    for b in before_returns:
        for p in b.leftover_props:
            m = re.match(r"(.+?)\s*==\s*(nil\(.*\))\s*$", p.strip())
            if m and base_name(m.group(1)) in carrier_vars:
                neg = f"{base_name(m.group(1))} != {m.group(2)}"
                if neg not in vc.leftover_props:
                    vc.leftover_props.append(neg)
    return vc


def _carrier_type_from_vars(vars: List[str], scalar_bases: set) -> str:
    """The abstract-state tuple type for a no-loop early-return function, whose
    carrier is just the threaded inputs: a scalar (stored at an int type) is
    ``Z``, everything else a ``list Z``."""
    parts = ["Z" if v in scalar_bases else "list Z" for v in vars]
    return "(" + " * ".join(parts) + ")"


_LOOP_RE = re.compile(r"_M_loop(\d+)_")
_CHILD_RE = re.compile(r"_(?:to_inner|after_inner)_(\d+)$")


def _loop_index(name: str) -> Optional[int]:
    m = _LOOP_RE.search(name)
    return int(m.group(1)) if m else None


def _child_index(name: str) -> Optional[int]:
    m = _CHILD_RE.search(name)
    return int(m.group(1)) if m else None


def fill_forest(tmpl: Template, blocks: List[VCBlock], spec: Spec,
                invs: List[List[str]], scalar_bases: set,
                collect: Optional[list] = None) -> Dict[str, str]:
    """Fill a loop-forest template's holes from the (now complete) per-loop VCs.

    The synthesizer is untouched: every hole still becomes ``synth_branched(arms,
    input_group)``.  The forest only adds a *richer routing* — each `entail`/
    `return` VC is classified by the **(from-loop -> to-loop)** transition it
    proves, and the holes are wired to the matching VCs:

    * ``loop{k}_before``  <- precond -> loop k         (entry; outermost loop)
    * ``loop{p}_to_inner_{c}``     <- loop p -> loop c  (enter the nested loop)
    * ``loop{k}_M2``      <- loop k -> loop k           (a body iteration)
    * ``loop{p}_after_inner_{c}``  <- loop c -> loop p  (resume the outer body)
    * ``loop{k}_end``     <- loop k -> result           (the loop's exit return)
    * ``loop{k}_M1``      = ``fun r => return r``        (break — fixed)
    * ``loop{k}_MretTy``  := loop k's carrier type        (per-loop result type)

    A loop is identified by its *distinguishing list variables* (its `Inv`'s list
    components, which differ per loop); the shared scalar witness does not
    disambiguate.  ``after_inner`` consumes the child loop's MretTy as its single
    argument (matching gen_rel_lib's Parameter and both call sites) — synthesized
    directly from the resume entailment's inner-carrier roots, no extra binder."""
    holes = tmpl.holes
    loop_ct: Dict[int, str] = {}
    for h in holes:                                  # carrier type from each loop's M1 arg
        if h.role == "fM1":
            loop_ct[_loop_index(h.name)] = _arg_type(h.type_str)
    loops = sorted(k for k in loop_ct if k is not None)

    # loop k <-> invs[k-1] (source order: outermost loop is loop 1, first `Inv`)
    loop_vars: Dict[int, List[str]] = {}
    loop_list: Dict[int, List[str]] = {}             # distinguishing list vars
    for k in loops:
        inv = invs[k - 1] if 0 <= k - 1 < len(invs) else []
        cv = witness.refine(inv, blocks, loop_ct[k], scalar_bases)
        loop_vars[k] = cv
        loop_list[k] = [v for v in cv if v not in scalar_bases]

    ensure_vars = spec.ensure_vars
    res_ty = _result_type(holes)
    if res_ty:
        ensure_vars = witness.refine(spec.ensure_vars, blocks, res_ty, scalar_bases)

    def loop_of(bases: set) -> Optional[int]:
        for k in loops:
            if any(b in bases for b in loop_list[k]):
                return k
        return None

    def src(vc: VCBlock):                            # the "from" location of a VC
        ctx = vc.context_exists
        if ctx and all(c.endswith("_free") for c in ctx):
            return "precond"
        return loop_of({base_name(c) for c in ctx})

    def dst(vc: VCBlock):                            # the "to" location of a VC
        bases = {base_name(m.lhs) for m in vc.exist_mapping}
        if bases and bases <= set(ensure_vars):
            return "result"
        return loop_of(bases)

    fblocks = [b for b in blocks if b.name.startswith(tmpl.func + "_")]
    entail_by: Dict[tuple, List[VCBlock]] = {}
    return_by: Dict[object, List[VCBlock]] = {}
    for b in fblocks:
        if b.kind == "entail":
            entail_by.setdefault((src(b), dst(b)), []).append(b)
        elif b.kind == "return":
            return_by.setdefault(src(b), []).append(b)

    def arms(vcs, out_group, wrap=None):
        return [(vc, referenced_funccalls(vc, fblocks), out_group, wrap) for vc in vcs]

    def _collect(h, input_group, arm_list):
        if collect is not None:
            collect.append((h, input_group, arm_list))

    repl: Dict[str, str] = {}
    for h in holes:
        k = _loop_index(h.name)
        # A hole whose declared type is `early_result A B` sits at a program point
        # that either continues (`Continue`, into its own carrier) or early-returns
        # (`ReturnNow`, into the function result).  Its entail arms must inject via
        # `Continue` and its early-return arms via `ReturnNow` — otherwise the body
        # returns a bare carrier and the lib does not type-check (the forest path
        # previously passed `wrap=None` for *every* hole, so any early_result hole
        # was malformed).  Non-early holes keep `wrap=None`.
        early = "early_result" in h.type_str
        cont = "Continue" if early else None
        rnow = "ReturnNow" if early else None
        if h.role == "loop_mretty":
            repl[h.name] = f"Definition {h.name} : Type := {loop_ct[k]}."
        elif h.role == "fM1":                        # break branch (fixed)
            repl[h.name] = _definition(h, "fun r => return r.")
        elif h.role == "fM2":                        # loop k body iteration
            # NOTE: a forest loop body with its *own* in-loop early return would be
            # early_result here and would additionally need its guard-true return
            # VCs routed as ReturnNow arms; no benchmark exercises that yet, so only
            # the Continue injection is wired (keeps an early_result body well-typed).
            al = arms(entail_by.get((k, k), []), loop_vars[k], cont)
            _collect(h, loop_vars[k], al)
            repl[h.name] = _definition(h, synth_branched(al, loop_vars[k]))
        elif h.role == "fbefore":                    # precond -> loop k
            entry = arms(entail_by.get(("precond", k), []), loop_vars[k], cont)
            # before-region early returns (`if (x==0) return ...`): their context is
            # all-`_free` (src == "precond"), so they are disjoint from any loop's
            # exit return and inject the result via ReturnNow.
            if early:
                entry += arms(return_by.get("precond", []), ensure_vars, rnow)
            _collect(h, spec.with_vars, entry)
            repl[h.name] = _definition(
                h, synth_branched(entry, spec.with_vars, curried=h.curried))
        elif h.role == "fend":                       # loop k -> result
            al = arms(return_by.get(k, []), ensure_vars)
            _collect(h, loop_vars[k], al)
            repl[h.name] = _definition(h, synth_branched(al, loop_vars[k]))
        elif h.role == "to_inner":                   # loop k -> child loop c
            c = _child_index(h.name)
            al = arms(entail_by.get((k, c), []), loop_vars[c], cont)
            _collect(h, loop_vars[k], al)
            repl[h.name] = _definition(h, synth_branched(al, loop_vars[k]))
        elif h.role == "after_inner":                # child loop c -> loop k
            c = _child_index(h.name)
            resume_vcs = entail_by.get((c, k), [])
            if not resume_vcs:
                # No resume entailment: a strengthened outer invariant (e.g.
                # `lseg(x, stop) * listrep(stop)`) makes the child's exit state
                # *be* the outer carrier, so the solver closed the continue-path
                # entailment trivially and emitted no proof block.  The resume is
                # then the identity — pass the inner loop's result through as the
                # new outer carrier.
                repl[h.name] = _definition(h, "fun r => return r.")
            else:
                # `after_inner` consumes ONLY the child's MretTy (a single
                # argument — see gen_rel_lib's Parameter and both call sites);
                # synthesize it straight from the resume entailment's inner-carrier
                # roots, no extra outer-carrier binder.
                al = arms(resume_vcs, loop_vars[k], cont)
                _collect(h, loop_vars[c], al)
                repl[h.name] = _definition(h, synth_branched(al, loop_vars[c]))
    return repl


def _is_recursive(func: str, blocks: List[VCBlock]) -> bool:
    """A whole-function hole is recursive iff one of its VCs calls the function
    itself (a `funccall_wit` whose callee is `func`)."""
    return any(b.kind == "funccall" and b.call_target == func
               for b in blocks if b.name.startswith(func + "_"))


def _result_type(holes: List[Hole]) -> Optional[str]:
    """The `MONAD <R>` result type of the hole that produces the function result
    (`end` / `M` / `normal`, or the forest's outer-loop `fend`), used to shape the
    `Ensure` tuple."""
    for role in ("end", "M", "normal", "fend"):
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


def _strip_ezval_deep(s: str) -> str:
    """Remove every (flat) `(Ez_val e)` coercion in a term, leaving `e`.  The
    abstract program is over `Z`, so the memory-value wrapper never belongs in a
    synthesized output: `(Ez_val 0)` -> `0`, `cons(Z, (Ez_val 0), l)` ->
    `cons(Z, 0, l)`.  Pointer `(Ez_val 0)` markers live in `leftover_props`/SEP,
    which this does not touch — `facts.augment` still sees them there."""
    prev = None
    while prev != s:
        prev = s
        s = re.sub(r"\(\s*Ez_val\s+([^()]+?)\s*\)", r"\1", s)
    return s


def _normalize_mappings(blocks: List[VCBlock]) -> None:
    """Strip val-coercions from every `exist_mapping` RHS (the synthesized output
    terms).  EliminateLocal-lifted witnesses are stripped on insertion
    (`_merge_witness_substitutions`); this also covers values arriving *directly*
    in `exist_mapping`, e.g. an early-return VC's `v_386 -> (Ez_val 0)`."""
    for b in blocks:
        for m in b.exist_mapping:
            m.rhs = _strip_ezval_deep(m.rhs)


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


def fill_template(template_text: str, autovc_text: str,
                  collect: Optional[list] = None) -> str:
    """Fill the template's holes.  When *collect* is a list, every VC-driven hole
    additionally appends ``(hole, input_group, arms)`` to it — the exact inputs
    and arms used to build that hole's Definition — so the segment-lemma emitter
    can state one refinement lemma per arm from the same data (see
    :mod:`.seg_lemmas`).  Purely additive: with ``collect=None`` the output is
    byte-for-byte unchanged."""
    tmpl = parse_template(template_text)
    spec = parse_spec(autovc_text)
    blocks = parse_blocks(autovc_text)
    # surface scalar data-witness substitutions (EliminateLocal) as mappings
    _merge_witness_substitutions(blocks, set(spec.carrier_vars + spec.ensure_vars))
    _normalize_mappings(blocks)   # (Ez_val e) -> e in every exist_mapping RHS
    # facts.augment(blocks)   # derive list facts from SEP + pointer props (e.g. l != nil)

    # Resolve the abstract carrier / result to their *logical* components: drop
    # pointer existentials, keep lists + data witnesses, ordered to the template
    # (registry-driven — see witness.py).  List-only functions are unchanged.
    scalar_bases = scalar_witness_bases(autovc_text)
    # Loop forest (`_M_loop{k}_*`): several loops, each with its own carrier and
    # result type — filled by per-loop VC routing (see `fill_forest`), not the
    # single-carrier path below.
    forest = any(h.role in ("fM1", "fM2", "fbefore", "fend", "to_inner",
                            "after_inner", "loop_mretty") for h in tmpl.holes)
    forest_repl: Dict[str, str] = {}
    if forest:
        forest_repl = fill_forest(tmpl, blocks, spec, parse_all_invs(autovc_text),
                                  scalar_bases, collect=collect)
    # No-loop early-return shape (`M_before`/`M_normal`): there is no `Inv`, so the
    # abstract carrier is the threaded inputs — the `With` vars — and `MretTy` is
    # their tuple type (the template declares it abstract: `Parameter MretTy`).
    noloop_early = any(h.role in ("before_noloop", "normal") for h in tmpl.holes)
    if noloop_early and not tmpl.carrier_type:
        tmpl.carrier_type = _carrier_type_from_vars(spec.with_vars, scalar_bases)
        spec = Spec(with_vars=spec.with_vars, carrier_vars=list(spec.with_vars),
                    ensure_vars=spec.ensure_vars)
    carrier_vars = spec.carrier_vars
    if tmpl.carrier_type and not noloop_early and not forest:
        carrier_vars = witness.refine(spec.carrier_vars, blocks, tmpl.carrier_type, scalar_bases)
    ensure_vars = spec.ensure_vars
    res_ty = _result_type(tmpl.holes)
    if res_ty and not forest:
        ensure_vars = witness.refine(spec.ensure_vars, blocks, res_ty, scalar_bases)
    spec = Spec(with_vars=spec.with_vars, carrier_vars=carrier_vars, ensure_vars=ensure_vars)

    guard = regions.parse_guard(tmpl.text)

    out = tmpl.text
    for hole in tmpl.holes:
        if hole.name in forest_repl:                    # loop-forest hole (per-loop routing)
            replacement = forest_repl[hole.name]
        elif hole.role == "mretty":                     # type definition, not a segment
            replacement = f"Definition MretTy : Type := {tmpl.carrier_type}."
        elif hole.role == "M1":                          # fixed break branch (no VC drives it)
            replacement = _definition(hole, "fun r => return r.")
        elif hole.role == "M" and _is_recursive(_hole_func(hole.name), blocks):
            # self-recursive function: a `Fixpoint` over a `match` on the
            # recursion argument (the arms' destructuring becomes the patterns).
            input_group, arms = _segment_arms(hole, blocks, spec, guard)
            if collect is not None:               # its self-call makes every arm
                collect.append((hole, input_group, arms))   # call-bearing -> deferred
            body = synth_recursive(arms, input_group[0])
            replacement = _recursive_definition(hole, input_group[0], body)
        elif hole.role in ("before", "M2", "end", "M",
                           "before_noloop", "normal", "fbefore"):
            input_group, arms = _segment_arms(hole, blocks, spec, guard)  # VC-driven: one uniform path
            if collect is not None:
                collect.append((hole, input_group, arms))
            body = synth_branched(arms, input_group, curried=hole.curried)
            replacement = _definition(hole, body)
        else:
            continue
        out = out.replace(hole.raw, replacement, 1)

    # Append frame-based function-call residuals (the continuation after each
    # call).  Only funccall blocks the autovc enriched with a `Frame:` emit one;
    # self-recursive calls are handled by the `Fixpoint` path above, not here.
    from .residual import build_all_residuals
    residuals = build_all_residuals(autovc_text)
    if residuals:
        out = (out.rstrip() + "\n\n"
               + "\n\n".join(rd.definition for rd in residuals) + "\n")
    return out


def fill_from_paths(template_path: str, autovc_path: str,
                    out_path: Optional[str] = None) -> str:
    template_text = Path(template_path).read_text()
    autovc_text = Path(autovc_path).read_text()
    result = fill_template(template_text, autovc_text)
    if out_path is not None:
        Path(out_path).write_text(result)
    return result
