"""Generate the *residual program* (continuation) of a function call from the
data-VC file's `funccall_wit` block — the frame-based counterpart of the
inner-loop tail.

A call site ``r = callee(args)`` lowers to ``r <- callee_M <args> ;; residual r``.
The residual is a *named* `Definition` that closes over the **frame** — the part
of the caller's abstract state the callee does not touch — and takes the callee's
result as its argument:

    Definition residual_prog_in_<caller>_call_<i> (frame... ) : <callee> -> MONAD <caller> :=
      fun r => <continuation>.

The inner-loop tail (`after_inner`) is the degenerate, *empty-frame* instance of
this same splice; a real function call differs only in that its frame is
non-empty and mandatory (the callee is independently specified, so its footprint
cannot absorb the caller's surrounding heap).

Everything is derived from VCs the file already carries, and the body is produced
by :func:`synth.synth_parts` *unchanged* — we hand it a **synthetic continuation
VC** in which the callee result is a root input (so the call itself is not
re-emitted) and the frame's destructured pieces are recovered with `any + assume`.
"""

from __future__ import annotations

import re
import sys
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple

from . import terms
from .frame_sep import translate_frame_sep
from .synth import (base_name, referenced_funccalls, synth_parts,
                    _post_sep_order, _scalar_result_vars)
from .vcparse import (Mapping, Spec, VCBlock, parse_blocks, parse_spec,
                      scalar_witness_bases)

__all__ = ["ResidualDef", "build_residual", "build_all_residuals",
           "inject_residual_annotations"]


@dataclass
class ResidualDef:
    name: str
    definition: str
    params: List[str]                       # captured frame parameters (nameable)
    result_binder: str                      # the callee-result binder, e.g. "r" or "'(pre, v)"
    callee: Optional[str] = None
    call_index: int = 0
    captured_types: Dict[str, str] = field(default_factory=dict)
    signature: str = ""                     # Extern-Coq type: `T1 -> T2 -> Tres -> program unit Tcaller`
    given_params: List[str] = field(default_factory=list)  # params needing `/*@ Given … */`
    frame_sep: str = ""                      # call-site `/*@ exists …, … */` frame assertion


def _func_of(fc_name: str) -> str:
    return re.sub(r"_funccall_wit_\d+$", "", fc_name)


def _call_index(fc_name: str) -> int:
    m = re.search(r"_funccall_wit_(\d+)$", fc_name)
    return int(m.group(1)) if m else 0


def _output_cone(owner: VCBlock) -> set:
    """Variables that flow into the owner VC's output tuple — the exist_mapping
    RHS vars, propagated through list-constructor destructurings.  Pointer guards
    (`retval != (Ez_val 0)`) are *not* outputs, so their vars stay out of the cone."""
    cone: set = set()
    for mp in owner.exist_mapping:
        cone.update(terms.free_vars(terms.parse_term(mp.rhs)))
    changed = True
    while changed:
        changed = False
        for prop in owner.leftover_props:
            m = re.match(r"(.+?)\s*==\s*(.+)", prop)
            if not m:
                continue
            rhs = terms.parse_term(m.group(2))
            if not isinstance(rhs, terms.Op):
                continue
            linked = [m.group(1).strip()] + terms.free_vars(rhs)
            if any(v in cone for v in linked):
                for v in linked:
                    if v not in cone:
                        cone.add(v)
                        changed = True
    return cone


def _cone_post_exists(fc: VCBlock, owner: VCBlock) -> List[str]:
    """The callee's *logical* results — its `post_exists` that actually flow into
    the owner VC's output (so pointer results like `retval` are dropped)."""
    cone = _output_cone(owner)
    return [rv for rv in fc.post_exists if rv in cone]


def _owner_vars(owner: VCBlock) -> set:
    out: set = set()
    for mp in owner.exist_mapping:
        out.update(terms.free_vars(terms.parse_term(mp.rhs)))
    for prop in owner.leftover_props:
        m = re.match(r"(.+?)\s*[=!]=\s*(.+)", prop)
        if m:
            out.add(m.group(1).strip())
            out.update(terms.free_vars(terms.parse_term(m.group(2))))
    return out


def _find_owner(blocks: List[VCBlock], func: str, fc: VCBlock) -> Optional[VCBlock]:
    """The entail/return VC whose program point is *after* the call — i.e. the one
    whose continuation consumes the call's result.  Normally the call's result is
    used directly by that VC; for a **chained** call (`x = f(x,y); x = f(x,z)`)
    the first call's result is consumed by the *next call*, so the continuation VC
    is found instead by the transitive call-chain (`referenced_funccalls`)."""
    fblocks = [b for b in blocks if b.name.startswith(func + "_")]
    want = set(fc.post_exists)
    for b in fblocks:
        if b.kind in ("entail", "return") and want & _owner_vars(b):
            return b
    for b in fblocks:                          # chained: fc is upstream in b's call chain
        if b.kind in ("entail", "return") and fc in referenced_funccalls(b, fblocks):
            return b
    return None


def _downstream_calls(fblocks: List[VCBlock], fc: VCBlock,
                      owner: VCBlock) -> List[VCBlock]:
    """The calls in `owner`'s continuation chain that consume `fc`'s result
    (transitively) — they sit *between* `fc` and the owner, so `fc`'s residual
    must re-emit them.  Empty for a straight (non-chained) call, which keeps the
    common case byte-identical to before."""
    chain = referenced_funccalls(owner, fblocks)
    produced = set(fc.post_exists)
    downstream: List[VCBlock] = []
    changed = True
    while changed:
        changed = False
        for c in chain:
            if c is fc or c in downstream:
                continue
            argvars: set = set()
            for val in c.with_instantiation.values():
                argvars |= set(terms.free_vars(terms.parse_term(val)))
            if argvars & produced:
                downstream.append(c)
                produced |= set(c.post_exists)
                changed = True
    return downstream


def _used_results(fc: VCBlock, owner: VCBlock,
                  downstream: List[VCBlock]) -> List[str]:
    """`fc`'s logical results that flow into the continuation: consumed by a
    downstream call's argument, or directly in the owner's output cone (pointer
    results, used by neither, drop out)."""
    consumers: set = set()
    for c in downstream:
        for val in c.with_instantiation.values():
            consumers |= set(terms.free_vars(terms.parse_term(val)))
    cone = _output_cone(owner)
    results = [rv for rv in fc.post_exists if rv in consumers or rv in cone]
    # Order by the callee's real result-tuple order (its contributed
    # postcondition SEP), not the arbitrary `post_exists` listing — this drives
    # the residual's incoming `'(a, b)` parameter binder, which must match the
    # tuple `fst`/`snd` the caller actually passes.  Falls back to `post_exists`
    # order when the autovc lacks the SEP block (behaviour unchanged there).
    rank = _post_sep_order(fc)
    if rank:
        results.sort(key=lambda rv: rank.get(rv, len(rank)))
    return results


def _order_by_frame(fulls: List[str], frame: List[str]) -> List[str]:
    """Order variables by first appearance in the frame SEP text — the order the
    loop body unfolded them (`store(&node->data, x) * sll(y, l0) * sllseg(.., l1)`
    -> ``x, l0, l1``).  Variables absent from the frame go last, name-stably."""
    text = "\n".join(frame)
    def key(v: str):
        i = text.find(v)
        return (i if i >= 0 else len(text), v)
    return sorted(fulls, key=key)


def _keep_prop(prop: str, scope_bases: set) -> bool:
    """Drop an obsolete unfold destructuring (`parent == cons(pieces...)`) whose
    `parent` is not a residual parameter/result: in the *faithful* residual those
    pieces are captured as parameters directly, so re-deriving them would leave the
    `parent` dangling.  Non-constructor props (pointer guards like
    `retval != (Ez_val 0)`) are kept — the synthesizer ignores them anyway."""
    m = re.match(r"(.+?)\s*==\s*(.+)", prop)
    if not m or not isinstance(terms.parse_term(m.group(2)), terms.Op):
        return True
    return base_name(m.group(1).strip()) in scope_bases


def _strip_outer_parens(s: str) -> str:
    s = s.strip()
    if not (s.startswith("(") and s.endswith(")")):
        return s
    depth = 0
    for i, c in enumerate(s):
        if c == "(":
            depth += 1
        elif c == ")":
            depth -= 1
            if depth == 0 and i != len(s) - 1:
                return s
    return s[1:-1].strip()


def _type_map(owner: VCBlock) -> Dict[str, str]:
    """Infer each variable's Coq type from its operator position in the owner's
    output terms and constructor props (``cons(Z, x, t)`` -> ``x : Z``)."""
    tm: Dict[str, str] = {}
    rhss = [terms.parse_term(mp.rhs) for mp in owner.exist_mapping]
    for prop in owner.leftover_props:
        m = re.match(r".+?\s*==\s*(.+)", prop)
        if m:
            rhss.append(terms.parse_term(m.group(1)))
    for t in rhss:
        for v, ty in terms.collect_var_types(t):
            tm.setdefault(base_name(v), ty)
    return tm


def _ty(base: str, type_map: Dict[str, str], scalar_bases: set) -> str:
    if base in scalar_bases:
        return "Z"
    return type_map.get(base, "list Z")


def _tuple_type(bases: List[str], type_map: Dict[str, str], scalar_bases: set) -> str:
    parts = [_ty(b, type_map, scalar_bases) for b in bases]
    return parts[0] if len(parts) == 1 else "(" + " * ".join(parts) + ")"


def _sub_var(text: str, old: str, new: str) -> str:
    return re.sub(rf"(?<![\w']){re.escape(old)}(?![\w'])", new, text)


def build_residual(
    blocks: List[VCBlock],
    spec: Spec,
    fc: VCBlock,
    *,
    carrier_vars: List[str],
    ensure_vars: List[str],
    scalar_bases: set,
    caller: Optional[str] = None,
) -> Optional[ResidualDef]:
    """Build the residual `Definition` for one `funccall_wit` block, or ``None``
    when the call has no logical (list) result that flows into a continuation
    (e.g. `malloc`, whose result is a bare pointer)."""
    func = _func_of(fc.name)
    if not fc.frame:
        return None                          # only enriched funccall blocks carry a frame
    if fc.call_target == func:
        return None                          # self-recursion is the Fixpoint path, not a residual
    owner = _find_owner(blocks, func, fc)
    if owner is None:
        return None
    fblocks = [b for b in blocks if b.name.startswith(func + "_")]
    downstream = _downstream_calls(fblocks, fc, owner)   # chained calls to re-emit
    results = _used_results(fc, owner, downstream)
    if not results:
        return None

    # A call may return a *scalar* (Z) component — a field-store data value like
    # `store(&(node->data), v, int)` in its postcondition SEP (e.g. `list_tail`'s
    # popped element).  `scalar_witness_bases` only sees simple `&name` stores, so
    # augment the scalar set from the call's (and any re-emitted downstream call's)
    # post_sep; otherwise the callee-result tuple mistypes the scalar as `list Z`
    # and the residual is ill-typed (`v :: l` needs `v : Z`).
    call_scalars = set(_scalar_result_vars(fc.post_sep))
    for c in downstream:
        call_scalars |= set(_scalar_result_vars(c.post_sep))
    scalar_bases = set(scalar_bases) | {base_name(v) for v in call_scalars}

    out_group = carrier_vars if owner.kind == "entail" else ensure_vars

    # Faithful parameters: the SE fresh variables the continuation actually reads —
    # the free vars of the owner's output terms and of any re-emitted downstream
    # call's arguments, minus the callee's own results and any results produced by
    # those downstream calls.  These are exactly the pieces the loop body already
    # unfolded (the frame at the call site — `store(&node->data, x) * sll(y, l0) *
    # sllseg(.., l1)`), so the residual captures `x, l0, l1` *verbatim* rather than
    # resolving them to a nameable parent and re-deriving them with `any + assume`.
    produced_here: set = set(fc.post_exists)
    for c in downstream:
        produced_here |= set(c.post_exists)
    live: List[str] = []
    for mp in owner.exist_mapping:
        if base_name(mp.lhs) in out_group:
            live += terms.free_vars(terms.parse_term(mp.rhs))
    for c in downstream:
        for val in c.with_instantiation.values():
            live += terms.free_vars(terms.parse_term(val))
    param_fulls: List[str] = []
    for v in live:
        if v not in produced_here and v not in param_fulls:
            param_fulls.append(v)
    param_fulls = _order_by_frame(param_fulls, fc.frame)
    full_of: Dict[str, str] = {}
    for v in param_fulls:
        full_of.setdefault(base_name(v), v)        # base name -> full source var
    params = list(full_of)                         # frame order, first occurrence wins
    # A param needs a call-site `/*@ Given … */` *unless* it is a genuine function
    # precondition (`With`/`Require`) variable — those are universally in scope, so
    # they are passed by name with no `Given`.  A precondition var is spelled
    # `<withvar>_<id>_free` (symexec's `_free` suffix) *and* has a base name that is
    # a `With` var; both a loop-`Inv` carrier instance (bare, no `_free`) and an
    # unfold piece (`_free` but base ∉ With, e.g. `x_427_free`/`l0_429_free`) are
    # loop-scoped and therefore need `Given`.
    with_bases = set(spec.with_vars)
    given_params = [p for p in params
                    if not (full_of[p].endswith("_free")
                            and base_name(full_of[p]) in with_bases)]

    type_map = _type_map(owner)

    # Rename callee results whose base collides with a param (or another result),
    # so the synthetic VC keeps the frame list and the callee result distinct.
    taken = set(params) | set(out_group)
    rename: Dict[str, str] = {}
    result_bases: List[str] = []
    for i, rv in enumerate(results):
        base = base_name(rv)
        if base in taken:
            base = f"r{i}"
            rename[rv] = f"{base}_{1000 + i}"        # fresh token, base_name -> rN
        result_bases.append(base)
        taken.add(base)

    def _rewrite(s: str) -> str:
        for old, new in rename.items():
            s = _sub_var(s, old, new)
        return s

    # The synthetic continuation VC: the owner's output assembly + destructurings,
    # with *this* call's results turned into root inputs (rewritten to fresh tokens
    # whose base is the chosen binder name).  `fc` itself is never in `funccalls`,
    # so it is not re-emitted; its results are consumed as already-bound inputs.
    # For a chained call the *downstream* calls ARE passed through (with their args
    # rewritten the same way), so the residual re-emits them — e.g. the first
    # `append`'s residual contains the second `append`.
    syn = VCBlock(name=fc.name + "_residual", kind=owner.kind)
    syn.exist_mapping = [Mapping(mp.lhs, _rewrite(mp.rhs))
                         for mp in owner.exist_mapping
                         if base_name(mp.lhs) in out_group]
    # The unfold destructuring (`l2 == cons(x, l0)`) is obsolete now that its
    # pieces `x, l0` are captured parameters: keep only props whose parent is a
    # param/result, so nothing dangles (see `_keep_prop`).
    scope_bases = set(params) | set(result_bases)
    syn.leftover_props = [_rewrite(p) for p in owner.leftover_props
                          if _keep_prop(p, scope_bases)]

    syn_funccalls: List[VCBlock] = []
    for c in downstream:
        c2 = VCBlock(name=c.name, kind="funccall", call_target=c.call_target)
        c2.post_exists = list(c.post_exists)
        # Carry the contributed postcondition SEP so `synth_parts` can order the
        # re-emitted call's multi-result destructure by the callee's real tuple
        # order (see `synth._post_sep_order`); rewrite its result vars the same way
        # as everything else so the frame/result renaming stays consistent.
        c2.post_sep = [_rewrite(s) for s in c.post_sep]
        c2.with_instantiation = {k: _rewrite(v) for k, v in c.with_instantiation.items()}
        syn_funccalls.append(c2)

    input_group = params + result_bases
    _binder, binds, ret = synth_parts(syn, syn_funccalls, input_group, out_group,
                                      curried=True)

    # Render the Definition: params become explicit arguments, the callee result
    # becomes the `fun <binder> =>` argument.
    if len(result_bases) == 1:
        result_binder = result_bases[0]
    else:
        result_binder = "'(" + ", ".join(result_bases) + ")"

    callee_ty = _tuple_type([base_name(r) for r in results], type_map, scalar_bases)
    captured_types = {p: _ty(p, type_map, scalar_bases) for p in params}

    # The residual is the continuation of the *whole function* after the call, so
    # it must run to the function result.  When the call sits inside the loop body
    # (owner is a loop-step `entail`, whose output is the next *carrier*), the
    # local continuation only computes that next carrier `a'`; the residual then
    # *resumes the loop* from `a'` and applies the post-loop tail —
    # `re <- {func}_M_loop_aux a';; {func}_M_loop_end re` — yielding the function
    # result.  A straight-line call (owner is a `return`) already returns the
    # result, so it is kept as-is.
    in_loop = owner.kind == "entail"
    if in_loop:
        carrier_expr = ret[len("return "):] if ret.startswith("return ") else ret
        re = "re" if "re" not in (set(params) | set(result_bases)) else "re0"
        tail = [f"{re} <- {func}_M_loop_aux {carrier_expr};;",
                f"{func}_M_loop_end {re}."]
        caller_ty = _tuple_type(ensure_vars, type_map, scalar_bases)
    else:
        tail = [ret + "."]
        caller_ty = _tuple_type(out_group, type_map, scalar_bases)

    caller = caller or (func + "_M")
    name = f"residual_prog_in_{caller}_call_{_call_index(fc.name)}"

    arg_decls = "".join(f" ({p} : {captured_types[p]})" for p in params)
    header = (f"Definition {name}{arg_decls} : "
              f"{callee_ty} -> MONAD ({_strip_outer_parens(caller_ty)}) :=")
    body_lines = ([f"  fun {result_binder} =>"]
                  + ["    " + b for b in binds]
                  + ["    " + t for t in tail])
    definition = "\n".join([header] + body_lines)

    # The Extern-Coq type for the `_rel.c` annotation: the same curried signature
    # with `MONAD` written as `program unit` (the symexec annotation spelling).
    signature = " -> ".join(
        [captured_types[p] for p in params]
        + [callee_ty, f"program unit ({_strip_outer_parens(caller_ty)})"])

    # The call-site frame assertion that (re)introduces the residual's loop-scoped
    # params (`x, l0, l1`), derived from the funccall's untouched SEP frame.  With
    # vars are left in scope (not re-bound); see `translate_frame_sep`.
    frame_sep = translate_frame_sep(fc.frame, spec.with_vars)

    return ResidualDef(name=name, definition=definition, params=params,
                       result_binder=result_binder, callee=fc.call_target,
                       call_index=_call_index(fc.name), captured_types=captured_types,
                       signature=signature, given_params=given_params,
                       frame_sep=frame_sep)


def build_all_residuals(autovc_text: str) -> List[ResidualDef]:
    """Build residuals for every list-returning call in an autovc file."""
    spec = parse_spec(autovc_text)
    blocks = parse_blocks(autovc_text)
    scalar_bases = scalar_witness_bases(autovc_text)
    out: List[ResidualDef] = []
    for fc in blocks:
        if fc.kind != "funccall":
            continue
        rd = build_residual(blocks, spec, fc, carrier_vars=spec.carrier_vars,
                            ensure_vars=spec.ensure_vars, scalar_bases=scalar_bases)
        if rd is not None:
            out.append(rd)
    return out


# ---- inject residual annotations into the `_rel.c` ------------------------

# A sibling/self call site already carrying the `low_level_spec_aux` continuation
# annotation that stage-1 emitted: `<lhs> = callee(args) /*@ where(...) <clause> */;`.
_CALL_ANNOT_RE = re.compile(
    r'^([ \t]*)'                                             # 1: indent
    r'(.*?\b(\w+)\s*\([^()]*\))[ \t]*'                       # 2: call expr, 3: callee
    r'(/\*@\s*where\(low_level_spec_aux\)\s*)'               # 4: annotation head
    r'(.*?)'                                                 # 5: clause (X = X; B = ...)
    r'(\s*\*/)[ \t]*;',                                      # 6: annotation tail
    re.MULTILINE)

_EXTERN_RE = re.compile(r'/\*@\s*Extern Coq\b.*?\*/', re.DOTALL)


def _append_residual_externs(text: str, residuals: List[ResidualDef]) -> str:
    """Declare each residual's signature so the annotation parser knows it,
    appended after the last existing `Extern Coq` block (or the Import line)."""
    lines = "".join(f"\n/*@ Extern Coq ({rd.name}: {rd.signature}) */"
                    for rd in residuals)
    externs = list(_EXTERN_RE.finditer(text))
    if externs:
        pos = externs[-1].end()
    else:
        imp = re.search(r'/\*@\s*Import Coq[^\n]*\*/', text)
        if not imp:
            return lines.lstrip("\n") + "\n" + text
        pos = imp.end()
    return text[:pos] + lines + text[pos:]


_EXISTS_HEAD_RE = re.compile(r"/\*@\s*exists\s+([^,]+),")
_CALLER_RE = re.compile(r"^residual_prog_in_(.+)_call_\d+$")


def _frame_exists_vars(frame_sep: str) -> List[str]:
    """The existential var names bound by a frame assertion's ``exists …,`` head
    (``[]`` when the assertion has no ``exists`` — a pure in-scope frame)."""
    m = _EXISTS_HEAD_RE.match(frame_sep)
    return m.group(1).split() if m else []


def _apply_var_rename(text: str, rename: Dict[str, str]) -> str:
    """Rename whole-word variables in ``text`` per ``rename`` in a single pass
    (so a replacement is never re-scanned).  Only names present in ``rename`` are
    touched — heap-pred heads, field names, types, and program vars (``node``,
    ``src@pre``) are left alone."""
    if not rename:
        return text
    return re.sub(r"\b\w+\b", lambda m: rename.get(m.group(0), m.group(0)), text)


def _frame_rename_maps(residuals: List[ResidualDef]) -> Dict[int, Dict[str, str]]:
    """Per-residual rename map giving each frame existential a distinct call-site
    spelling, so two calls in one function do not clash on a function-scoped
    ``/*@ Given … */``.  Each frame var ``v`` becomes ``v_frame`` (first use in the
    caller) or ``v_<n>_frame`` (its n-th, n≥2); counting is per **caller function**
    (the scope a `Given` lives in) in call-index order.  Ambient `With` vars never
    reach here — they are not frame existentials — so they keep their bare names."""
    by_caller: Dict[str, List[ResidualDef]] = {}
    for rd in residuals:
        cm = _CALLER_RE.match(rd.name)
        by_caller.setdefault(cm.group(1) if cm else rd.name, []).append(rd)
    out: Dict[int, Dict[str, str]] = {}
    for rds in by_caller.values():
        counts: Dict[str, int] = {}
        for rd in sorted(rds, key=lambda r: r.call_index):
            m: Dict[str, str] = {}
            for v in _frame_exists_vars(rd.frame_sep):
                n = counts.get(v, 0) + 1
                counts[v] = n
                m[v] = f"{v}_frame" if n == 1 else f"{v}_{n}_frame"
            out[id(rd)] = m
    return out


def inject_residual_annotations(relc_text: str, autovc_text: str) -> str:
    """Fill the `cont` of every frame-call `where(low_level_spec_aux)` site in a
    `_rel.c`: declare each residual `Extern Coq`, instantiate ``cont =
    residual(params)``, and introduce any non-`With` params (loop-`Inv`
    existentials) with a `/*@ Given … */` before the call.  Files with no
    frame-carrying calls (``build_all_residuals`` empty) are returned unchanged."""
    residuals = build_all_residuals(autovc_text)
    if not residuals:
        return relc_text
    # Each residual already records which of its params need `/*@ Given … */`
    # (`rd.given_params`) — the ones bound by an intermediate annotation rather
    # than the function precondition — decided per call site in `build_residual`,
    # NOT by a global first-match `parse_spec` (which, on a multi-function autovc,
    # would read the wrong function's carrier; see the README `Given` TODO).
    text = _append_residual_externs(relc_text, residuals)

    # Distinct `_frame` spelling per call site so multiple calls in one function
    # do not collide on a function-scoped `/*@ Given … */` (see `_frame_rename_maps`).
    rename_of = _frame_rename_maps(residuals)

    # Group residuals + call sites by callee.  We only inject when the counts
    # match exactly: a callee with N call sites must have N residuals to know
    # which residual belongs to which call.  A mismatch means a *chained* call
    # whose continuation contains a further call — build_residual emits only the
    # tail residual, so some call sites have no residual; rather than mis-assign,
    # we skip that callee and warn (those files need chained-call residuals).
    res_by_callee: Dict[str, List[ResidualDef]] = {}
    for rd in residuals:
        res_by_callee.setdefault(rd.callee, []).append(rd)
    for rds in res_by_callee.values():
        rds.sort(key=lambda r: r.call_index)

    site_count: Dict[str, int] = {}
    for m in _CALL_ANNOT_RE.finditer(text):
        site_count[m.group(3)] = site_count.get(m.group(3), 0) + 1

    queue: Dict[str, List[ResidualDef]] = {}
    for callee, rds in res_by_callee.items():
        if site_count.get(callee, 0) == len(rds):
            queue[callee] = list(rds)
        else:
            print(f"residual-annotation: skipped callee {callee!r} "
                  f"({len(rds)} residual(s) vs {site_count.get(callee, 0)} call "
                  f"site(s) — chained calls not yet supported)", file=sys.stderr)

    def repl(m: "re.Match") -> str:
        indent, call_expr, callee, clause = m.group(1), m.group(2), m.group(3), m.group(5)
        rds = queue.get(callee)
        if not rds:
            return m.group(0)                  # no residual for this call: leave as-is
        rd = rds.pop(0)
        # Rename this call site's frame existentials to their distinct `_frame`
        # spellings (bare `With` params are not in the map, so they pass through).
        rmap = rename_of.get(id(rd), {})
        cont_args = [rmap.get(p, p) for p in rd.params]
        cont = rd.name if not rd.params else f"{rd.name}({', '.join(cont_args)})"
        new_clause = clause.replace("X = X", f"X = X, cont = {cont}", 1)
        # When the residual introduces loop-scoped params (`given_params`), precede
        # the call with the frame assertion that names them and the `/*@ Given … */`
        # that brings them into scope; a residual over only in-scope `With` vars
        # (no `given_params`) needs neither.
        prefix = ""
        if rd.given_params:
            if rd.frame_sep:
                frame_sep = _apply_var_rename(rd.frame_sep, rmap)
                frame_block = "\n".join(indent + ln for ln in frame_sep.splitlines())
                prefix += frame_block + "\n"
            given = " ".join(rmap.get(p, p) for p in rd.given_params)
            prefix += f"{indent}/*@ Given {given} */\n"
        return f"{prefix}{indent}{call_expr} {m.group(4)}{new_clause}{m.group(6)};"

    return _CALL_ANNOT_RE.sub(repl, text)
