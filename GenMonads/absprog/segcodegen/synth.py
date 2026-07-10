"""Synthesize an abstract-program segment body from a single VC proof block.

A segment has type ``<inputs> -> MONAD <outputs>``.  The proof block fixes the
output lists as terms over the input lists plus some *fresh* variables; the job
is to find those fresh variables and explain each one.

Each fresh variable is *produced* by exactly one step:

* a **call** step ``r <- FN_M args``, when the variable is annotated
  ``[r: from call to FN]`` (arguments come from the matching ``funccall_wit``
  block's *Callee With-variable instantiation*);
* a **constraint** step ``v <- any <ty>;; ... assume!! (known = term)``, when the
  variable appears in a leftover prop ``known == term``.  Every fresh variable
  in ``term`` is introduced with its type inferred from the operator signatures
  (so ``l2 == cons(Z, x, t)`` gives ``x : Z``, ``t : list Z``).

A step *consumes* the variables it references.  Because a call argument may use
a destructured variable, or a constraint may destructure a call result, the
steps are emitted in **topological order** of these producer/consumer
dependencies — not a fixed "constraints then calls" phase.

Nothing here is specific to lists or to ``cons``/``app`` — operator shapes come
entirely from :mod:`.terms` / the signature data file.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple

from . import terms
from .terms import Op, Term, Var
from .vcparse import VCBlock


def base_name(v: str) -> str:
    """`l1_384_free` -> `l1`, `l3_445` -> `l3`, `x_427_free` -> `x`."""
    v = re.sub(r"_free$", "", v)
    v = re.sub(r"_\d+$", "", v)
    return v


def _natural_key(s: str):
    return [int(t) if t.isdigit() else t for t in re.split(r"(\d+)", s)]


def _scalar_result_vars(post_sep: List[str]) -> set:
    """Post-existentials that a call returns as a **scalar (Z)** — the `data`
    value of a *field store with a non-pointer C type*, e.g.
    ``store(&(retval->data), v, signed int)`` marks ``v`` scalar.  These are the
    `addabstract` *data witnesses*, which are appended to the abstract result
    tuple *after* the list components (see `_post_sep_order`)."""
    out: set = set()
    for atom in post_sep:
        # field store `store(&(p->f), VALUE, TYPE)` — value then type
        m = re.search(r"store\(\s*&\([^)]*\)\s*,\s*(\w+)\s*,\s*([^,)]+)\)", atom)
        if m and "*" not in m.group(2):
            out.add(m.group(1))
        # simple store `store(&name, TYPE, VALUE)` — type then value
        m = re.search(r"store\(\s*&(\w+)\s*,\s*([^,]+?)\s*,\s*(\w+)\s*\)", atom)
        if m and "*" not in m.group(2):
            out.add(m.group(3))
    return out


def _post_sep_order(fb: VCBlock) -> Dict[str, int]:
    """Rank each of a call's post-existentials to reflect the callee's real
    abstract result-tuple order, read from the call's *contributed postcondition
    SEP* (``fb.post_sep``).

    The SEP reproduces the callee's ``Ensure`` heap conjuncts.  The tuple order
    `addabstract` builds from that Ensure is: **list/heap components first, in
    their SEP-conjunct order, then scalar data-witnesses appended last** (the
    ``store(&(_->data), v, int)`` values — see :func:`_scalar_result_vars`).
    A borrowing copy (``sll(src@pre, l2) * sll(__return, l3)``) has no scalar, so
    its two lists keep SEP order ``(l2, l3)``; ``list_tail``
    (``… data == v … sllseg(x, __return, l2)``) returns ``(l2, v)`` — the list
    ``l2`` first, the scalar ``v`` last — even though ``v`` precedes ``l2`` in the
    SEP.  This matches the callee's generated ``_M`` tuple, so the destructure
    pattern binds ``fst``/``snd`` to the right components.  A *pointer*
    existential (a returned address) gets a rank too but the output cone drops it,
    so only the surviving components' relative order matters.

    Empty when the autovc predates this block (older tool output); callers then
    keep the legacy ``post_exists`` order."""
    post = set(fb.post_exists)
    scalars = _scalar_result_vars(fb.post_sep)
    appear: List[str] = []
    seen: set = set()
    for tok in re.findall(r"[A-Za-z_]\w*", "\n".join(fb.post_sep)):
        if tok in post and tok not in seen:
            seen.add(tok)
            appear.append(tok)
    ordered = [v for v in appear if v not in scalars] + [v for v in appear if v in scalars]
    return {v: i for i, v in enumerate(ordered)}


def _any_type(ty: str) -> str:
    ty = ty.strip()
    return f"({ty})" if " " in ty else ty


def referenced_funccalls(vc: VCBlock, blocks: List[VCBlock]) -> List[VCBlock]:
    """The funccall blocks whose list results this VC (transitively) consumes.

    Empty for a pure entailment with no calls — which is the common case.  The
    closure is over logical-list dataflow: a call is referenced if one of its
    list results appears in this VC, and any call producing an *argument* of a
    referenced call is pulled in too (chained calls).  Pointer-only calls (e.g.
    `malloc`, whose results never appear in a list position) are not included.
    """
    produces: Dict[str, VCBlock] = {}
    for fb in blocks:
        if fb.kind != "funccall":
            continue
        for rv in fb.post_exists:
            produces.setdefault(rv, fb)

    # variables this VC consumes in a logical-list position
    work: List[str] = []
    for mp in vc.exist_mapping:
        work += terms.free_vars(terms.parse_term(mp.rhs))
    for prop in vc.leftover_props:
        m = re.match(r"(.+?)\s*==\s*(.+)", prop)
        if not m:
            continue
        rhs = terms.parse_term(m.group(2))
        if isinstance(rhs, Op):            # `lhs == <list constructor>`
            work.append(m.group(1).strip())
            work += terms.free_vars(rhs)

    result: List[VCBlock] = []
    seen: set[int] = set()
    while work:
        fb = produces.get(work.pop())
        if fb is None or id(fb) in seen:
            continue
        seen.add(id(fb))
        result.append(fb)
        for val in fb.with_instantiation.values():   # chase arguments (chained calls)
            work += terms.free_vars(terms.parse_term(val))
    return result


def _all_variables(vc: VCBlock, funccalls: List[VCBlock]) -> set:
    """Every logical variable occurring in this VC's context, mappings, props,
    and (for call argument tracing) the referenced funccalls' With-instantiations."""
    out: set[str] = set(vc.context_exists)
    for mp in vc.exist_mapping:
        out.update(terms.free_vars(terms.parse_term(mp.rhs)))
    for prop in vc.leftover_props:
        m = re.match(r"(.+?)\s*[=!]=\s*(.+)", prop)
        if m:
            out.add(m.group(1).strip())
            out.update(terms.free_vars(terms.parse_term(m.group(2))))
    for fb in funccalls:
        for v in fb.with_instantiation.values():
            out.update(terms.free_vars(terms.parse_term(v)))
    return out


class _Names:
    """Allocates clean Coq identifiers for fresh variables, by type."""

    def __init__(self, reserved: List[str]) -> None:
        self._taken: set[str] = set(reserved)
        self._elem = 0
        self._res = 0

    def _uniquify(self, base: str) -> str:
        name = base
        while name in self._taken:
            name += "'"
        self._taken.add(name)
        return name

    def for_type(self, ty: str, hint: Optional[str]) -> str:
        if ty.strip().startswith("list") and hint:
            return self._uniquify(hint + "'")
        base = "x" if self._elem == 0 else f"x{self._elem - 1}"
        self._elem += 1
        return self._uniquify(base)

    def result(self) -> str:
        base = "r" if self._res == 0 else f"r{self._res - 1}"
        self._res += 1
        return self._uniquify(base)


@dataclass(frozen=True)
class Bind:
    """One rendered bind line *plus* the structure it was rendered from.

    ``text`` is the Coq source (the single source of truth for the Definition
    body); the remaining fields are the structure captured **at emit time**, when
    the final Coq identifiers (post ``_Names`` allocation / ``known`` resolution)
    are in hand.  Downstream consumers (:func:`_match_branch`, the lemma emitter
    in :mod:`.seg_lemmas`) read these fields directly instead of re-parsing
    ``text`` — so a change to the rendering can never silently desync a reader.

    ``kind`` is one of ``"any" | "assume" | "call"``:

    * ``any``    — ``var <- any (ty);;`` introduces ``var`` at raw type ``ty``.
    * ``assume`` — ``assume!! (lhs rel rhs);;`` a guard; ``rel`` is ``"="``/``"<>"``.
    * ``call``   — ``<results> <- callee_M args;;`` binds ``results`` (rendered Coq
      names, in tuple order) from ``callee`` (base name, no ``_M``).
    """
    text: str
    kind: str
    var: Optional[str] = None                 # any: introduced name
    ty: Optional[str] = None                  # any: raw (unparenthesized) type
    lhs: Optional[str] = None                 # assume: resolved lhs name
    rel: Optional[str] = None                 # assume: "=" | "<>"
    rhs: Optional[str] = None                 # assume: rendered term
    results: Tuple[str, ...] = ()             # call: bound result names
    callee: Optional[str] = None              # call: callee base (no "_M")

    @property
    def prop(self) -> str:                    # assume: the full guard proposition
        return f"{self.lhs} {self.rel} {self.rhs}"


@dataclass
class _Step:
    """One emitted bind (or group of binds) producing some fresh variables."""
    idx: int
    kind: str                                   # "call" | "constraint"
    produces: Tuple[str, ...]
    refs: Tuple[str, ...]                        # variables it consumes
    # call payload
    rv: Optional[str] = None
    callee: Optional[str] = None
    arg_terms: Tuple[Term, ...] = ()
    # constraint payload
    lhs: Optional[str] = None
    term: Optional[Term] = None
    rel: str = "="                              # Coq relation: "=" (==) or "<>" (!=)
    intro: Tuple[Tuple[str, str], ...] = ()     # (var, type) to introduce via any


def synth_arm(
    vc: VCBlock,
    funccalls: List[VCBlock],
    input_group: List[str],
    output_group: List[str],
    *,
    curried: bool = False,
    wrap: Optional[str] = None,
) -> Tuple[str, List[Bind], str]:
    """Synthesize one segment as structured parts: (binder, :class:`Bind` list,
    return).  Each :class:`Bind` carries both its rendered ``text`` and the
    structure it came from, so readers never re-parse the string.
    :func:`synth_parts` is the string-only view over this.

    `funccalls` are the (precomputed) funccall blocks this VC depends on — see
    :func:`referenced_funccalls`; usually empty.  Returning parts (rather than a
    joined string) lets branched segments share a common prefix across arms.

    `wrap`, when given (e.g. ``"Continue"`` / ``"ReturnNow"``), wraps the returned
    expression in that constructor at construction time — for `early_result`-typed
    holes."""
    names = _Names(input_group)

    # output terms, by tuple position
    out_terms: List[Optional[Term]] = [None] * len(output_group)
    for mp in vc.exist_mapping:
        b = base_name(mp.lhs)
        if b not in output_group:
            continue
        out_terms[output_group.index(b)] = terms.parse_term(mp.rhs)
    out_terms = [t if t is not None else Var("(* missing *)") for t in out_terms]

    # Inline solver-emitted *definitions* of intermediate ``_free`` variables so
    # the output is expressed purely over the segment's inputs.  Two sources:
    #   (a) ``exist_mapping`` entries whose lhs is NOT an output var — the solver
    #       named an intermediate (``l0_624_free -> l3_620_free``);
    #   (b) leftover props ``X == term`` where ``X`` is a lone non-input,
    #       non-output variable (``l3_620_free == l2_2 ++ l2_3``).
    # Without this, an output like ``l2_1 ++ (v :: l0_624_free)`` keeps an
    # unbound ``l0_624_free`` and its defining prop becomes a bogus ``assume!!``.
    # Only the solver's own intermediate existentials (``…_free``) are inlined —
    # never inputs, outputs, or call results (``res_50``, ``retval_17``), whose
    # binds must survive as `any`/destructure/call steps.  And only when the
    # ``_free`` var actually flows into the OUTPUT: a ``…_free == nil`` on a
    # destructure tail that never reaches the result is a discriminating *guard*
    # (``assume!! (l1' = nil)``), not a definition, and must stay.
    subst_cand: Dict[str, Term] = {}
    prop_lhs: Dict[str, int] = {}      # candidate free-var -> its leftover prop index
    for mp in vc.exist_mapping:
        if mp.lhs.endswith("_free") and base_name(mp.lhs) not in output_group:
            subst_cand.setdefault(mp.lhs, terms.parse_term(mp.rhs))
    for pi, prop in enumerate(vc.leftover_props):
        m = re.match(r"(.+?)\s*==\s*(.+)", prop)
        if not m:
            continue
        lhs = m.group(1).strip()
        lterm = terms.parse_term(lhs)
        if (isinstance(lterm, Var)
                and lhs.endswith("_free")
                and base_name(lhs) not in input_group
                and base_name(lhs) not in output_group):
            subst_cand.setdefault(lhs, terms.parse_term(m.group(2)))
            prop_lhs.setdefault(lhs, pi)
    # Closure of the output's free vars under the candidate keys — only these
    # substitutions are actually applied (and their defining props consumed).
    definitional_props: set[int] = set()
    if subst_cand:
        reached: set[str] = set()
        work = [v for t in out_terms for v in terms.free_vars(t)]
        while work:
            v = work.pop()
            if v in reached or v not in subst_cand:
                continue
            reached.add(v)
            work.extend(terms.free_vars(subst_cand[v]))
        free_subst = {k: subst_cand[k] for k in reached}
        for _ in range(len(free_subst) + 1):      # resolve chains to a fixpoint
            nxt = {k: terms.substitute(v, free_subst) for k, v in free_subst.items()}
            if all(terms.render(nxt[k], {}) == terms.render(free_subst[k], {})
                   for k in free_subst):
                break
            free_subst = nxt
        out_terms = [terms.substitute(t, free_subst) for t in out_terms]
        definitional_props = {prop_lhs[k] for k in reached if k in prop_lhs}

    # A variable is *introduced* by a function call iff it is one of that call's
    # *Postcondition existentials*.  Everything else is a **root**: a variable
    # bound by the annotation that precedes this VC's program point — the loop
    # `Inv` when the point is inside/after that loop (loop-body step, post-loop
    # return), or the function's `With`/`Require` precondition when no in-body
    # annotation precedes it (the loop-entry VC, or any VC of a loop-free
    # function).  Which annotation that is, is encoded by the caller's choice of
    # `input_group` (carrier vars vs With vars).  The roots whose base name is an
    # input (`l1_388_free` -> `l1`) are the segment's inputs; they may sit
    # directly in the context (a plain assignment / loop entry) or be reached
    # only by tracing a call's argument instantiation (here `list_append_raw(x,
    # y)` feeds the roots `l1_388_free`/`l2_387_free`).  No call is assumed.
    introduced_by_call: set[str] = set()
    for fb in funccalls:
        introduced_by_call.update(fb.post_exists)

    # The *output cone*: the variables that actually flow into the result tuple,
    # reached from `out_terms` through list-constructor equations (`lhs == term`
    # with `lhs` already in the cone) and through chained-call arguments.  A
    # call's projected results are its post-existentials *in* this cone — so a
    # post-existential that feeds only a dropped data witness (e.g. the numeric
    # return of a list-returning recursive call) is not mistaken for an extra
    # tuple component.
    cone: set[str] = set()
    for t in out_terms:
        cone.update(terms.free_vars(t))
    changed = True
    while changed:
        changed = False
        for pi, prop in enumerate(vc.leftover_props):
            if pi in definitional_props:      # already inlined into the outputs
                continue
            m = re.match(r"(.+?)\s*==\s*(.+)", prop)
            if not m:
                continue
            rhs = terms.parse_term(m.group(2))
            if not isinstance(rhs, Op):       # only logical-list constructor equations
                continue
            # the equation `lhs == cons(h, t)` links both sides: a destructured
            # call result (`res == cons(h, t)`, lhs fresh) is reached *from* its
            # components, and a constructed output reaches *into* them — so the
            # cone propagates in either direction.
            linked = [m.group(1).strip()] + terms.free_vars(rhs)
            if any(v in cone for v in linked):
                for v in linked:
                    if v not in cone:
                        cone.add(v); changed = True
        for fb in funccalls:
            if any(rv in cone for rv in fb.post_exists):
                for val in fb.with_instantiation.values():
                    for v in terms.free_vars(terms.parse_term(val)):
                        if v not in cone:
                            cone.add(v); changed = True

    # ---- build candidate steps & the producer index ----
    steps: List[_Step] = []
    producer: Dict[str, _Step] = {}   # fresh var -> the step that produces it

    # call steps: a funccall block's logical results are its abstract return.  A
    # callee may return *several* logical values (e.g. `list_tail : list Z ->
    # MONAD (list Z * Z)` yields a prefix list and the popped element); they
    # appear together in `post_exists` in the callee's result-tuple order.  One
    # `r <- FN_M args` binds the whole result and each component is projected
    # out of it (`fst`/`snd`) — see `_proj`.
    for fb in funccalls:
        results = [rv for rv in fb.post_exists if rv in cone and rv not in producer]
        if not results:
            continue
        # Order the projected results by the callee's actual result-tuple order,
        # read from the call's contributed postcondition SEP (see
        # `_post_sep_order`).  The raw `post_exists` list order does NOT track the
        # tuple order, so the `'(a, b)` destructure would otherwise bind `fst`/
        # `snd` to the wrong logical values.  Falls back to `post_exists` order
        # when the autovc has no such SEP block.
        rank = _post_sep_order(fb)
        if rank:
            results.sort(key=lambda rv: rank.get(rv, len(rank)))
        ordered = sorted(fb.with_instantiation.items(), key=lambda kv: _natural_key(kv[0]))
        arg_terms = tuple(terms.parse_term(v) for _, v in ordered)
        refs = tuple(v for t in arg_terms for v in terms.free_vars(t))
        st = _Step(idx=len(steps), kind="call", produces=tuple(results), refs=refs,
                   rv=results[0], callee=fb.call_target, arg_terms=arg_terms)
        steps.append(st)
        for rv in results:
            producer[rv] = st

    # bind every root whose base name is an input to its canonical name
    known: Dict[str, str] = {}
    for v in _all_variables(vc, funccalls):
        if base_name(v) in input_group and v not in introduced_by_call:
            known[v] = base_name(v)

    # constraint steps: every logical-list prop `root <rel> term` (`rel` is `==`
    # or `!=`) becomes an `assume!!` guard.  An `==` over a list constructor with
    # not-yet-known variables introduces the fresh (non-input, not-yet-produced)
    # ones of `term` (`l2 == cons(Z,x,t)` -> `x <- any Z;; t <- any (list Z);;
    # assume!! (l2 = x :: t)`).  A constraint introducing no fresh variable is a
    # *pure guard* (`l == nil`, `l != nil`); it is kept too (it produces nothing,
    # only constrains an in-scope variable).  A `!=` is always a pure guard — we
    # never `any`-introduce variables under a disequality (it would be vacuous).
    # The `isinstance(term, Op)` filter keeps only list-constructor RHSs, which
    # excludes pointer (dis)equalities like `x != (Ez_val 0)` (RHS is a bare Var).
    for pi, prop in enumerate(vc.leftover_props):
        if pi in definitional_props:          # inlined into the outputs, not a guard
            continue
        m = re.match(r"(.+?)\s*([=!]=)\s*(.+)", prop)
        if not m:
            continue
        lhs, op, rhs = m.group(1).strip(), m.group(2), m.group(3).strip()
        term = terms.parse_term(rhs)
        if not isinstance(term, Op):          # only logical-list (dis)equations
            continue
        rel = "=" if op == "==" else "<>"
        if rel == "=":
            intro = [(v, ty) for v, ty in terms.collect_var_types(term)
                     if base_name(v) not in input_group and v not in producer]
        else:
            intro = []                         # disequality is a pure guard
        produced = {v for v, _ in intro}
        refs = tuple([lhs] + [v for v in terms.free_vars(term) if v not in produced])
        st = _Step(idx=len(steps), kind="constraint", produces=tuple(produced), refs=refs,
                   lhs=lhs, term=term, rel=rel, intro=tuple(intro))
        steps.append(st)
        for v in produced:
            producer.setdefault(v, st)

    # ---- inclusion: every step feeding an output, plus every pure guard (and
    #      whatever produces the variables it constrains) ----
    included: set[int] = set()
    work = [v for t in out_terms for v in terms.free_vars(t)]
    for st in steps:
        if st.kind == "constraint" and not st.intro:   # pure guard, kept globally
            included.add(st.idx)
            work.extend(st.refs)
    while work:
        st = producer.get(work.pop())
        if st is None or st.idx in included:
            continue
        included.add(st.idx)
        work.extend(st.refs)

    order = _schedule([s for s in steps if s.idx in included], set(known))

    # ---- emit ----
    binds: List[Bind] = []
    for st in order:
        if st.kind == "constraint":
            for v, ty in st.intro:
                name = names.for_type(ty, known.get(st.lhs))
                known[v] = name
                binds.append(Bind(f"{name} <- any {_any_type(ty)};;",
                                  "any", var=name, ty=ty))
            lhs = known.get(st.lhs, st.lhs)
            rhs = terms.render(st.term, known)
            binds.append(Bind(f"assume!! ({lhs} {st.rel} {rhs});;",
                              "assume", lhs=lhs, rel=st.rel, rhs=rhs))
        else:  # call
            args = [terms.render(t, known, top=False) for t in st.arg_terms]
            if len(st.produces) == 1:
                name = names.result()
                binds.append(Bind(f"{name} <- {st.callee}_M {' '.join(args)};;",
                                  "call", results=(name,), callee=st.callee))
                known[st.produces[0]] = name
            else:                            # multi-result callee: destructure
                comps = [names.result() for _ in st.produces]
                pat = "'(" + ", ".join(comps) + ")"
                binds.append(Bind(f"{pat} <- {st.callee}_M {' '.join(args)};;",
                                  "call", results=tuple(comps), callee=st.callee))
                for rv, nm in zip(st.produces, comps):
                    known[rv] = nm

    if not out_terms:                        # empty output tuple -> unit (`tt`, not `()`)
        inner = "tt"
    elif len(out_terms) == 1:
        # single output: render parenthesized so a compound (`l1 ++ l2`) is not
        # mis-parsed after `return` (where `++` would bind looser than the term).
        inner = terms.render(out_terms[0], known, top=False)
    else:
        inner = "(" + ", ".join(terms.render(t, known) for t in out_terms) + ")"
    if wrap:                                  # early_result constructor: Continue / ReturnNow
        inner = f"{wrap} ({inner})"           # parens: the arg may be `a ++ b`, a tuple, …
    return _binder(input_group, curried), binds, f"return {inner}"


def synth_parts(
    vc: VCBlock,
    funccalls: List[VCBlock],
    input_group: List[str],
    output_group: List[str],
    *,
    curried: bool = False,
    wrap: Optional[str] = None,
) -> Tuple[str, List[str], str]:
    """String-only view over :func:`synth_arm`: (binder, rendered bind lines,
    return).  Kept as the stable API for callers that only need the text."""
    binder, binds, ret = synth_arm(vc, funccalls, input_group, output_group,
                                   curried=curried, wrap=wrap)
    return binder, [b.text for b in binds], ret


def _step_key(st: "_Step"):
    """Intrinsic, branch-stable ordering key for tie-breaking ready steps."""
    primary = st.lhs if st.kind == "constraint" else (st.rv or "")
    return (0 if st.kind == "constraint" else 1, _natural_key(primary))


def _schedule(steps: List["_Step"], available: set) -> List["_Step"]:
    """Eager (as-soon-as-ready) linearization: a step is emitted once every
    variable it references is in scope.  Independent ready steps are ordered by
    `_step_key`, so sibling branches linearize shared binds identically."""
    available = set(available)
    remaining = list(steps)
    order: List["_Step"] = []
    while remaining:
        ready = [s for s in remaining if all(r in available for r in s.refs)]
        if not ready:                     # dependency cycle / unsatisfiable — emit rest as-is
            ready = remaining[:]
        st = min(ready, key=_step_key)
        order.append(st)
        available.update(st.produces)
        remaining.remove(st)
    return order


def synth_entail(
    vc: VCBlock,
    funccalls: List[VCBlock],
    input_group: List[str],
    output_group: List[str],
    *,
    curried: bool = False,
) -> str:
    """Synthesize a single (unbranched) segment body as a Coq term string."""
    binder, binds, ret = synth_parts(vc, funccalls, input_group, output_group, curried=curried)
    return _assemble(binder, binds, ret)


def _assemble(binder: str, binds: List[str], ret: str) -> str:
    return "\n".join([binder] + ["    " + b for b in binds] + ["    " + ret + "."])


def _common_prefix(lists: List[List[str]]) -> List[str]:
    prefix: List[str] = []
    for col in zip(*lists):
        if all(x == col[0] for x in col):
            prefix.append(col[0])
        else:
            break
    return prefix


def _arm_lines(binds: List[str], ret: str, pad: str) -> List[str]:
    inner = list(binds) + [ret]
    if len(inner) == 1:
        return [f"{pad}( {inner[0]} )"]
    out = [f"{pad}( {inner[0]}"]
    out += [f"{pad}  {l}" for l in inner[1:-1]]
    out.append(f"{pad}  {inner[-1]} )")
    return out


def _choice_lines(arms: List[Tuple[List[str], str]], pad: str) -> List[str]:
    """Right-nested binary `choice` over the arms (each a (binds, ret) pair).

    `choice` is a binary combinator, so a chain of three or more arms must
    parenthesize its second operand: ``choice A (choice B (choice C D))``.
    Without the parens ``choice A choice B …`` parses as ``choice`` over-applied
    to four arguments."""
    if len(arms) == 1:
        return _arm_lines(arms[0][0], arms[0][1], pad)
    lines = [f"{pad}choice"]
    lines += _arm_lines(arms[0][0], arms[0][1], pad + "  ")
    rest = arms[1:]
    if len(rest) == 1:
        lines += _arm_lines(rest[0][0], rest[0][1], pad + "  ")
    else:                                    # wrap the nested choice in parens
        lines.append(pad + "  (")
        lines += _choice_lines(rest, pad + "    ")
        lines.append(pad + "  )")
    return lines


def _compose_arms(parts: List[Tuple[str, List[str], str]]) -> str:
    """Combine pre-synthesized arms (binder, binds, ret) by factoring their
    longest common bind prefix and combining the divergent tails with `choice`.
    A single arm renders as-is (no `choice`, no wrapping parens)."""
    if len(parts) == 1:
        return _assemble(*parts[0])
    binder = parts[0][0]
    bind_lists = [p[1] for p in parts]
    prefix = _common_prefix(bind_lists)
    k = len(prefix)
    arm_parts = [(p[1][k:], p[2]) for p in parts]
    lines = [binder] + ["    " + b for b in prefix] + _choice_lines(arm_parts, "    ")
    lines[-1] += "."
    return "\n".join(lines)


# An arm: (vc, its referenced funccalls, that arm's output group, optional wrap).
Arm = Tuple[VCBlock, List[VCBlock], List[str], Optional[str]]


def synth_branched(
    arms: List[Arm],
    input_group: List[str],
    *,
    curried: bool = False,
) -> str:
    """Synthesize one segment from several branch arms (e.g. a loop body with an
    inner `if`, or an `early_result` point with both fall-through and early
    return).  Each arm carries its own output group and optional return wrap
    (``"Continue"`` / ``"ReturnNow"`` for `early_result`, ``None`` otherwise), so
    a plain branch (uniform output, no wrap) and an early-result branch
    (Continue arms over the carrier + ReturnNow arms over the result) are the
    same construction.  Each arm is synthesized independently; their longest
    common bind prefix is emitted once and the divergent tails combined with
    `choice`.  The first divergent bind of each arm is its discriminating guard
    (`assume!! (v = h :: t)` vs `assume!! (v = nil)`, or `v <> nil` vs `v = nil`),
    so the arms are mutually exclusive."""
    parts = [synth_parts(vc, fcs, input_group, out, curried=curried, wrap=wrap)
             for vc, fcs, out, wrap in arms]
    return _compose_arms(parts)


def _match_branch(binds: List[Bind], ret: str, input_var: str) -> Tuple[str, List[str]]:
    """Turn one synthesized arm into a `match` branch on `input_var`.

    The arm discriminates the recursion argument with `v <- any T;; … assume!!
    (input_var = <pattern>)`.  In a `match` that destructuring is the branch
    pattern itself, so we read the pattern off the `assume` :class:`Bind`, drop it
    together with the `any` binds of the variables it introduces (now bound by the
    pattern), and keep the rest as the branch body.  An arm with no such
    destructuring keeps all its binds under a wildcard."""
    destructure = None
    for b in binds:
        if b.kind == "assume" and b.lhs == input_var and b.rel == "=":
            destructure = b
    if destructure is None:
        return "_", [b.text for b in binds] + [ret]
    pattern = destructure.rhs
    pat_vars = set(re.findall(r"[A-Za-z_][\w']*", pattern))
    kept = []
    for b in binds:
        if b is destructure:
            continue
        if b.kind == "any" and b.var in pat_vars:   # the freshes are now match-bound
            continue
        kept.append(b.text)
    return pattern, kept + [ret]


def synth_recursive(arms: List[Arm], input_var: str) -> str:
    """Assemble a structurally-recursive body: a `match` on the single recursion
    argument whose branches are the synthesized arms with their destructuring
    `any + assume` replaced by the match pattern.  A self-call on the matched
    tail is then a structural subterm, so the enclosing definition can be a
    `Fixpoint`."""
    lines = [f"match {input_var} with"]
    for vc, fcs, out, wrap in arms:
        _binder, binds, ret = synth_arm(vc, fcs, [input_var], out, wrap=wrap)
        pattern, body = _match_branch(binds, ret, input_var)
        if len(body) == 1:
            lines.append(f"| {pattern} => {body[0]}")
        else:
            lines.append(f"| {pattern} =>")
            lines += [f"    {b}" for b in body]
    lines.append("end")
    return "\n".join(lines)


def _binder(input_group: List[str], curried: bool) -> str:
    if curried:                       # several separate arguments: fun a b c =>
        return "fun " + " ".join(input_group) + " =>"
    if len(input_group) == 1:
        return f"fun {input_group[0]} =>"
    return "fun '(" + ", ".join(input_group) + ") =>"   # one tuple argument
