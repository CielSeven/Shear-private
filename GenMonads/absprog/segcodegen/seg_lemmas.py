"""Emit per-arm ``safeExec`` refinement-lemma **statements** for a filled lib.

For each VC-driven segment arm (one wit), state the lemma that the segment, run
on its symbolic inputs, refines ``return <output>`` — the abstract program being
stateless (``Σ = unit``), this is exactly the wit's denotational claim
"``<output>`` is a possible result of the segment":

    Lemma seg_<wit> :
      forall <inputs> <fresh>, <guards> ->
        forall X, safeExec (@ATrue unit) (SEG <inputs>) X ->
                  safeExec (@ATrue unit) (return <output>) X.
    Proof. Admitted.

The output term, guards, and fresh (`any`) variables are read from the *same*
:class:`~.synth.ArmParts` the Definition body was built from (via the ``collect``
hook of :func:`~.fill_template`), so a lemma can never drift from the code it
certifies.

Scope (P0–P1): **statements only**, ``Admitted`` bodies — the goal is a
type-checking file across every hole shape (curried/tupled binders,
``Continue``/``ReturnNow`` wraps, forest glue).  Arms that introduce a value via
a **function call** get **no lemma**: their segment is ``r <- callee_M …;; return
f r``, whose refinement is obtained by *composing* the callee's own segment lemma
with the bind rule — there is no primitive per-arm ``return <output>`` fact to
state.  Such arms are skipped (counted at the tooling level, not written to the
file).
"""

from __future__ import annotations

import re
import sys
from dataclasses import dataclass, field
from typing import List, Optional, Tuple


def _warn(msg: str) -> None:
    """Surface a coverage-loss event on stderr (codebase idiom: tagged print).

    A skipped arm produces *no* lemma text — silent, it reads as full coverage,
    so every skip must announce itself and say why."""
    print(f"[seg_lemmas] WARN {msg}", file=sys.stderr)

from . import fill_template
from .synth import Bind, synth_arm
from .template import Hole, _arg_type


# ---- structured arm view -----------------------------------------------------
#
# :func:`synth_arm` returns the segment as ``(binder, [Bind], return)``, where
# every :class:`~.synth.Bind` carries both its rendered ``text`` (the source of
# truth for the Definition body) *and* the structure it was rendered from — the
# `any`-introduced fresh vars, the `assume!!` guards, the `r <- callee_M …` calls.
# The lemma emitter reads that structure off the fields directly, so it can never
# desync from the rendering the way a string re-parse would.


@dataclass
class _Arm:
    """One synthesized arm, structured for the lemma emitter."""
    binder_vars: List[str]
    curried: bool
    bind_objs: List[Bind]
    ret: str
    any_binds: List[Tuple[str, str]] = field(default_factory=list)   # (name, coq type)
    guards: List[str] = field(default_factory=list)                  # assume propositions
    calls: List[Tuple[Tuple[str, ...], str]] = field(default_factory=list)  # (results, callee)
    vc_name: str = ""


def _arm_view(vc, fcs, input_group: List[str], out_group: List[str],
              curried: bool, wrap: Optional[str]) -> _Arm:
    _binder, binds, ret = synth_arm(vc, fcs, input_group, out_group,
                                    curried=curried, wrap=wrap)
    return _Arm(
        binder_vars=list(input_group), curried=curried, bind_objs=binds, ret=ret,
        any_binds=[(b.var, b.ty) for b in binds if b.kind == "any"],
        guards=[b.prop for b in binds if b.kind == "assume"],
        calls=[(b.results, b.callee) for b in binds if b.kind == "call"],
        vc_name=getattr(vc, "name", ""),
    )


# ---- type-string helpers (depth-aware; no assumptions about the carrier) ----

def _split_top(s: str, sep: str) -> List[str]:
    """Split *s* on top-level (paren-depth 0) occurrences of *sep* (``"->"`` or
    ``"*"``)."""
    parts, depth, i, start = [], 0, 0, 0
    while i < len(s):
        c = s[i]
        if c == "(":
            depth += 1
        elif c == ")":
            depth -= 1
        elif depth == 0 and s.startswith(sep, i):
            parts.append(s[start:i])
            i += len(sep)
            start = i
            continue
        i += 1
    parts.append(s[start:])
    return [p.strip() for p in parts]


def _strip_outer_parens(s: str) -> str:
    """Drop one matching outer paren layer wrapping the whole string."""
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
                return s          # the opening paren closes early -> not a full wrap
    return s[1:-1].strip()


def _resolve_type(ty: str, lib_text: str) -> str:
    """Expand a ``Definition <alias> : Type := <tuple>.`` alias to its tuple — a
    forest ``after_inner`` hole is typed by the child loop's ``_M_loop{k}_MretTy``
    alias, which the segment binder destructures componentwise."""
    ty = ty.strip()
    m = re.search(rf"Definition\s+{re.escape(ty)}\s*:\s*Type\s*:=\s*(.+?)\.\s*$",
                  lib_text, re.M)
    return m.group(1).strip() if m else ty


def _input_types(hole: Hole, binder_vars: List[str], lib_text: str) -> List[str]:
    """The Coq type of each input variable, read off the hole's declared type
    (resolving a ``MretTy`` type-alias carrier to its component tuple)."""
    if hole.curried:                                   # T1 -> T2 -> ... -> MONAD R
        head = hole.type_str.split("MONAD", 1)[0]
        segs = [s for s in _split_top(head, "->") if s]  # drop the trailing "" after ->
        if len(segs) < len(binder_vars):               # malformed/miscounted hole type
            _warn(f"'{hole.name}': type '{hole.type_str}' exposes {len(segs)} "
                  f"argument type(s) but the segment has {len(binder_vars)} binder(s); "
                  f"padding missing types with 'Type' (lemma may not type-check)")
            segs = segs + ["Type"] * (len(binder_vars) - len(segs))
        return segs[:len(binder_vars)]
    arg = _arg_type(hole.type_str) or ""               # CARRIER -> MONAD R
    if len(binder_vars) == 1:
        return [arg]
    return _split_top(_strip_outer_parens(_resolve_type(arg, lib_text)), "*")


def _seg_app(hole: Hole, binder_vars: List[str]) -> str:
    """How the segment Definition is applied to its inputs, mirroring the binder:
    curried ``SEG a b c``, tupled ``SEG (a, b, c)``, or single ``SEG a``."""
    if hole.curried:
        return f"{hole.name} " + " ".join(binder_vars)
    if len(binder_vars) == 1:
        return f"{hole.name} {binder_vars[0]}"
    return f"{hole.name} (" + ", ".join(binder_vars) + ")"


_LEMMA_HEADER = "(* ---- Per-segment safeExec refinement lemmas ---- *)"


# Inline proof automation.  Discharges every arm (call-free/call-bearing,
# no-`any`/`any`) to Qed.  Built only from the framework *lemmas* — never
# `safeExec_proequiv`, and never the `safe_step`/`safe_choice_*` tactics (those
# close guards with a bare `auto`, silently taking the wrong `choice` branch when
# arms carry complementary guards).  `seg_solve` peels the hypothesis head:
#   * `prog_nf` + `cbv beta iota` normalise binds and collapse the `let '(a,b) :=
#     (u,v) in _` that a multi-result `bind_ret_l` leaves behind;
#   * `assume!!` -> `safeExec_test_bind`, guard closed by `seg_guard` (a false
#     guard *fails*, so the enclosing `+` backtracks to the other branch);
#   * `choice`  -> `choice_l`/`choice_r` under `+` (branch chosen by backtracking:
#     decision-(b); generator-directed selection by arm index is a TODO);
#   * `any`     -> `safeExec_any_bind`, leaving the witness an evar pinned
#     downstream by `seg_guard`'s `eassumption` (plain `auto` won't touch goal
#     evars) or, absent a guard, by the final `exact H`;
#   * `_ => fail` so a stuck (wrong-branch) head fails cleanly at level 0 rather
#     than raising `lazymatch`'s uncatchable "No matching clauses".
# See TODO/segment_refinement_lemmas_plan.md (P2-P4) for the full derivation.
_PROOF_PRELUDE = """(* Per-arm safeExec refinement automation (see seg_lemmas.py for rationale). *)
Ltac seg_guard := solve [ eassumption | auto | congruence | tauto | lia ].
Ltac seg_solve H :=
  prog_nf in H; cbv beta iota in H;
  first
  [ exact H
  | lazymatch type of H with
    | safeExec _ ((assume!! _) ;; _) _ =>
        apply safeExec_test_bind in H; [ seg_solve H | seg_guard ]
    | safeExec _ (choice _ _) _ =>
        (apply safeExec_choice_l in H + apply safeExec_choice_r in H); seg_solve H
    | safeExec _ (bind (any _) _) _ =>
        eapply safeExec_any_bind in H; seg_solve H
    | _ => fail   (* stuck head: clean level-0 fail so `+`/`first` can backtrack *)
    end ].
Ltac seg_grab := match goal with H : safeExec _ _ _ |- _ => seg_solve H end."""


def _sanitize(name: str) -> str:
    return re.sub(r"[^A-Za-z0-9_']", "_", name)


def _proof(hole: Hole, arm: _Arm) -> str:
    """The proof script for one arm; every arm is discharged by `seg_grab` (§4).

    Two per-arm switches:

    * **unfold** — a *call-free* arm's LHS is the segment `Definition` (`unfold`
      it to expose the body); a *call-bearing* arm's LHS is already inlined by the
      call→`return r_ret` substitution, so there is nothing to unfold.
    * **subst** — for *no-`any`* arms, `subst` collapses guard equalities (`l1 =
      nil`, `l1 = x :: l1'`) so a recursive-`Fixpoint` M's `match l1 with ...`
      reduces and an `end`-arm's `l1 ++ l2` output matches `l1 ++ nil` (no-op for
      inequality guards / plain `bind` chains).  For *`any`* arms (P3) we must NOT
      `subst`: the guard hypothesis is what `assumption` uses to pin the `any`
      witness evars introduced by `safeExec_any_bind` — `subst`ing it away would
      strand those evars."""
    subst = "" if arm.any_binds else "subst; "
    unfold = "" if arm.calls else f"unfold {hole.name} in *; "
    return f"Proof. intros; {subst}{unfold}cbv beta iota in *; seg_grab. Qed."


def _tuple_components(ty: str) -> List[str]:
    """Split a (possibly redundantly-parenthesized) product type into its
    component types: ``((list Z * Z))`` -> ``["list Z", "Z"]``."""
    s = ty.strip()
    while True:
        s2 = _strip_outer_parens(s)
        if s2 == s:
            break
        s = s2
    return _split_top(s, "*")


def _callee_result_type(callee: str, texts: List[str]) -> Optional[str]:
    """The ``R`` in ``<callee>_M : … -> MONAD R``, read from the filled lib or a
    sibling ``*_rel_lib.v`` (``Definition`` / ``Parameter`` / recursive
    ``Fixpoint``).  Returns ``None`` if not found (then the arm is skipped)."""
    for text in texts:
        m = re.search(rf"(?:Definition|Parameter|Fixpoint)\s+{re.escape(callee)}_M\b(.*?)(?::=|\.)",
                      text, re.S)
        if not m:
            continue
        mm = re.search(r"MONAD\s*(.+)$", m.group(1).strip(), re.S)
        if mm:
            return mm.group(1).strip()
    return None


def _fresh(base: str, taken: set) -> str:
    name = base
    while name in taken:
        name += "'"
    taken.add(name)
    return name


def _subst_vars(s: str, mapping: dict) -> str:
    """Whole-word substitution of call-result names by their quantified
    ``*_ret`` existentials (so guards/outputs reference the forall-bound var)."""
    if not mapping:
        return s
    pat = r"\b(" + "|".join(re.escape(k) for k in mapping) + r")\b"
    return re.sub(pat, lambda m: mapping[m.group(1)], s)


def _call_subst(arm: _Arm, texts: List[str], taken: set):
    """For a call-bearing arm, build the inlined LHS body: each ``r <- callee_M
    args`` bind becomes ``r <- return r_ret``, where ``r_ret`` is a fresh
    forall-bound existential at the callee's ``_M`` result type; non-call binds
    are kept verbatim (by their rendered ``text``).  Returns ``(lhs_lines,
    ret_binders, name_map)`` or ``None`` if a callee result type can't be
    resolved (arm skipped)."""
    lhs_lines: List[str] = []                        # LHS body, in emit order
    ret_binders: List[str] = []                      # `(r_ret : T)` forall binders
    name_map: dict = {}                              # call-result name -> r_ret var
    for b in arm.bind_objs:
        if b.kind != "call":
            lhs_lines.append(b.text)
            continue
        results = list(b.results)
        R = _callee_result_type(b.callee, texts)
        if R is None:
            _warn(f"skipping seg lemma for '{arm.vc_name or '?'}': cannot resolve "
                  f"result type of '{b.callee}_M' (searched {len(texts)} lib(s)) "
                  f"-- this refinement obligation is NOT certified")
            return None
        if len(results) == 1:
            rv = _fresh(results[0] + "_ret", taken)
            ret_binders.append(f"({rv} : {R})")
            name_map[results[0]] = rv
            lhs_lines.append(f"{results[0]} <- return {rv};;")
        else:                                        # multi-result: one r_ret per component
            comps = _tuple_components(R)
            rvs = []
            for res, cty in zip(results, comps):
                rv = _fresh(res + "_ret", taken)
                ret_binders.append(f"({rv} : {cty})")
                name_map[res] = rv
                rvs.append(rv)
            pat = "'(" + ", ".join(results) + ")"
            lhs_lines.append(f"{pat} <- return ({', '.join(rvs)});;")
    return lhs_lines, ret_binders, name_map


def _lemma(hole: Hole, input_group: List[str], arm: _Arm, idx: int,
           lib_text: str, texts: List[str]) -> Optional[str]:
    """Render one arm's refinement lemma.  A **call-free** arm refines
    ``return <output>`` directly from the segment Definition.  A **call-bearing**
    arm's segment is ``… r <- callee_M args;; …``; since the callee result is an
    existential on both sides, we substitute the call with ``r <- return r_ret``
    (``r_ret`` a fresh forall-bound existential at the callee's result type) — the
    lemma then certifies that surrounding computation refines ``return <output>``
    over ``r_ret``.  Returns ``None`` if a callee type can't be resolved."""
    lemname = "seg_" + (_sanitize(arm.vc_name) if arm.vc_name else f"{hole.name}_arm{idx}")

    binders = [f"({v} : {ty})"
               for v, ty in zip(input_group, _input_types(hole, input_group, lib_text))]
    binders += [f"({name} : {ty})" for name, ty in arm.any_binds]

    if not arm.calls:                                # call-free: LHS is `SEG inputs`
        lhs = _seg_app(hole, input_group)
        ret, hyps_src = arm.ret, arm.guards
    else:                                            # call-bearing: substitute the call
        taken = set(input_group) | {n for n, _ in arm.any_binds} \
            | {r for res, _ in arm.calls for r in res}
        plan = _call_subst(arm, texts, taken)
        if plan is None:
            return None
        lhs_lines, ret_binders, name_map = plan
        # LHS: the inlined body (call → return r_ret); r stays local, bound by the
        # return.  RHS/hyps reference the forall-bound r_ret instead.
        lhs = "(" + "\n     ".join(lhs_lines + [arm.ret]) + ")"
        binders += ret_binders
        ret = _subst_vars(arm.ret, name_map)
        hyps_src = [_subst_vars(g, name_map) for g in arm.guards]

    forall_in = "forall " + " ".join(binders) + ",\n" if binders else ""
    hyps = "".join(f"  {g} ->\n" for g in hyps_src)
    return (
        f"Lemma {lemname} :\n"
        f"  {forall_in}"
        f"{hyps}"
        f"  forall X,\n"
        f"    safeExec (@ATrue unit) ({lhs}) X ->\n"
        f"    safeExec (@ATrue unit) ({ret}) X.\n"
        f"{_proof(hole, arm)}"
    )


# ---- loop-body branch-selection lemmas (layer 1) + fused (layer 2) ----------
#
# The per-arm lemmas reduce an *already-selected* loop-body arm (`M_loop_M2 a ⊑
# return Continue s`).  The loop body itself is a `choice`; before any arm lemma
# applies, the whole-function proof must *select the branch*.  We emit that as its
# own certified lemma:
#   * layer 1 — one per branch, keyed on the guard: `M_loop_body a ⊑ ⟨branch⟩`,
#     proved by `unfold …_M_loop_body; cbv beta iota; seg_grab` (kept abstract in
#     `a`);
#   * layer 2 — per wit, by *composition*: `apply ⟨select⟩; eapply
#     safeExec_bind_reta with (a := ⟨arm result⟩); [.. | apply ⟨arm lemma⟩]; cbv;
#     exact` — the arm lemma is exactly `safeExec_bind_reta`'s `c1 ⊑ ret a`
#     premise, and `cbv` does the `match`/iota step.
# Only `M_loop_M1`/`M_loop_M2` arms get these (not `before`/`end`).

# The loop *stem* is `{F}_M_loop` (single loop) or `{F}_M_loop{k}` (forest / multi
# -loop, e.g. `iter_back_2`); its body is `{stem}_body` and its arm holes are
# `{stem}_M{j}`.  The `\d*` absorbs the loop index so both shapes are handled.
_LOOP_MK_RE = re.compile(r"^(.*_M_loop\d*)_(M\d)$")
_LOOP_BODY_RE = re.compile(
    r"Definition\s+(\w+_M_loop\d*_body)\s*:\s*(.+?)\s*->\s*MONAD\b.*?:="
    r"(.*?)(?=\n\s*Definition\b|\n\s*repeat_break\b)", re.S)


@dataclass
class _LoopBranch:
    mk: str            # "M1" | "M2"
    guard: str         # guard proposition (references the lambda param `a`)
    body: str          # branch body after the guard: `r <- {F}_M_loop_Mk a ;; ⟨cont⟩`
    cont: str          # continuation after the `M_loop_Mk a` call (`continue a'` / `match …`)
    side: str          # "l" | "r" — position in the `choice` (for `safeExec_choice_{l,r}`)


@dataclass
class _LoopBody:
    name: str          # the `{F}_M_loop[k]_body` Definition name
    state_ty: str
    branches: List[_LoopBranch]

    @property
    def stem(self) -> str:                    # `{F}_M_loop[k]` (drops the `_body`)
        return self.name[:-len("_body")]


def _paren_groups(s: str) -> List[str]:
    """Contents of the top-level ``(...)`` groups of *s*, in order."""
    groups: List[str] = []
    depth, start = 0, None
    for i, c in enumerate(s):
        if c == "(":
            if depth == 0:
                start = i + 1
            depth += 1
        elif c == ")":
            depth -= 1
            if depth == 0 and start is not None:
                groups.append(s[start:i])
    return groups


def _guard_core(g: str) -> Tuple[bool, str]:
    """Split a guard into (is-negated, core proposition), stripping ``~`` and
    redundant parens: ``~ (guardP a)`` -> ``(True, "guardP a")``, ``(guardP a)``
    -> ``(False, "guardP a")``.  Lets two branch guards be compared for
    complementarity (`G` vs `~G`) regardless of parenthesization."""
    g = _strip_outer_parens(g.strip())
    neg = False
    while g.startswith("~"):
        neg = not neg
        g = _strip_outer_parens(g[1:].strip())
    return neg, re.sub(r"\s+", " ", g).strip()


def _branches_complementary(branches: List["_LoopBranch"]) -> bool:
    """A well-formed loop body's two branches guard on ``G`` and ``~G`` (the
    ``guardP`` true/false split).  Anything else is an unexpected skeleton shape."""
    if len(branches) != 2:
        return False
    (n0, c0), (n1, c1) = _guard_core(branches[0].guard), _guard_core(branches[1].guard)
    return n0 != n1 and c0 == c1


def _parse_loop_bodies(lib_text: str) -> dict:
    """Map ``func -> _LoopBody`` by parsing each concrete ``{func}_M_loop_body``
    ``choice`` definition (guard + branch body for each of the two arms)."""
    out: dict = {}
    for m in _LOOP_BODY_RE.finditer(lib_text):
        name, state_ty, body = m.group(1), m.group(2).strip(), m.group(3)
        idx = body.find("choice")
        if idx < 0:
            continue
        branches: List[_LoopBranch] = []
        for i, g in enumerate(_paren_groups(body[idx + len("choice"):])[:2]):
            g = g.strip()
            gg = _paren_groups(g)
            if not gg or ";;" not in g:
                continue
            guard = gg[0].strip()
            after = g.split(";;", 1)[1].strip()
            mk = re.search(r"_M_loop\d*_(M\d)\b", after)   # `_M_loop_M1` or `_M_loop2_M1`
            if not mk:
                continue
            cont = after.split(";;", 1)[1].strip() if ";;" in after else ""
            branches.append(_LoopBranch(mk=mk.group(1), guard=guard, body=after,
                                        cont=cont, side="l" if i == 0 else "r"))
        if branches:
            # `side` is the operand position (what `choice_{l,r}` consume) and each
            # branch's guard/body are parsed together, so branch *order* is handled
            # correctly by construction.  What we cannot assume is the *shape*: warn
            # loudly if the two guards are not the expected complementary `G`/`~G`
            # split, rather than silently emitting lemmas for a loop we misread.
            if not _branches_complementary(branches):
                _warn(f"loop body '{name}': branch guards are not the expected "
                      f"complementary G / ~G split "
                      f"({[b.guard for b in branches]}); unexpected skeleton shape")
            out[name] = _LoopBody(name=name, state_ty=state_ty, branches=branches)
    return out


def _select_lemma(lb: _LoopBody, br: _LoopBranch) -> Tuple[str, str]:
    """Layer-1 branch-selection lemma for one ``choice`` arm (abstract in ``a``).

    The proof is *deterministic* — the branch's `choice` side is known at
    generation time (`br.side`) and its guard is the lemma hypothesis — so it
    selects that side directly (`safeExec_choice_{l,r}`) and discharges the
    `assume!!` guard by name, rather than relying on `seg_grab`'s backtracking
    (which mis-drives the break/`M1` branch)."""
    name = f"seg_{lb.stem}_select_{br.mk}"
    text = (
        f"Lemma {name} :\n"
        f"  forall (a : {lb.state_ty}),\n"
        f"  {br.guard} ->\n"
        f"  forall X,\n"
        f"    safeExec (@ATrue unit) ({lb.name} a) X ->\n"
        f"    safeExec (@ATrue unit) ({br.body}) X.\n"
        "Proof.\n"
        "  intros a Hg X H.\n"
        f"  unfold {lb.name} in H; cbv beta iota in H.\n"
        f"  apply safeExec_choice_{br.side} in H.\n"
        "  apply safeExec_test_bind in H; [ exact H | exact Hg ].\n"
        "Qed."
    )
    return text, name


def _leaf_kck(leaf: str) -> Tuple[str, str]:
    """The K-applied form and unfold keyword for a bare ``continue E`` / ``break
    E`` leaf.  Under the ``repeat_break`` continuation ``K = fun x => match x with
    by_continue a' => kc a' | by_break r => kb r`` we have ``x <- continue E ;; K
    x`` reduces to ``kc E`` (``continue E = ret (by_continue E)``, then
    ``bind_ret_l``), and ``break E`` to ``kb E``.  ``E`` may be a wrapped payload
    (``Continue r``) — the early-return loop's normal-exit branch."""
    leaf = leaf.strip()
    if leaf.startswith("continue"):
        return f"kc {leaf[len('continue'):].strip()}", "continue"
    if leaf.startswith("break"):
        return f"kb {leaf[len('break'):].strip()}", "break"
    return leaf, ""


_MATCH_CONT_RE = re.compile(r"^match\s+(.+?)\s+with\s+(.*)\s+end\b", re.S)


def _parse_match_cont(cont: str):
    """Parse a ``match SCRUT with | Ctor vars => leaf | ... end`` continuation into
    ``(scrut, [(ctor, [vars], leaf), ...])``; ``None`` if *cont* is a bare leaf."""
    m = _MATCH_CONT_RE.match(cont.strip())
    if not m:
        return None
    scrut, arms_text = m.group(1).strip(), m.group(2)
    arms = []
    for chunk in arms_text.split("|"):
        chunk = chunk.strip()
        if not chunk:
            continue
        am = re.match(r"(.+?)\s*=>\s*(.+)", chunk, re.S)
        if not am:
            return None
        pat = am.group(1).split()
        arms.append((pat[0], pat[1:], am.group(2).strip()))
    return (scrut, arms) if arms else None


def _selectcont_lemma(lb: "_LoopBody", br: "_LoopBranch", sel_name: str) -> Tuple[str, str]:
    """Continuation-form (match-wrapped) select lemma, derived from the bare
    ``sel_name`` via the framework's bind-left-congruence
    ``safeExec_bind_partial_target``.  Reduces one ``repeat_break`` step —
    ``bind (M_loop_body a) ⟨by_continue/by_break match⟩`` — directly to
    ``bind (M_loop_M{k} a) ⟨selected continuation⟩``, so a whole-function proof
    (P6) picks the branch in a single ``apply`` instead of unfolding + peeling.

    Only for *simple* loops (bare ``continue``/``break`` arms).  The call term
    ``M_loop_M{k} a`` is abstracted with ``remember … in *`` before normalizing so
    that monad-law rewrites stay symmetric between hypothesis and goal even when an
    arm hole is definitionally ``ret`` (which would otherwise collapse only the
    hypothesis)."""
    call_prefix = br.body.split(";;", 1)[0].strip()      # `<binder> <- {stem}_M{k} a`
    binder, _, call_term = (s.strip() for s in call_prefix.partition("<-"))
    name = f"seg_{lb.stem}_selectcont_{br.mk}"
    parsed = _parse_match_cont(br.cont)
    if parsed is None:
        # Bare leaf `continue E` / `break E` (E may be wrapped, e.g. `break
        # (Continue r)` for an early-return loop's normal-exit branch).
        kck, unfold_kw = _leaf_kck(br.cont)
        new_rhs = f"{call_prefix} ;; {kck}"
        tail = (f"  unfold {unfold_kw} in H.\n"
                "  prog_nf in H. cbv beta iota in H. exact H.\n")
    else:
        # Branched early-return arm `match a' with Continue …|ReturnNow …`: push
        # the outer continuation into each arm, then close the residual
        # bind-over-match by `destruct` + `bind_ret_l` per constructor.  The
        # `choice`/guard was already resolved by the bare select, so this pure
        # match-commute equivalence is safe to route through `safeExec_proequiv`.
        scrut, arms = parsed
        rhs_arms, proof_arms, pat_intros = [], [], []
        for ctor, vars_, leaf in arms:
            kck, unfold_kw = _leaf_kck(leaf)
            rhs_arms.append(f"       | {' '.join([ctor] + vars_)} => {kck}")
            pat_intros.append(" ".join(vars_) if vars_ else "_")
            proof_arms.append(f"  - unfold {unfold_kw}. rewrite bind_ret_l. reflexivity.")
        new_rhs = (f"{call_prefix} ;;\n"
                   f"       match {scrut} with\n"
                   + "\n".join(rhs_arms) + "\n"
                   "       end")
        tail = (
            "  prog_nf in H. cbv beta iota in H.\n"
            "  eapply safeExec_proequiv; [ | exact H ].\n"
            "  apply bind_equiv; [ reflexivity | ].\n"
            f"  intros {scrut}.\n"
            f"  destruct {scrut} as [ " + " | ".join(pat_intros) + " ].\n"
            + "\n".join(proof_arms) + "\n"
        )
    text = (
        f"Lemma {name} :\n"
        f"  forall (a : {lb.state_ty}) (R : Type)\n"
        f"         (kc : _ -> MONAD R) (kb : _ -> MONAD R),\n"
        f"  {br.guard} ->\n"
        f"  forall X,\n"
        f"    safeExec (@ATrue unit)\n"
        f"      (x <- {lb.name} a ;;\n"
        f"       match x with\n"
        f"       | by_continue a' => kc a'\n"
        f"       | by_break r => kb r\n"
        f"       end) X ->\n"
        f"    safeExec (@ATrue unit) ({new_rhs}) X.\n"
        "Proof.\n"
        "  intros a R kc kb Hg X H.\n"
        "  eapply safeExec_bind_partial_target in H.\n"
        f"  2:{{ intros X0 H0. apply {sel_name} in H0; [ exact H0 | exact Hg ]. }}\n"
        "  2:{ reflexivity. }\n"
        f"  remember ({call_term}) as m_arm in *.\n"
        + tail +
        "Qed."
    )
    return text, name


def _reduce_cont(cont: str, arm_ret_value: str) -> str:
    """The continuation ``cont`` applied to the arm's result and reduced: a bare
    ``continue a'``/``break a'`` substitutes the result; a ``match a' with
    Continue …|ReturnNow …`` picks the branch by the result's head constructor."""
    cont = cont.strip()
    if cont.startswith("match"):
        head, _, payload = arm_ret_value.partition(" ")
        if head == "Continue":
            return f"continue {payload.strip()}"
        return f"break ({arm_ret_value})"          # ReturnNow r' => break (ReturnNow r')
    kw = cont.split()[0] if cont else "continue"    # continue | break
    return f"{kw} ({arm_ret_value})"


def _fused_lemma(lb: _LoopBody, br: _LoopBranch, select_name: str, hole: Hole,
                 input_group: List[str], arm: _Arm, arm_lemname: str,
                 lib_text: str) -> str:
    """Layer-2 fused lemma: ``M_loop_body ⊑ ⟨reduced arm result⟩`` by composing
    the branch-selection lemma with the arm lemma via ``safeExec_bind_reta``."""
    tup = "(" + ", ".join(input_group) + ")"
    guard_inst = re.sub(r"\ba\b", tup, br.guard)
    arm_ret = arm.ret[len("return "):].strip() if arm.ret.startswith("return ") else arm.ret
    fused_rhs = _reduce_cont(br.cont, arm_ret)

    binders = [f"({v} : {ty})"
               for v, ty in zip(input_group, _input_types(hole, input_group, lib_text))]
    binders += [f"({n} : {t})" for n, t in arm.any_binds]
    forall_in = "forall " + " ".join(binders) + ",\n" if binders else ""
    hyps = f"  {guard_inst} ->\n" + "".join(f"  {g} ->\n" for g in arm.guards)
    name = f"seg_{lb.stem}_loopbody_{_sanitize(arm.vc_name)}"
    # Pass the arm lemma's binders *explicitly* (input group ++ `any` vars, in the
    # order `_lemma` declared them): a var that occurs only in a guard (e.g. `l2'`
    # in a `ReturnNow` arm, absent from the output) is otherwise not inferrable by
    # unification.  `match goal` only *renames* the (unique) exec hypothesis — it
    # cannot fail, so it does not mask errors — then the proven proto-style linear
    # script runs (select the branch, compose the arm lemma via
    # `safeExec_bind_reta`, reduce the `match`/iota).
    arm_args = " ".join(input_group + [n for n, _ in arm.any_binds])
    proof = (
        "Proof.\n"
        "  intros.\n"
        "  match goal with H : safeExec _ _ _ |- _ => rename H into Hexec end.\n"
        f"  apply {select_name} in Hexec; [ | assumption ].\n"
        f"  eapply safeExec_bind_reta with (a := {arm_ret}) in Hexec.\n"
        f"  2:{{ apply ({arm_lemname} {arm_args}); assumption. }}\n"
        "  cbv beta iota in Hexec. exact Hexec.\n"
        "Qed."
    )
    return (
        f"Lemma {name} :\n"
        f"  {forall_in}"
        f"{hyps}"
        f"  forall X,\n"
        f"    safeExec (@ATrue unit) ({lb.name} {tup}) X ->\n"
        f"    safeExec (@ATrue unit) ({fused_rhs}) X.\n"
        f"{proof}"
    )


def _loop_body_lemmas(lib_text: str, entries: list) -> Tuple[List[str], dict]:
    """Emit the layer-1 select + layer-2 fused lemmas for every collected
    loop-body arm.  *entries* are ``(hole, input_group, arm, arm_lemname)`` for
    holes matching ``…_M_loop_M{1,2}``."""
    stats = {"select": 0, "selectcont": 0, "fused": 0, "fused_skipped_call": 0}
    loop_bodies = _parse_loop_bodies(lib_text)

    # ---- Layer 1: a select lemma per branch of *every* loop body ----
    # Emitted for all loops, not just those with a collected arm — a nested
    # (forest) function's *outer* loop (`M_loop1`) selects into `M_loop1_M2`
    # (itself the `to_inner`+inner-loop+`after_inner` composite, so never a
    # collected VC hole), yet its whole-function proof still needs to pick the
    # branch.  `select_names[(stem, mk)]` lets layer 2 reference these.
    out: List[str] = []
    select_names: dict = {}
    for lb in loop_bodies.values():
        for br in lb.branches:
            sel_text, sel_name = _select_lemma(lb, br)
            out.append(sel_text)
            stats["select"] += 1
            select_names[(lb.stem, br.mk)] = (lb, br, sel_name)
            # Continuation-form (match-wrapped) select: reduces one repeat_break
            # step to the selected branch in a single apply.  Handles both simple
            # loops (bare continue/break) and early-return loops (match arm) —
            # see `_selectcont_lemma`.
            sc_text, _ = _selectcont_lemma(lb, br, sel_name)
            out.append(sc_text)
            stats["selectcont"] += 1

    # ---- Layer 2: fused lemma per collected loop-body arm (call-free only) ----
    groups: dict = {}
    for hole, ig, arm, lemname in entries:
        m = _LOOP_MK_RE.match(hole.name)
        if m:
            groups.setdefault((m.group(1), m.group(2)), []).append((hole, ig, arm, lemname))
    for (stem, mk), grp in groups.items():
        sel = select_names.get((stem, mk))
        if sel is None:
            continue
        lb, br, sel_name = sel
        for hole, ig, arm, lemname in grp:
            # A *call-bearing* arm's lemma is stated over the call→`return r_ret`
            # *inlined* body, not over `M_loop_M{k} (tuple)`, so it is not the
            # `c1 ⊑ ret a` premise `safeExec_bind_reta` needs — the fused step for
            # it must go through the callee's own segment lemma at whole-function
            # assembly (P6), not here.  The layer-1 select is still emitted above.
            if arm.calls:
                _warn(f"loop-body fused lemma skipped for '{arm.vc_name}': "
                      f"call-bearing arm composes via the callee at assembly, not here")
                stats["fused_skipped_call"] += 1
                continue
            out.append(_fused_lemma(lb, br, sel_name, hole, ig, arm, lemname, lib_text))
            stats["fused"] += 1
    return out, stats


_LOOPBODY_HEADER = ("(* ---- Loop-body branch-selection lemmas: layer 1 (bare + "
                    "continuation-form select) + layer 2 (fused) ---- *)")


def render_seg_lemmas(header: str, collected: list, lib_text: str,
                      sibling_texts: Optional[List[str]] = None) -> Tuple[str, dict]:
    """Build the ``_seg_lemmas.v`` text from the collected ``(hole, input_group,
    arms)`` tuples.  *header* is the file preamble (monad imports + the filled
    lib import); *lib_text* is the filled lib (for ``MretTy`` alias resolution);
    *sibling_texts* are peer ``*_rel_lib.v`` bodies (for resolving a callee's
    ``_M`` result type).  Returns ``(text, stats)`` with per-outcome counts."""
    texts = [lib_text] + list(sibling_texts or [])
    lemmas: List[str] = []
    loopbody_entries: list = []           # (hole, input_group, arm, lemname) for M_loop_M*
    stats = {"emitted": 0, "emitted_call": 0, "skipped_calls": 0,
             "select": 0, "selectcont": 0, "fused": 0}
    for hole, input_group, arm_specs in collected:
        for idx, (vc, fcs, out_group, wrap) in enumerate(arm_specs):
            arm = _arm_view(vc, fcs, input_group, out_group, hole.curried, wrap)
            text = _lemma(hole, input_group, arm, idx, lib_text, texts)
            if text is None:                            # callee type unresolved -> skip
                stats["skipped_calls"] += 1
                continue
            lemmas.append(text)
            stats["emitted_call" if arm.calls else "emitted"] += 1
            if _LOOP_MK_RE.match(hole.name):            # a loop-body arm -> needs selection
                lemname = "seg_" + (_sanitize(arm.vc_name) if arm.vc_name
                                    else f"{hole.name}_arm{idx}")
                loopbody_entries.append((hole, input_group, arm, lemname))
    body = "\n\n".join(lemmas)
    out = f"{header}\n{_PROOF_PRELUDE}\n\n{_LEMMA_HEADER}\n\n{body}\n"
    lb_lemmas, lb_stats = _loop_body_lemmas(lib_text, loopbody_entries)
    stats["select"], stats["fused"] = lb_stats["select"], lb_stats["fused"]
    stats["selectcont"] = lb_stats["selectcont"]
    if lb_lemmas:
        out += f"\n{_LOOPBODY_HEADER}\n\n" + "\n\n".join(lb_lemmas) + "\n"
    return out, stats


def build_seg_lemmas(template_text: str, autovc_text: str, lib_module: str,
                     monad: str = "staterel",
                     libs_dir: Optional[str] = None) -> Tuple[str, dict]:
    """Generate the segment-lemma file text for a template + autovc pair.

    *lib_module* is the dotted logical name of the already-filled lib to import
    (e.g. ``LLM4PV.benchgen.glibc_slist.libs.glibc_slist_copy_rel_lib``).
    *libs_dir*, when given, holds the sibling ``*_rel_lib.v`` files consulted to
    resolve a callee's result type.  Runs :func:`fill_template` with the
    ``collect`` hook to recover the exact arms used, then renders the lemmas.
    """
    import glob
    import os
    from ..gen_rel_lib import coq_imports
    collected: list = []
    filled = fill_template(template_text, autovc_text, collect=collected)
    sibling_texts: List[str] = []
    if libs_dir:
        for p in sorted(glob.glob(os.path.join(libs_dir, "*_rel_lib.v"))):
            try:
                sibling_texts.append(open(p, encoding="utf-8").read())
            except OSError:
                pass
    header = f"{coq_imports(monad)}\nRequire Import Coq.micromega.Lia.\nRequire Import {lib_module}.\n"
    return render_seg_lemmas(header, collected, filled, sibling_texts)
