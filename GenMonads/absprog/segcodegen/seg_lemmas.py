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
from typing import List, Optional, Tuple

from . import fill_template
from .synth import ArmParts, synth_arms
from .template import Hole, _arg_type


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
        segs = _split_top(head, "->")
        return [segs[i] for i in range(len(binder_vars))]
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


_LEMMA_HEADER = "(* ---- Per-segment safeExec refinement lemmas (statements; P0-P1) ---- *)"


def _sanitize(name: str) -> str:
    return re.sub(r"[^A-Za-z0-9_']", "_", name)


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


def _call_subst(arm: ArmParts, texts: List[str], taken: set):
    """For a call-bearing arm, plan the ``r <- callee_M args`` → ``r <- return
    r_ret`` rewrite: allocate a forall-bound ``*_ret`` existential per callee
    result (typed by the callee's ``_M`` result type), and map each call-result
    name to it.  Returns ``(line_rewrites, ret_binders, name_map)`` or ``None`` if
    a callee result type can't be resolved (arm skipped)."""
    line_rewrites: List[Tuple[str, str]] = []       # (original bind line, replacement)
    ret_binders: List[str] = []                     # `(r_ret : T)` forall binders
    name_map: dict = {}                             # call-result name -> r_ret var
    for results, callee, args in arm.calls:
        R = _callee_result_type(callee, texts)
        if R is None:
            return None
        argstr = " ".join(args)
        if len(results) == 1:
            orig = f"{results[0]} <- {callee}_M {argstr};;"
            rv = _fresh(results[0] + "_ret", taken)
            ret_binders.append(f"({rv} : {R})")
            name_map[results[0]] = rv
            line_rewrites.append((orig, f"{results[0]} <- return {rv};;"))
        else:                                        # multi-result: one r_ret per component
            pat = "'(" + ", ".join(results) + ")"
            orig = f"{pat} <- {callee}_M {argstr};;"
            comps = _tuple_components(R)
            rvs = []
            for res, cty in zip(results, comps):
                rv = _fresh(res + "_ret", taken)
                ret_binders.append(f"({rv} : {cty})")
                name_map[res] = rv
                rvs.append(rv)
            line_rewrites.append((orig, f"{pat} <- return ({', '.join(rvs)});;"))
    return line_rewrites, ret_binders, name_map


def _lemma(hole: Hole, input_group: List[str], arm: ArmParts, idx: int,
           lib_text: str, texts: List[str]) -> Optional[str]:
    """Render one arm's refinement lemma.  A **call-free** arm refines
    ``return <output>`` directly from the segment Definition.  A **call-bearing**
    arm's segment is ``… r <- callee_M args;; …``; since the callee result is an
    existential on both sides, we substitute the call with ``r <- return r_ret``
    (``r_ret`` a fresh forall-bound existential at the callee's result type) — the
    lemma then certifies that surrounding computation refines ``return <output>``
    over ``r_ret``.  Returns ``None`` if a callee type can't be resolved."""
    vc_name = getattr(arm, "_vc_name", "") or ""
    lemname = "seg_" + (_sanitize(vc_name) if vc_name else f"{hole.name}_arm{idx}")

    binders = [f"({v} : {ty})"
               for v, ty in zip(input_group, _input_types(hole, input_group, lib_text))]
    binders += [f"({name} : {ty})" for name, ty in arm.any_binds]

    if not arm.calls:                                # call-free: LHS is `SEG inputs`
        lhs = _seg_app(hole, input_group)
        ret, hyps_src = arm.ret, arm.guards
    else:                                            # call-bearing: substitute the call
        taken = set(input_group) | {n for n, _ in arm.any_binds} \
            | {r for res, _, _ in arm.calls for r in res}
        plan = _call_subst(arm, texts, taken)
        if plan is None:
            return None
        line_rewrites, ret_binders, name_map = plan
        binds = list(arm.binds)
        for orig, repl in line_rewrites:
            binds = [repl if b == orig else b for b in binds]
        # LHS: the inlined body (call → return r_ret); r stays local, bound by the
        # return.  RHS/hyps reference the forall-bound r_ret instead.
        lhs = "(" + "\n     ".join(binds + [arm.ret]) + ")"
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
        f"Proof. Admitted."
    )


def render_seg_lemmas(header: str, collected: list, lib_text: str,
                      sibling_texts: Optional[List[str]] = None) -> Tuple[str, dict]:
    """Build the ``_seg_lemmas.v`` text from the collected ``(hole, input_group,
    arms)`` tuples.  *header* is the file preamble (monad imports + the filled
    lib import); *lib_text* is the filled lib (for ``MretTy`` alias resolution);
    *sibling_texts* are peer ``*_rel_lib.v`` bodies (for resolving a callee's
    ``_M`` result type).  Returns ``(text, stats)`` with per-outcome counts."""
    texts = [lib_text] + list(sibling_texts or [])
    lemmas: List[str] = []
    stats = {"emitted": 0, "emitted_call": 0, "skipped_calls": 0}
    for hole, input_group, arm_specs in collected:
        parts = synth_arms(arm_specs, input_group, curried=hole.curried)
        for idx, (arm, (vc, *_rest)) in enumerate(zip(parts, arm_specs)):
            arm._vc_name = getattr(vc, "name", "")      # label the lemma by its wit
            text = _lemma(hole, input_group, arm, idx, lib_text, texts)
            if text is None:                            # callee type unresolved -> skip
                stats["skipped_calls"] += 1
                continue
            lemmas.append(text)
            stats["emitted_call" if arm.calls else "emitted"] += 1
    body = "\n\n".join(lemmas)
    return f"{header}\n{_LEMMA_HEADER}\n\n{body}\n", stats


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
    header = f"{coq_imports(monad)}\nRequire Import {lib_module}.\n"
    return render_seg_lemmas(header, collected, filled, sibling_texts)
