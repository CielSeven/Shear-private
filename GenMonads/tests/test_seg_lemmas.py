"""Unit tests for the segment-refinement-lemma generator (``seg_lemmas``) and the
structured ``Bind`` contract it relies on (``synth.synth_arm``).

These tests are deliberately **self-contained**: every input is built in-code
from the plain ``VCBlock`` / ``Mapping`` / ``Hole`` / ``Bind`` dataclasses, and
every assertion is over returned Python strings/objects.  Nothing here reads a
project file, an ``autovc``, or a ``_rel_lib.v``, and nothing invokes Rocq — so
the suite runs anywhere in milliseconds and pins the generator's behaviour
independently of the benchmark corpus.
"""

import re

import pytest

from GenMonads.absprog.segcodegen import seg_lemmas as L
from GenMonads.absprog.segcodegen import synth as S
from GenMonads.absprog.segcodegen.template import Hole
from GenMonads.absprog.segcodegen.vcparse import Mapping, VCBlock


def _norm(s: str) -> str:
    return re.sub(r"\s+", " ", s).strip()


def _hole(name, ty, arity=1, role="normal") -> Hole:
    return Hole(name=name, type_str=ty, role=role, raw="", input_arity=arity)


# ---- canonical in-code arms -------------------------------------------------
# A `rev`/`iter`-style body: `l1 = x :: l1'` guard, output `x :: l1'`.  Exercises
# the `any` + `assume` binds.
def _destructure_vc(name="rev_body") -> VCBlock:
    vc = VCBlock(name=name, kind="entail")
    vc.exist_mapping = [Mapping("l2_1", "cons(Z, x_1, l1p_1)")]
    vc.leftover_props = ["l1_5 == cons(Z, x_1, l1p_1)"]
    return vc


# A pure disequality guard: `l1 <> nil`, identity output.
def _pure_guard_vc(name="tail_body") -> VCBlock:
    vc = VCBlock(name=name, kind="entail")
    vc.exist_mapping = [Mapping("l2_1", "l1_5")]
    vc.leftover_props = ["l1_5 != nil(Z)"]
    return vc


# A multi-result call `'(r, r0) <- g_M l1`, output `r ++ (r0 :: nil)`.
def _call_vc(name="use_g"):
    fc = VCBlock(name="f_funccall_wit_1", kind="funccall", call_target="g")
    fc.post_exists = ["p_1", "e_2"]
    fc.with_instantiation = {"a_1": "l1_9"}
    vc = VCBlock(name=name, kind="return")
    vc.exist_mapping = [Mapping("l2_1", "app(Z, p_1, cons(Z, e_2, nil(Z)))")]
    return vc, fc


# =============================================================================
# synth.Bind — structure captured at emit time (source of truth for readers)
# =============================================================================

def test_synth_parts_is_faithful_text_view_of_synth_arm():
    """`synth_parts` must be exactly the `.text` projection of `synth_arm`."""
    vc = _destructure_vc()
    binder_a, binds_a, ret_a = S.synth_arm(vc, [], ["l1"], ["l2"])
    binder_s, binds_s, ret_s = S.synth_parts(vc, [], ["l1"], ["l2"])
    assert (binder_a, ret_a) == (binder_s, ret_s)
    assert [b.text for b in binds_a] == binds_s


def test_bind_any_and_assume_fields():
    _b, binds, _r = S.synth_arm(_destructure_vc(), [], ["l1"], ["l2"])
    anys = [b for b in binds if b.kind == "any"]
    assumes = [b for b in binds if b.kind == "assume"]
    assert [(b.var, b.ty) for b in anys] == [("x", "Z"), ("l1'", "list Z")]
    assert len(assumes) == 1
    g = assumes[0]
    assert (g.lhs, g.rel, g.rhs) == ("l1", "=", "x :: l1'")
    assert g.prop == "l1 = x :: l1'"            # reconstructed, matches the text
    assert g.text == "assume!! (l1 = x :: l1');;"


def test_bind_pure_guard_is_disequality():
    _b, binds, _r = S.synth_arm(_pure_guard_vc(), [], ["l1"], ["l2"])
    assert len(binds) == 1 and binds[0].kind == "assume"
    assert binds[0].rel == "<>" and binds[0].prop == "l1 <> nil"


def test_bind_call_fields_multi_result():
    vc, fc = _call_vc()
    _b, binds, ret = S.synth_arm(vc, [fc], ["l1"], ["l2"])
    calls = [b for b in binds if b.kind == "call"]
    assert len(calls) == 1
    assert calls[0].callee == "g" and calls[0].results == ("r", "r0")
    assert calls[0].text == "'(r, r0) <- g_M l1;;"
    assert _norm(ret) == "return (r ++ (r0 :: nil))"


def test_synth_recursive_reads_bind_structure_not_regex():
    """The migrated `_match_branch` reads `Bind` fields; a `nil`/`cons` split
    must yield the two match patterns with their bodies."""
    vc_nil = VCBlock(name="rev_nil", kind="entail")
    vc_nil.exist_mapping = [Mapping("l2_1", "nil(Z)")]
    vc_nil.leftover_props = ["l1_5 == nil(Z)"]
    body = S.synth_recursive(
        [(vc_nil, [], ["l2"], None), (_destructure_vc("rev_cons"), [], ["l2"], None)],
        "l1")
    assert "match l1 with" in body
    assert "| nil => return nil" in body
    assert "| x :: l1' =>" in body


# =============================================================================
# seg_lemmas._arm_view — deriving the structured view for the emitter
# =============================================================================

def test_arm_view_derives_any_guards_calls():
    arm = L._arm_view(_destructure_vc(), [], ["l1"], ["l2"], False, None)
    assert arm.any_binds == [("x", "Z"), ("l1'", "list Z")]
    assert arm.guards == ["l1 = x :: l1'"]
    assert arm.calls == []
    assert arm.vc_name == "rev_body"

    vc, fc = _call_vc()
    carm = L._arm_view(vc, [fc], ["l1"], ["l2"], False, None)
    assert carm.calls == [(("r", "r0"), "g")]
    assert carm.any_binds == [] and carm.guards == []


# =============================================================================
# seg_lemmas._call_subst — call → `return r_ret` inlining (finding #2 payoff)
# =============================================================================

def _call_arm(bind, ret, calls, name="a"):
    return L._Arm(binder_vars=["l1"], curried=False, bind_objs=[bind], ret=ret,
                  calls=calls, vc_name=name)


def test_call_subst_single_result_reads_bind_not_string():
    bind = S.Bind("r <- h_M l1;;", "call", results=("r",), callee="h")
    arm = _call_arm(bind, "return r", [(("r",), "h")], "use_h")
    sib = "Parameter h_M : list Z -> MONAD (list Z)."
    lhs_lines, ret_binders, name_map = L._call_subst(arm, ["", sib], {"l1", "r"})
    assert lhs_lines == ["r <- return r_ret;;"]
    assert name_map == {"r": "r_ret"}
    assert len(ret_binders) == 1 and "list Z" in ret_binders[0] and "r_ret" in ret_binders[0]


def test_call_subst_multi_result_typed_by_tuple_components():
    bind = S.Bind("'(r, r0) <- g_M l1;;", "call", results=("r", "r0"), callee="g")
    arm = _call_arm(bind, "return (r ++ (r0 :: nil))", [(("r", "r0"), "g")], "use_g")
    sib = "Definition g_M : list Z -> MONAD (list Z * Z) := fun l => tt."
    lhs_lines, ret_binders, name_map = L._call_subst(arm, ["", sib], {"l1", "r", "r0"})
    assert lhs_lines == ["'(r, r0) <- return (r_ret, r0_ret);;"]
    assert name_map == {"r": "r_ret", "r0": "r0_ret"}
    assert ret_binders == ["(r_ret : list Z)", "(r0_ret : Z)"]     # component types


def test_call_subst_unresolved_callee_returns_none_and_warns(capsys):
    """Finding #3: an unresolvable callee drops the obligation — it must warn,
    never silently vanish."""
    bind = S.Bind("r <- mystery_M l1;;", "call", results=("r",), callee="mystery")
    arm = _call_arm(bind, "return r", [(("r",), "mystery")], "seg_demo")
    assert L._call_subst(arm, ["(* no mystery_M here *)"], {"l1", "r"}) is None
    err = capsys.readouterr().err
    assert "[seg_lemmas] WARN" in err
    assert "mystery_M" in err and "seg_demo" in err


# =============================================================================
# seg_lemmas._lemma — full lemma-statement rendering
# =============================================================================

def test_lemma_call_free_statement_and_proof():
    hole = _hole("f_M_loop_M2", "list Z -> MONAD (list Z)", role="M2")
    arm = L._arm_view(_destructure_vc(), [], ["l1"], ["l2"], False, None)
    text = L._lemma(hole, ["l1"], arm, 0, lib_text="", texts=[""])
    assert text.startswith("Lemma seg_rev_body :")
    assert "forall (l1 : list Z) (x : Z) (l1' : list Z)," in text
    assert "l1 = x :: l1' ->" in text                       # guard hypothesis
    assert "safeExec (@ATrue unit) (f_M_loop_M2 l1) X ->" in text
    assert "safeExec (@ATrue unit) (return (x :: l1')) X." in text
    # call-free -> `unfold`; has `any` -> no `subst`
    assert "unfold f_M_loop_M2 in *;" in text
    assert "subst;" not in text
    assert text.rstrip().endswith("seg_grab. Qed.")


def test_lemma_call_bearing_inlines_call_over_forall_ret():
    hole = _hole("f_M", "list Z -> MONAD (list Z)", role="M")
    vc, fc = _call_vc()
    arm = L._arm_view(vc, [fc], ["l1"], ["l2"], False, None)
    sib = "Definition g_M : list Z -> MONAD (list Z * Z) := fun l => tt."
    text = L._lemma(hole, ["l1"], arm, 0, lib_text="", texts=["", sib])
    # the call is inlined: `g_M` gone, results become forall-bound r_ret existentials
    assert "g_M" not in text
    assert "(r_ret : list Z) (r0_ret : Z)" in text
    assert "'(r, r0) <- return (r_ret, r0_ret);;" in text
    assert "safeExec (@ATrue unit) (return (r_ret ++ (r0_ret :: nil))) X." in text
    # call-bearing -> no `unfold`; no `any` -> `subst`
    assert "unfold" not in text
    assert "subst;" in text


@pytest.mark.parametrize("any_binds,calls,want_subst,want_unfold", [
    ([], [], True, True),                          # no-any, call-free
    ([("x", "Z")], [], False, True),               # any,    call-free
    ([], [(("r",), "h")], True, False),            # no-any, call-bearing
    ([("x", "Z")], [(("r",), "h")], False, False),  # any,    call-bearing
])
def test_proof_switches(any_binds, calls, want_subst, want_unfold):
    hole = _hole("SEG", "list Z -> MONAD (list Z)")
    arm = L._Arm(binder_vars=["l1"], curried=False, bind_objs=[], ret="return l1",
                 any_binds=list(any_binds), calls=list(calls), vc_name="x")
    proof = L._proof(hole, arm)
    assert ("subst;" in proof) is want_subst
    assert ("unfold SEG in *;" in proof) is want_unfold
    assert proof.endswith("seg_grab. Qed.")


# =============================================================================
# seg_lemmas._input_types — hole-type reading, incl. finding #5 (soft-fail)
# =============================================================================

def test_input_types_curried_exact_is_silent(capsys):
    h = _hole("h", "list Z -> Z -> MONAD (list Z)", arity=2)
    assert L._input_types(h, ["a", "b"], "") == ["list Z", "Z"]
    assert L._input_types(h, ["a"], "") == ["list Z"]          # fewer binders: truncates
    assert capsys.readouterr().err == ""                        # well-formed -> no warning


def test_input_types_curried_malformed_pads_and_warns(capsys):
    """Finding #5: more binders than arrow-arg types must warn + pad, not crash."""
    h = _hole("h", "list Z -> Z -> MONAD R", arity=3)
    assert L._input_types(h, ["a", "b", "c"], "") == ["list Z", "Z", "Type"]
    err = capsys.readouterr().err
    assert "[seg_lemmas] WARN" in err and "'h'" in err


def test_input_types_tupled_resolves_mretty_alias():
    h = _hole("f_M_loop_end", "f_MretTy -> MONAD (list Z)", arity=1, role="end")
    lib = "Definition f_MretTy : Type := (list Z * list Z * Z).\n"
    assert L._input_types(h, ["a", "b", "c"], lib) == ["list Z", "list Z", "Z"]


# =============================================================================
# seg_lemmas.render_seg_lemmas — file assembly, prelude, stats, skip accounting
# =============================================================================

def test_render_includes_header_prelude_and_lemma():
    hole = _hole("f_M_loop_M2", "list Z -> MONAD (list Z)", role="M2")
    collected = [(hole, ["l1"], [(_destructure_vc(), [], ["l2"], None)])]
    text, stats = L.render_seg_lemmas("(* MY HEADER *)", collected, lib_text="",
                                      sibling_texts=[])
    assert "(* MY HEADER *)" in text
    assert "Ltac seg_solve" in text and "Ltac seg_grab" in text     # proof prelude
    assert L._LEMMA_HEADER in text
    assert "Lemma seg_rev_body :" in text
    assert stats == {"emitted": 1, "emitted_call": 0, "skipped_calls": 0,
                     "select": 0, "selectcont": 0, "fused": 0}


def test_render_skips_unresolved_call_and_accounts_for_it(capsys):
    """A call arm whose callee can't be resolved is skipped from the file, but
    that loss is counted *and* announced (findings #2/#3)."""
    hole = _hole("f_M", "list Z -> MONAD (list Z)", role="M")
    vc, fc = _call_vc()
    collected = [(hole, ["l1"], [(vc, [fc], ["l2"], None)])]
    text, stats = L.render_seg_lemmas("(* H *)", collected, lib_text="",
                                      sibling_texts=[])            # no g_M anywhere
    assert stats["skipped_calls"] == 1 and stats["emitted_call"] == 0
    assert "seg_use_g" not in text
    assert "[seg_lemmas] WARN" in capsys.readouterr().err


# =============================================================================
# loop-body branch-selection (layer 1) + fused (layer 2)
# =============================================================================

_LIB_SIMPLE = """
Definition f_M_loop_body : (list Z * list Z) -> MONAD (CntOrBrk (list Z * list Z) MretTy) :=
  fun a =>
    choice (assume!! (~ (f_guardP a));; r <- f_M_loop_M1 a ;; break r)
           (assume!! ((f_guardP a));; a' <- f_M_loop_M2 a ;; continue a').
Definition f_M_loop_aux := repeat_break f_M_loop_body.
"""

_LIB_MATCH = """
Definition g_M_loop_body : (list Z * list Z * list Z) -> MONAD (CntOrBrk (list Z * list Z * list Z) (early_result MretTy (list Z))) :=
  fun a =>
    choice (assume!! (~ (g_guardP a));; r <- g_M_loop_M1 a ;; break (Continue r))
           (assume!! ((g_guardP a));;
            a' <- g_M_loop_M2 a ;;
            match a' with
            | Continue a'' => continue a''
            | ReturnNow r' => break (ReturnNow r')
            end).
  repeat_break g_M_loop_body.
"""


def test_parse_loop_bodies_simple_shape():
    lb = L._parse_loop_bodies(_LIB_SIMPLE)["f_M_loop_body"]
    assert lb.state_ty == "(list Z * list Z)" and lb.stem == "f_M_loop"
    br = {b.mk: b for b in lb.branches}
    assert set(br) == {"M1", "M2"}
    assert br["M2"].guard == "(f_guardP a)"
    assert br["M1"].guard == "~ (f_guardP a)"
    assert br["M2"].cont == "continue a'"
    assert "f_M_loop_M2 a" in br["M2"].body


def test_parse_loop_bodies_match_shape():
    lb = L._parse_loop_bodies(_LIB_MATCH)["g_M_loop_body"]
    m2 = next(b for b in lb.branches if b.mk == "M2")
    assert m2.cont.startswith("match a' with") and m2.cont.endswith("end")


def test_branch_guard_complementarity_check(capsys):
    """Well-formed `G`/`~G` guards parse silently; a non-complementary pair
    (unexpected skeleton shape) is warned about, not silently accepted."""
    assert L._guard_core("~ (f_guardP a)") == (True, "f_guardP a")
    assert L._guard_core("(f_guardP a)") == (False, "f_guardP a")
    L._parse_loop_bodies(_LIB_SIMPLE)                       # complementary
    assert "WARN" not in capsys.readouterr().err
    bad = _LIB_SIMPLE.replace("~ (f_guardP a)", "(other_guard a)")
    L._parse_loop_bodies(bad)                               # G vs unrelated
    assert "not the expected complementary" in capsys.readouterr().err


_LIB_SWAPPED = """
Definition f_M_loop_body : (list Z) -> MONAD (CntOrBrk (list Z) MretTy) :=
  fun a =>
    choice (assume!! ((f_guardP a));; a' <- f_M_loop_M2 a ;; continue a')
           (assume!! (~ (f_guardP a));; r <- f_M_loop_M1 a ;; break r).
Definition f_M_loop_aux := repeat_break f_M_loop_body.
"""


def test_select_side_tracks_operand_position_not_mk():
    """Branch order is handled by construction: with the `choice` operands
    swapped, the continue branch (M2) sits at position 0 and still selects
    `choice_l` — so `side` needs no guard-polarity derivation."""
    lb = L._parse_loop_bodies(_LIB_SWAPPED)["f_M_loop_body"]
    m2 = next(b for b in lb.branches if b.mk == "M2")
    assert m2.side == "l"                                   # M2 now the left operand
    text, _ = L._select_lemma(lb, m2)
    assert "apply safeExec_choice_l in H." in text          # selects the M2 operand


def test_parse_loop_bodies_forest_indexed():
    """Multi-loop (forest) bodies `_M_loop{k}_body` with `_M_loop{k}_M{j}` arms."""
    lib = _LIB_SIMPLE.replace("f_M_loop", "h_M_loop2")   # h_M_loop2_body / _M_loop2_M2
    lb = L._parse_loop_bodies(lib)["h_M_loop2_body"]
    assert lb.stem == "h_M_loop2"
    m2 = next(b for b in lb.branches if b.mk == "M2")
    assert "h_M_loop2_M2 a" in m2.body


@pytest.mark.parametrize("cont,ret,want", [
    ("continue a'", "(l1, l2)", "continue ((l1, l2))"),
    ("match a' with C => _ end", "Continue ((l1, l2))", "continue ((l1, l2))"),
    ("match a' with C => _ end", "ReturnNow (l3)", "break (ReturnNow (l3))"),
])
def test_reduce_cont(cont, ret, want):
    assert L._reduce_cont(cont, ret) == want


def test_select_lemma_abstract_in_a():
    lb = L._parse_loop_bodies(_LIB_SIMPLE)["f_M_loop_body"]
    m2 = next(b for b in lb.branches if b.mk == "M2")
    text, name = L._select_lemma(lb, m2)
    assert name == "seg_f_M_loop_select_M2"
    assert "forall (a : (list Z * list Z))," in text
    assert "(f_guardP a) ->" in text
    assert "safeExec (@ATrue unit) (f_M_loop_body a) X ->" in text
    assert "safeExec (@ATrue unit) (a' <- f_M_loop_M2 a ;; continue a') X." in text
    # deterministic proof: M2 is the right choice branch, guard discharged by name
    assert "apply safeExec_choice_r in H." in text
    assert "apply safeExec_test_bind in H; [ exact H | exact Hg ]." in text


def _m2_arm(ret, wrap_reduced, guards):
    return L._Arm(
        binder_vars=["l1", "l2", "l3"], curried=False, bind_objs=[], ret=ret,
        any_binds=[("x", "Z"), ("l2'", "list Z"), ("l3'", "list Z")],
        guards=guards, calls=[], vc_name="g_entail_wit_2")


def test_fused_lemma_composition_and_explicit_binders():
    lb = L._parse_loop_bodies(_LIB_MATCH)["g_M_loop_body"]
    m2 = next(b for b in lb.branches if b.mk == "M2")
    hole = _hole("g_M_loop_M2",
                 "(list Z * list Z * list Z) -> MONAD (early_result (list Z * list Z * list Z) (list Z))")
    arm = _m2_arm("return Continue ((l1 ++ nil, l2', l3'))",
                  None, ["l2 = x :: l2'", "l3 = x0 :: l3'"])
    text = L._fused_lemma(lb, m2, "seg_g_loop_body_select_M2", hole,
                          ["l1", "l2", "l3"], arm, "seg_g_entail_wit_2", "")
    # guard instantiated at the tuple, body on M_loop_body, reduced Continue output
    assert "(g_guardP (l1, l2, l3)) ->" in text
    assert "safeExec (@ATrue unit) (g_M_loop_body (l1, l2, l3)) X ->" in text
    assert "safeExec (@ATrue unit) (continue ((l1 ++ nil, l2', l3'))) X." in text
    # composed via safeExec_bind_reta with the arm result, arm applied with EXPLICIT
    # binders (so guard-only vars like l2' are determined)
    assert "eapply safeExec_bind_reta with (a := Continue ((l1 ++ nil, l2', l3')))" in text
    assert "apply (seg_g_entail_wit_2 l1 l2 l3 x l2' l3')" in text


def test_loop_body_fused_skips_call_bearing(capsys):
    """A call-bearing loop arm gets layer-1 select but NO fused (its arm lemma is
    over the inlined body, not `M_loop_M2 a`) — skip is counted and warned."""
    hole = _hole("f_M_loop_M2", "(list Z * list Z) -> MONAD (list Z * list Z)")
    arm = L._Arm(binder_vars=["l1", "l2"], curried=False, bind_objs=[],
                 ret="return (l2, r)", any_binds=[], guards=[],
                 calls=[(("r",), "cb")], vc_name="f_entail_wit_2")
    entries = [(hole, ["l1", "l2"], arm, "seg_f_entail_wit_2")]
    out, stats = L._loop_body_lemmas(_LIB_SIMPLE, entries)
    # layer-1 select is emitted for *both* branches of the loop body (all loops),
    # independent of collected arms; the call-bearing fused is skipped + warned.
    assert stats == {"select": 2, "selectcont": 2,
                     "fused": 0, "fused_skipped_call": 1}
    assert any("select_M1" in t for t in out) and any("select_M2" in t for t in out)
    assert not any("loopbody_" in t for t in out)       # no fused
    assert "[seg_lemmas] WARN" in capsys.readouterr().err


def test_selectcont_emitted_for_simple_loop():
    """A simple loop gets a continuation-form (match-wrapped) select lemma per
    branch, derived from the bare select via `safeExec_bind_partial_target` and
    proved deterministically (remember + prog_nf, no `seg_grab`/`proequiv`)."""
    out, stats = L._loop_body_lemmas(_LIB_SIMPLE, [])
    assert stats["selectcont"] == 2
    sc = [t for t in out if "selectcont" in t]
    assert len(sc) == 2
    m2 = next(t for t in sc if "selectcont_M2" in t)
    # LHS wraps the loop body under the by_continue/by_break match; RHS is the
    # selected arm followed by the matching continuation (kc for M2's continue).
    assert "x <- f_M_loop_body a ;;" in m2
    assert "| by_continue a' => kc a'" in m2 and "| by_break r => kb r" in m2
    assert "a' <- f_M_loop_M2 a ;; kc a'" in m2
    assert "safeExec_bind_partial_target" in m2 and "remember (f_M_loop_M2 a)" in m2
    assert "seg_f_M_loop_select_M2" in m2       # references the bare select
    assert "proequiv" not in m2                 # prog_nf-only, per constraint
    m1 = next(t for t in sc if "selectcont_M1" in t)
    assert "r <- f_M_loop_M1 a ;; kb r" in m1   # break arm -> kb leaf


def test_selectcont_emitted_for_early_return(capsys):
    """An early-return loop body (branched `match a' with Continue|ReturnNow`) now
    gets a continuation-form select per branch too: the outer continuation is
    pushed into each match arm and the residual bind-over-match is closed by
    `destruct` + `bind_ret_l` (routed through `safeExec_proequiv`).  The
    normal-exit branch's wrapped `break (Continue r)` reduces to `kb (Continue
    r)`.  No skip, no WARN."""
    out, stats = L._loop_body_lemmas(_LIB_MATCH, [])
    assert stats["select"] == 2 and stats["selectcont"] == 2
    assert "selectcont_skipped_early" not in stats
    assert "[seg_lemmas] WARN" not in capsys.readouterr().err
    sc = [t for t in out if "selectcont" in t]
    assert len(sc) == 2
    # M1 (guard-false) normal exit: wrapped-break payload rides through `kb`.
    m1 = next(t for t in sc if "selectcont_M1" in t)
    assert "r <- g_M_loop_M1 a ;; kb (Continue r)" in m1
    assert "unfold break in H" in m1
    # M2 (guard-true) branched arm: match pushed through the continuation,
    # closed per-constructor by destruct + bind_ret_l via safeExec_proequiv.
    m2 = next(t for t in sc if "selectcont_M2" in t)
    assert "| Continue a'' => kc a''" in m2
    assert "| ReturnNow r' => kb (ReturnNow r')" in m2
    assert "eapply safeExec_proequiv" in m2 and "apply bind_equiv" in m2
    assert "destruct a' as [ a'' | r' ]" in m2


# =============================================================================
# pure string helpers
# =============================================================================

def test_split_top_respects_paren_depth():
    assert L._split_top("A -> (B -> C) -> D", "->") == ["A", "(B -> C)", "D"]
    assert L._split_top("list Z * (A * B) * Z", "*") == ["list Z", "(A * B)", "Z"]


def test_strip_outer_parens_only_when_whole_wrap():
    assert L._strip_outer_parens("((list Z))") == "(list Z)"
    assert L._strip_outer_parens("(A) * (B)") == "(A) * (B)"     # opener closes early


def test_tuple_components_peels_redundant_parens():
    assert L._tuple_components("((list Z * Z))") == ["list Z", "Z"]
    assert L._tuple_components("list Z") == ["list Z"]


@pytest.mark.parametrize("decl,want", [
    ("Definition g_M : list Z -> MONAD (list Z * Z) := fun l => tt.", "(list Z * Z)"),
    ("Parameter h_M : list Z -> MONAD (list Z).", "(list Z)"),
    ("Fixpoint k_M (l : list Z) : MONAD (list Z) := tt.", "(list Z)"),
])
def test_callee_result_type_across_decl_forms(decl, want):
    assert L._callee_result_type(decl.split("_M")[0].split()[-1], [decl]) == want


def test_callee_result_type_absent_is_none():
    assert L._callee_result_type("nope", ["Definition other_M : MONAD unit := tt."]) is None


def test_subst_vars_is_whole_word():
    # `r` maps to `r_ret`, but `r0` and `re` must not be touched
    assert L._subst_vars("r ++ (r0 :: re)", {"r": "r_ret"}) == "r_ret ++ (r0 :: re)"


def test_fresh_avoids_collisions():
    taken = {"r_ret"}
    assert L._fresh("r_ret", taken) == "r_ret'"
    assert L._fresh("r_ret", taken) == "r_ret''"
