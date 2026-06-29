"""Tests for ``GenMonads.assertgen``.

End-to-end: roll the sum_list tutorial lib back to its pre-edit state, run the
deterministic inserter, and assert the verifier reports ``ok``.

We don't run ``coqc`` from the unit tests (depends on the user's Rocq install);
that's covered by the manual run-book in the plan. We *do* check the structural
gate — assert-only + soundness-lemma present.
"""

from __future__ import annotations

import json
import os
import shutil

import pytest

from GenMonads.assertgen.insert import run as run_assertgen


REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
TUTORIAL = os.path.join(REPO_ROOT, ".codex", "skills",
                        "abstract-program-assert", "tutorial", "sum_list")


def _strip_to_pre_edit(src_path: str, dst_path: str) -> None:
    """Drop the inserted assert line and the trailing soundness section."""
    out = []
    with open(src_path, "r", encoding="utf-8") as f:
        for ln in f.read().splitlines():
            if "assert (-2147483648 <= s + x <= 2147483647);;" in ln:
                continue
            stripped = ln.lstrip()
            if (
                stripped.startswith("Definition sum_acc_inv")
                or stripped.startswith("Lemma sum_")
            ):
                break
            out.append(ln)
    with open(dst_path, "w", encoding="utf-8") as f:
        f.write("\n".join(out) + "\n")


def _make_digest(dst_path: str) -> None:
    """Mimic what ``extract_unproved_goals.py`` produces for sum_list_safety_wit_2.

    Shape is taken verbatim from the real extractor output so the regex paths
    inside the pattern are exercised against real text.
    """
    digest = {
        "base": "sum_list",
        "range_predicates": ["sum_list_range"],
        "unproved_count": 1,
        "unproved_source": "manual:Admitted",
        "extern_coq_programs": ["sum_list_M", "sum_list_M_loop",
                                "sum_list_M_loop_end"],
        "function_require": "",
        "goals": [
            {
                "name": "sum_list_safety_wit_2",
                "proof_name": "proof_of_sum_list_safety_wit_2",
                "kind": "safety_wit",
                "statement": "...",
                "hypotheses_pure": [
                    "(l3 = (cons (x) (l0)))",
                    "(safeExec ATrue (bind ((sum_list_M_loop (l3) (sx))) (sum_list_M_loop_end)) X )",
                    "(l1 = (app (l2) (l3)))",
                    "(sum_list_range l1 )",
                    "(p <> 0)",
                ],
                "goal_pure": [
                    "((sx + x ) <= INT_MAX)",
                    "((INT_MIN) <= (sx + x ))",
                ],
                "safeExec_hypotheses": [
                    "(safeExec ATrue (bind ((sum_list_M_loop (l3) (sx))) (sum_list_M_loop_end)) X )",
                ],
                "abstract_programs_referenced": [
                    "sum_list_M_loop", "sum_list_M_loop_end",
                ],
                "range_predicates_in_goal": ["sum_list_range"],
            },
        ],
    }
    with open(dst_path, "w", encoding="utf-8") as f:
        json.dump(digest, f)


def test_assertgen_pop_pattern_end_to_end_on_sum_list(tmp_path):
    lib_pre = tmp_path / "sum_list_rel_lib.v"
    rel_c = tmp_path / "sum_list_rel.c"
    digest = tmp_path / "goals.json"

    _strip_to_pre_edit(
        os.path.join(TUTORIAL, "sum_list_rel_lib.v"),
        str(lib_pre),
    )
    shutil.copy2(os.path.join(TUTORIAL, "sum_list_rel.c"), str(rel_c))
    _make_digest(str(digest))

    rel_c_before = rel_c.read_text(encoding="utf-8")

    rep = run_assertgen(
        base="sum_list",
        rel_c_path=str(rel_c),
        lib_path=str(lib_pre),
        digest_path=str(digest),
        elem_lo=-1000,
        elem_hi=1000,
        len_bound=1000,
        coqc_cmd=None,   # structural gate only — no Coq dependency in CI
        edit_rel_c=True,
    )

    # Outcome.
    assert rep.status == "ok", f"unexpected status: {rep.status} — {rep.reason}"
    assert rep.verifier["assert_only_ok"] is True
    assert rep.verifier["soundness_lemma_ok"] is True
    assert rep.verifier["ok"] is True
    # Verifier ran without coqc, so compile_passed is left as None.
    assert rep.verifier["compile_passed"] is None

    # Pattern fired.
    assert rep.patterns_matched, "pop_accumulator should have matched"
    assert rep.patterns_matched[0]["pattern"] == "pop_accumulator"
    assert rep.patterns_matched[0]["fn"] == "sum_list"
    assert rep.patterns_matched[0]["target"] == "sum_list_M_loop_body"

    # Resulting lib has the assert inside M_loop_body.
    lib_after = lib_pre.read_text(encoding="utf-8")
    assert "assert (let '(rem, s) := a in" in lib_after
    assert "-2147483648 <= s + x <= 2147483647" in lib_after

    # Soundness lemmas appended with the existing range predicate name.
    assert "sum_list_acc_inv" in lib_after
    assert "Lemma sum_list_acc_inv_init" in lib_after
    assert "Lemma sum_list_acc_inv_step" in lib_after
    assert "Lemma sum_list_assert_holds" in lib_after
    assert "sum_list_range" in lib_after          # used by acc_inv_init
    # No fresh `Definition range` block — the spec already declared one.
    assert "Definition range " not in lib_after

    # rel.c unchanged because the existing range predicate already covers it.
    assert rel_c.read_text(encoding="utf-8") == rel_c_before


def test_assertgen_refuses_when_no_goals(tmp_path):
    lib = tmp_path / "lib.v"
    rel_c = tmp_path / "rel.c"
    digest = tmp_path / "goals.json"
    lib.write_text("Require Import Coq.ZArith.ZArith.\n", encoding="utf-8")
    rel_c.write_text("/*@ Extern Coq */\n", encoding="utf-8")
    digest.write_text(json.dumps({"base": "x", "goals": []}), encoding="utf-8")

    rep = run_assertgen(
        base="x",
        rel_c_path=str(rel_c),
        lib_path=str(lib),
        digest_path=str(digest),
        elem_lo=0, elem_hi=0, len_bound=0,
    )
    assert rep.status == "unsupported"
    assert "no unproved goals" in rep.reason


def test_assertgen_refuses_on_unrecognized_goal(tmp_path):
    """A wit whose RHS isn't a `(s + x)` overflow must be refused cleanly."""
    lib = tmp_path / "lib.v"
    rel_c = tmp_path / "rel.c"
    digest = tmp_path / "goals.json"
    lib.write_text("Require Import Coq.ZArith.ZArith.\n", encoding="utf-8")
    rel_c.write_text("/*@ Extern Coq */\n", encoding="utf-8")
    digest.write_text(json.dumps({
        "base": "weird",
        "goals": [{
            "name": "weird_safety_wit_1",
            "kind": "safety_wit",
            "statement": "...",
            "hypotheses_pure": [],
            "goal_pure": ["( 0 <= sortedness l )"],
            "safeExec_hypotheses": [],
            "abstract_programs_referenced": [],
            "range_predicates_in_goal": [],
        }],
    }), encoding="utf-8")

    rep = run_assertgen(
        base="weird",
        rel_c_path=str(rel_c),
        lib_path=str(lib),
        digest_path=str(digest),
        elem_lo=0, elem_hi=0, len_bound=0,
    )
    assert rep.status == "unsupported"
    assert "no registered pattern matched" in rep.reason
