"""Tests for the workdir-mode synthesis backend foundation.

Covers prepare_workdir + AGENTS.md template + pre-spawn checks
(:func:`check_prerequisites`) + Layer-2 file-system whitelist + Layer-3
strict skeleton diff.  The codex invocation itself is not exercised here —
that's the synthesize-side rewire (task #33) and gets exercised through
the higher-level pipeline tests.
"""

from __future__ import annotations

import os
import pytest

from GenMonads.absprog.workdir import (
    check_prerequisites,
    locate_coq_project,
    prepare_workdir,
    render_agents_md,
    required_callee_libs,
    snapshot_workdir,
    validate_attempt,
    validate_skeleton_diff,
    validate_workdir_filesystem,
)


# ---------------------------------------------------------------------------
# AGENTS.md template


class TestAgentsMdTemplate:
    def test_substitutes_basename(self):
        md = render_agents_md("list_tail")
        assert "list_tail_rel_lib.v" in md

    def test_leaves_generic_placeholders_literal(self):
        md = render_agents_md("demo")
        # Generic placeholders intended for the agent's reading must stay
        # as literal braces — escaping with ``{{...}}`` in the template.
        assert "{fn}_M_loop_M1" in md
        assert "{fn}_M_loop{k}_M1" in md
        assert "{fn}_M_loop{k}_to_inner_{c}" in md
        assert "{fn}_loop{k}_guardP" in md

    def test_contains_all_section_markers(self):
        md = render_agents_md("demo")
        for marker in [
            "## A2", "## A3", "## A4", "## A5", "## A6",
            "## A7", "## A8", "## A9", "## A10", "## A11", "## A12",
        ]:
            assert marker in md, f"missing section {marker!r} in AGENTS.md"

    def test_mentions_verification_command(self):
        md = render_agents_md("demo")
        assert "coqc -arg-file _CoqProject skeleton/demo_rel_lib.v" in md

    def test_mentions_file_system_contract(self):
        md = render_agents_md("demo")
        assert "Edit ONLY ``skeleton/demo_rel_lib.v``" in md
        assert "out/transcript.txt" in md

    def test_mentions_strict_replacement_contract(self):
        md = render_agents_md("demo")
        assert "post-run validator" in md
        assert "structural diff" in md
        assert "byte-identical" in md


# ---------------------------------------------------------------------------
# locate_coq_project + prepare_workdir


def _write(path, text):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        f.write(text)


def test_locate_coq_project_walks_upward(tmp_path):
    deep = tmp_path / "a" / "b" / "c"
    deep.mkdir(parents=True)
    cp = tmp_path / "_CoqProject"
    cp.write_text("-Q . MyLib\n", encoding="utf-8")
    found = locate_coq_project(str(deep))
    assert found == str(cp)


def test_locate_coq_project_returns_none_when_absent(tmp_path):
    deep = tmp_path / "no" / "project" / "here"
    deep.mkdir(parents=True)
    assert locate_coq_project(str(deep)) is None


class TestPrepareWorkdir:
    @pytest.fixture
    def cp(self, tmp_path):
        path = tmp_path / "_CoqProject"
        path.write_text("-Q . MyLib\n", encoding="utf-8")
        return path

    def test_lays_down_four_artifacts(self, tmp_path, cp):
        parent = tmp_path / "synth"
        parent.mkdir()
        paths = prepare_workdir(
            parent_dir=str(parent),
            basename="demo",
            skeleton_text="(* skeleton *)\nParameter MretTy : Type.\n",
            coq_project_src=str(cp),
        )
        assert os.path.isfile(paths["agents_md"])
        assert os.path.isfile(paths["skeleton_path"])
        assert os.path.exists(paths["coq_project"])
        assert os.path.isdir(paths["out_dir"])
        assert paths["transcript"].endswith("out/transcript.txt")
        # Skeleton contents match what we passed in.
        with open(paths["skeleton_path"]) as f:
            assert f.read() == "(* skeleton *)\nParameter MretTy : Type.\n"

    def test_coq_project_symlinks_when_possible(self, tmp_path, cp):
        parent = tmp_path / "synth"
        parent.mkdir()
        paths = prepare_workdir(
            parent_dir=str(parent),
            basename="demo",
            skeleton_text="",
            coq_project_src=str(cp),
        )
        # On macOS/Linux a symlink is used; readlink resolves to the source.
        if os.path.islink(paths["coq_project"]):
            assert os.readlink(paths["coq_project"]) == os.path.abspath(str(cp))
        else:
            # Filesystem disallowed symlinks → copy fallback.
            with open(paths["coq_project"]) as f:
                assert "MyLib" in f.read()

    def test_reset_idempotent_clears_out_dir(self, tmp_path, cp):
        parent = tmp_path / "synth"
        parent.mkdir()
        paths = prepare_workdir(
            parent_dir=str(parent), basename="demo",
            skeleton_text="v1", coq_project_src=str(cp),
        )
        # Drop a stale transcript from a "previous" run.
        with open(paths["transcript"], "w") as f:
            f.write("old transcript")
        # Re-prep with fresh skeleton — should reset out/ and skeleton.
        paths2 = prepare_workdir(
            parent_dir=str(parent), basename="demo",
            skeleton_text="v2", coq_project_src=str(cp),
        )
        assert paths2["workdir"] == paths["workdir"]
        # out/ has been cleared.
        assert not os.path.exists(paths2["transcript"])
        # Skeleton has the new content.
        with open(paths2["skeleton_path"]) as f:
            assert f.read() == "v2"

    def test_hard_errors_when_coq_project_missing(self, tmp_path):
        parent = tmp_path / "synth"
        parent.mkdir()
        with pytest.raises(ValueError, match="_CoqProject not found"):
            prepare_workdir(
                parent_dir=str(parent), basename="demo",
                skeleton_text="", coq_project_src=None,
            )


# ---------------------------------------------------------------------------
# Pre-spawn prerequisite checks


class TestCheckPrerequisites:
    SKELETON = (
        "Require Import Coq.ZArith.ZArith.\n"
        "From MonadLib Require Import MonadLib.\n"
        "Require Import list_tail_rel_lib.\n"
        "Require Export sllseg_rel_lib.\n"
    )

    def test_required_callee_libs_filters_to_rel_lib(self):
        names = required_callee_libs(self.SKELETON)
        assert names == ["list_tail_rel_lib", "sllseg_rel_lib"]

    def test_no_callees_no_check(self, tmp_path):
        skel = "From MonadLib Require Import MonadLib.\n"
        # coq_lib_dir unset is fine when there are no callees.
        check_prerequisites(skel, None)

    def test_errors_when_coq_lib_dir_unset(self):
        with pytest.raises(ValueError, match="COQ_LIB_DIR is unset"):
            check_prerequisites(self.SKELETON, None)

    def test_errors_when_callee_missing(self, tmp_path):
        # Provide one callee but not the other.
        (tmp_path / "list_tail_rel_lib.v").write_text("(* stub *)")
        with pytest.raises(ValueError, match="sllseg_rel_lib.v"):
            check_prerequisites(self.SKELETON, str(tmp_path))

    def test_passes_when_all_callees_present(self, tmp_path):
        (tmp_path / "list_tail_rel_lib.v").write_text("(* stub *)")
        (tmp_path / "sllseg_rel_lib.v").write_text("(* stub *)")
        check_prerequisites(self.SKELETON, str(tmp_path))  # must not raise


# ---------------------------------------------------------------------------
# Layer-2 file-system whitelist


class TestValidateWorkdirFilesystem:
    def _setup(self, tmp_path):
        workdir = tmp_path / "wd"
        (workdir / "skeleton").mkdir(parents=True)
        (workdir / "out").mkdir(parents=True)
        (workdir / "AGENTS.md").write_text("rules")
        (workdir / "skeleton/demo_rel_lib.v").write_text("Parameter X : Type.")
        (workdir / "_CoqProject").write_text("-Q . X")
        return workdir

    def test_passes_when_only_whitelisted_files_changed(self, tmp_path):
        wd = self._setup(tmp_path)
        before = snapshot_workdir(str(wd))
        # Agent rewrites the skeleton and writes a transcript — allowed.
        (wd / "skeleton/demo_rel_lib.v").write_text("Definition X : Type := nat.")
        (wd / "out/transcript.txt").write_text("done")
        validate_workdir_filesystem(
            str(wd), before,
            expected_modified={"skeleton/demo_rel_lib.v"},
            expected_created={"out/transcript.txt"},
        )

    def test_rejects_modified_read_only_file(self, tmp_path):
        wd = self._setup(tmp_path)
        before = snapshot_workdir(str(wd))
        (wd / "AGENTS.md").write_text("the agent tampered with this")
        with pytest.raises(ValueError, match="AGENTS.md"):
            validate_workdir_filesystem(
                str(wd), before,
                expected_modified={"skeleton/demo_rel_lib.v"},
                expected_created={"out/transcript.txt"},
            )

    def test_rejects_unexpected_new_file(self, tmp_path):
        wd = self._setup(tmp_path)
        before = snapshot_workdir(str(wd))
        (wd / "scratch.v").write_text("Definition junk := tt.")
        with pytest.raises(ValueError, match="unexpected file"):
            validate_workdir_filesystem(
                str(wd), before,
                expected_modified={"skeleton/demo_rel_lib.v"},
                expected_created={"out/transcript.txt"},
            )

    def test_rejects_deleted_file(self, tmp_path):
        wd = self._setup(tmp_path)
        before = snapshot_workdir(str(wd))
        os.remove(wd / "_CoqProject")
        with pytest.raises(ValueError, match="deleted"):
            validate_workdir_filesystem(
                str(wd), before,
                expected_modified={"skeleton/demo_rel_lib.v"},
                expected_created={"out/transcript.txt"},
            )


# ---------------------------------------------------------------------------
# Layer-3 strict skeleton diff


class TestValidateSkeletonDiff:
    SKEL = """\
Require Import Coq.ZArith.ZArith.
From MonadLib Require Import MonadLib.

Parameter MretTy : Type.

Parameter demo_M_loop_M1 : (list Z * Z) -> MONAD MretTy.

Definition demo_M_loop_aux := repeat_break demo_M_loop_body.

Parameter demo_M_loop_M2 : (list Z * Z) -> MONAD (list Z * Z).
"""

    MUST_DEFINE = ["MretTy", "demo_M_loop_M1", "demo_M_loop_M2"]

    def test_accepts_pure_parameter_to_definition_replacement(self):
        filled = """\
Require Import Coq.ZArith.ZArith.
From MonadLib Require Import MonadLib.

Definition MretTy : Type := (list Z * Z).

Definition demo_M_loop_M1 : (list Z * Z) -> MONAD MretTy :=
  fun a => return a.

Definition demo_M_loop_aux := repeat_break demo_M_loop_body.

Definition demo_M_loop_M2 : (list Z * Z) -> MONAD (list Z * Z) :=
  fun a => return a.
"""
        # Must not raise.
        validate_skeleton_diff(self.SKEL, filled, self.MUST_DEFINE)

    def test_rejects_signature_drift(self):
        filled = self.SKEL.replace(
            "Parameter MretTy : Type.",
            "Definition MretTy : Type := nat.",
        ).replace(
            # Signature changed from `(list Z * Z) -> MONAD MretTy` to
            # `list Z -> MONAD MretTy` — this is the violation under test.
            "Parameter demo_M_loop_M1 : (list Z * Z) -> MONAD MretTy.",
            "Definition demo_M_loop_M1 : list Z -> MONAD MretTy := fun l => return l.",
        ).replace(
            "Parameter demo_M_loop_M2 : (list Z * Z) -> MONAD (list Z * Z).",
            "Definition demo_M_loop_M2 : (list Z * Z) -> MONAD (list Z * Z) := fun a => return a.",
        )
        with pytest.raises(ValueError, match="signature must not change"):
            validate_skeleton_diff(self.SKEL, filled, self.MUST_DEFINE)

    def test_rejects_modification_of_concrete_definition(self):
        filled = self.SKEL.replace(
            "Definition demo_M_loop_aux := repeat_break demo_M_loop_body.",
            "Definition demo_M_loop_aux := repeat_break demo_M_loop_body_TAMPERED.",
        ).replace(
            "Parameter MretTy : Type.",
            "Definition MretTy : Type := nat.",
        ).replace(
            "Parameter demo_M_loop_M1 : (list Z * Z) -> MONAD MretTy.",
            "Definition demo_M_loop_M1 : (list Z * Z) -> MONAD MretTy := fun a => return a.",
        ).replace(
            "Parameter demo_M_loop_M2 : (list Z * Z) -> MONAD (list Z * Z).",
            "Definition demo_M_loop_M2 : (list Z * Z) -> MONAD (list Z * Z) := fun a => return a.",
        )
        with pytest.raises(ValueError, match="modified outside the agreed contract"):
            validate_skeleton_diff(self.SKEL, filled, self.MUST_DEFINE)

    def test_rejects_added_foreign_definition(self):
        filled = self.SKEL.replace(
            "Parameter MretTy : Type.",
            "Definition MretTy : Type := nat.\nDefinition demo_M_loop_M1_FAKE : nat := 0.",
        )
        with pytest.raises(ValueError, match="not present in skeleton"):
            validate_skeleton_diff(self.SKEL, filled, self.MUST_DEFINE)

    def test_rejects_removed_block(self):
        filled = "\n".join(
            line for line in self.SKEL.splitlines()
            if "demo_M_loop_M2" not in line
        )
        with pytest.raises(ValueError, match="removed top-level block"):
            validate_skeleton_diff(self.SKEL, filled, self.MUST_DEFINE)

    def test_rejects_must_define_left_as_parameter(self):
        # Agent only replaced one of three must_define entries.
        filled = self.SKEL.replace(
            "Parameter MretTy : Type.",
            "Definition MretTy : Type := nat.",
        ).replace(
            "Parameter demo_M_loop_M1 : (list Z * Z) -> MONAD MretTy.",
            "Definition demo_M_loop_M1 : (list Z * Z) -> MONAD MretTy := fun a => return a.",
        )
        # demo_M_loop_M2 is still a Parameter.
        with pytest.raises(ValueError, match="demo_M_loop_M2.*still declared as a Parameter"):
            validate_skeleton_diff(self.SKEL, filled, self.MUST_DEFINE)

    def test_rejects_definition_without_type(self):
        filled = self.SKEL.replace(
            "Parameter MretTy : Type.",
            "Definition MretTy := nat.",
        ).replace(
            "Parameter demo_M_loop_M1 : (list Z * Z) -> MONAD MretTy.",
            "Definition demo_M_loop_M1 : (list Z * Z) -> MONAD MretTy := fun a => return a.",
        ).replace(
            "Parameter demo_M_loop_M2 : (list Z * Z) -> MONAD (list Z * Z).",
            "Definition demo_M_loop_M2 : (list Z * Z) -> MONAD (list Z * Z) := fun a => return a.",
        )
        with pytest.raises(ValueError, match="omits the type annotation"):
            validate_skeleton_diff(self.SKEL, filled, self.MUST_DEFINE)

    def test_outer_parens_tolerated_on_signature(self):
        filled = self.SKEL.replace(
            "Parameter MretTy : Type.",
            "Definition MretTy : Type := nat.",
        ).replace(
            "Parameter demo_M_loop_M1 : (list Z * Z) -> MONAD MretTy.",
            # Extra balanced parens around the signature — normalized away.
            "Definition demo_M_loop_M1 : ((list Z * Z) -> MONAD MretTy) := fun a => return a.",
        ).replace(
            "Parameter demo_M_loop_M2 : (list Z * Z) -> MONAD (list Z * Z).",
            "Definition demo_M_loop_M2 : (list Z * Z) -> MONAD (list Z * Z) := fun a => return a.",
        )
        validate_skeleton_diff(self.SKEL, filled, self.MUST_DEFINE)


# ---------------------------------------------------------------------------
# Combined attempt validation


class TestValidateAttempt:
    SKEL = """\
Parameter MretTy : Type.

Parameter demo_M_loop_M1 : list Z -> MONAD MretTy.
"""

    def test_passes_for_clean_attempt(self, tmp_path):
        wd = tmp_path / "wd"
        (wd / "skeleton").mkdir(parents=True)
        (wd / "out").mkdir(parents=True)
        skel_path = wd / "skeleton/demo_rel_lib.v"
        skel_path.write_text(self.SKEL)
        (wd / "AGENTS.md").write_text("rules")
        (wd / "_CoqProject").write_text("-Q . X")
        before = snapshot_workdir(str(wd))
        # Agent edits the skeleton and writes a transcript.
        filled = (
            "Definition MretTy : Type := nat.\n\n"
            "Definition demo_M_loop_M1 : list Z -> MONAD MretTy := "
            "fun l => return 0.\n"
        )
        skel_path.write_text(filled)
        (wd / "out/transcript.txt").write_text("done")
        ok, msg = validate_attempt(
            str(wd), before, self.SKEL, filled,
            must_define=["MretTy", "demo_M_loop_M1"],
            basename="demo",
        )
        assert ok, msg
        assert msg is None

    def test_reports_skeleton_diff_failure(self, tmp_path):
        wd = tmp_path / "wd"
        (wd / "skeleton").mkdir(parents=True)
        (wd / "out").mkdir(parents=True)
        skel_path = wd / "skeleton/demo_rel_lib.v"
        skel_path.write_text(self.SKEL)
        (wd / "AGENTS.md").write_text("rules")
        (wd / "_CoqProject").write_text("-Q . X")
        before = snapshot_workdir(str(wd))
        filled = (
            "Definition MretTy : Type := nat.\n\n"
            "Definition demo_M_loop_M1 : list Z -> MONAD nat := "  # signature drift
            "fun l => return 0.\n"
        )
        skel_path.write_text(filled)
        (wd / "out/transcript.txt").write_text("done")
        ok, msg = validate_attempt(
            str(wd), before, self.SKEL, filled,
            must_define=["MretTy", "demo_M_loop_M1"],
            basename="demo",
        )
        assert not ok
        assert "skeleton diff" in msg
        assert "signature must not change" in msg

    def test_reports_filesystem_failure_before_diff(self, tmp_path):
        wd = tmp_path / "wd"
        (wd / "skeleton").mkdir(parents=True)
        (wd / "out").mkdir(parents=True)
        skel_path = wd / "skeleton/demo_rel_lib.v"
        skel_path.write_text(self.SKEL)
        (wd / "AGENTS.md").write_text("rules")
        (wd / "_CoqProject").write_text("-Q . X")
        before = snapshot_workdir(str(wd))
        # Agent's "filled" version is fine but they ALSO tampered with AGENTS.md.
        filled = (
            "Definition MretTy : Type := nat.\n\n"
            "Definition demo_M_loop_M1 : list Z -> MONAD MretTy := "
            "fun l => return 0.\n"
        )
        skel_path.write_text(filled)
        (wd / "AGENTS.md").write_text("rules — tampered")
        (wd / "out/transcript.txt").write_text("done")
        ok, msg = validate_attempt(
            str(wd), before, self.SKEL, filled,
            must_define=["MretTy", "demo_M_loop_M1"],
            basename="demo",
        )
        assert not ok
        assert "file-system whitelist" in msg


# ---------------------------------------------------------------------------
# Workdir-mode prompt allocation: AGENTS.md owns static framework knowledge,
# stdin owns the per-attempt task brief.  These invariants pin task #31's
# slim done — any drift (e.g. someone re-adding "## QCP Monad Primitives"
# to the prompt) breaks the test.


class TestPromptAllocation:
    @pytest.fixture
    def stdin_prompt(self, tmp_path):
        from GenMonads.absprog.context import collect_synthesis_context
        from GenMonads.absprog.templates import render_prompt
        c_file = "shape_invdataset/Glibc_slist_clean_iter/glibc_slist_iter_back_2.c"
        ctx = collect_synthesis_context(
            c_file,
            sibling_dirs=["shape_invdataset/Glibc_slist_clean_iter"],
        )
        return render_prompt(ctx)

    @pytest.fixture
    def agents_md(self):
        return render_agents_md("glibc_slist_iter_back_2")

    def test_static_framework_text_lives_in_agents_md(self, agents_md):
        # Sections A5–A12 are the framework cheatsheet — present in AGENTS.md.
        assert "QCP Monad primitives" in agents_md or "## A5" in agents_md
        assert "Naming conventions" in agents_md or "## A7" in agents_md
        assert "Forest mechanics" in agents_md or "## A8" in agents_md
        assert "Opaque-call obligations" in agents_md or "## A10" in agents_md

    def test_static_framework_text_not_in_stdin(self, stdin_prompt):
        # The same content must NOT have leaked back into the stdin prompt.
        assert "## QCP Monad Primitives" not in stdin_prompt
        assert "Use plain `return EXPR`" not in stdin_prompt
        assert "Do not replace helper-call results with `any`." not in stdin_prompt
        assert "Every opaque call's result must be bound to a named variable" not in stdin_prompt
        assert "You are generating Coq monadic abstract programs" not in stdin_prompt

    def test_dynamic_task_content_lives_in_stdin(self, stdin_prompt):
        # Per-function content the AGENTS.md cannot know.
        assert "## Function Summary" in stdin_prompt
        assert "## C Source" in stdin_prompt
        assert "## Prompt Context" in stdin_prompt
        assert "## Required Signatures" in stdin_prompt
        # Workdir pointer — the agent reads the actual skeleton, not a
        # mocked sketch.
        assert "skeleton/<basename>_rel_lib.v" in stdin_prompt

    def test_workdir_pointer_replaces_per_call_sketch(self, stdin_prompt):
        # No inlined ``Definition <fn>_M_loop1_M2 :`` sketch leaking back.
        fn = "glibc_slist_clean_iter_back_2"
        scaffold = stdin_prompt.split("## Selected Scaffold", 1)[1].split("##", 1)[0]
        assert f"Definition {fn}_M_loop1_M2" not in scaffold
        assert f"{fn}_M_loop2_aux" not in scaffold

    def test_must_define_list_carries_per_function_names(self, stdin_prompt):
        fn = "glibc_slist_clean_iter_back_2"
        # The dynamic name list is in the slim prompt.
        assert "## Definitions to Provide" in stdin_prompt
        assert f"- `{fn}_M_loop1_M1`" in stdin_prompt
        assert f"- `{fn}_M_loop1_to_inner_2`" in stdin_prompt


# ---------------------------------------------------------------------------
# AGENTS.md mentions every workdir-specific contract


class TestAgentsMdContracts:
    def test_workdir_contract_keywords_present(self):
        md = render_agents_md("demo")
        # A2 — file system contract
        assert "Edit ONLY" in md
        assert "out/transcript.txt" in md
        # A3 — verification command
        assert "coqc -arg-file _CoqProject" in md
        assert "exit code is 0" in md
        # A4 — strict replacement contract
        assert "STRICT" in md
        assert "byte-identical" in md
        # A11 — sandbox limits
        assert "Network access is disabled" in md
        # A12 — failure semantics
        assert "Admitted" in md


# ---------------------------------------------------------------------------
# Bug #1 — Layer 2 tolerates coqc output artifacts.
# Bug #2 — Layer 2 tolerates `.codex/` + rocq-mcp setup when available.


from GenMonads.absprog.workdir import (
    _is_tolerated_path,
    _write_rocq_mcp_config,
)


class TestTolerateCoqcArtifacts:
    def _setup(self, tmp_path):
        wd = tmp_path / "wd"
        (wd / "skeleton").mkdir(parents=True)
        (wd / "out").mkdir(parents=True)
        (wd / "AGENTS.md").write_text("rules")
        (wd / "skeleton/demo_rel_lib.v").write_text("Parameter X : Type.")
        (wd / "_CoqProject").write_text("-Q . X")
        return wd

    def test_tolerated_path_predicate_recognises_coqc_extensions(self):
        for path in (
            "skeleton/demo_rel_lib.vo",
            "skeleton/demo_rel_lib.vok",
            "skeleton/demo_rel_lib.vos",
            "skeleton/demo_rel_lib.glob",
            "skeleton/.demo_rel_lib.aux",
        ):
            assert _is_tolerated_path(path), \
                f"coqc artifact {path!r} should be tolerated"

    def test_tolerated_path_predicate_rejects_source_files(self):
        for path in (
            "skeleton/demo_rel_lib.v",
            "AGENTS.md",
            "_CoqProject",
            "out/transcript.txt",
        ):
            assert not _is_tolerated_path(path), \
                f"non-artifact path {path!r} must not be tolerated"

    def test_snapshot_workdir_skips_coqc_byproducts(self, tmp_path):
        wd = self._setup(tmp_path)
        # Drop a coqc output as if the agent had just compiled.
        (wd / "skeleton/demo_rel_lib.vo").write_bytes(b"\x00\x01compiled")
        snap = snapshot_workdir(str(wd))
        # Source files are present; artifacts are filtered out.
        assert "skeleton/demo_rel_lib.v" in snap
        assert "AGENTS.md" in snap
        assert "skeleton/demo_rel_lib.vo" not in snap

    def test_layer2_passes_when_only_coqc_artifacts_appeared(self, tmp_path):
        """Bug #1 regression: a well-behaved agent that runs coqc would
        previously be rejected because the .vo/.vok/.vos/.glob artifacts
        weren't in `expected_created`.  They're now ignored at snapshot
        time, so Layer 2 should pass without listing them explicitly."""
        wd = self._setup(tmp_path)
        before = snapshot_workdir(str(wd))
        # Agent makes a legitimate edit AND coqc emits the usual artifacts.
        (wd / "skeleton/demo_rel_lib.v").write_text(
            "Definition X : Type := nat."
        )
        (wd / "out/transcript.txt").write_text("done")
        for ext in (".vo", ".vok", ".vos", ".glob"):
            (wd / f"skeleton/demo_rel_lib{ext}").write_bytes(b"\x00" * 16)
        (wd / "skeleton/.demo_rel_lib.aux").write_bytes(b"\x00" * 8)
        # Must not raise — only the .v change and the transcript are
        # acknowledged; the artifacts are silently ignored.
        validate_workdir_filesystem(
            str(wd), before,
            expected_modified={"skeleton/demo_rel_lib.v"},
            expected_created={"out/transcript.txt"},
        )


class TestTolerateCodexInternals:
    def _setup(self, tmp_path):
        wd = tmp_path / "wd"
        (wd / "skeleton").mkdir(parents=True)
        (wd / "out").mkdir(parents=True)
        (wd / "AGENTS.md").write_text("rules")
        (wd / "skeleton/demo_rel_lib.v").write_text("Parameter X : Type.")
        (wd / "_CoqProject").write_text("-Q . X")
        return wd

    def test_tolerated_path_predicate_recognises_codex_subtree(self):
        for path in (".codex", ".codex/config.toml", ".codex/history.jsonl"):
            assert _is_tolerated_path(path), f"{path!r} should be tolerated"

    def test_snapshot_workdir_skips_codex_directory(self, tmp_path):
        wd = self._setup(tmp_path)
        codex_dir = wd / ".codex"
        codex_dir.mkdir()
        (codex_dir / "history.jsonl").write_text("{}\n")
        (codex_dir / "config.toml").write_text("[stub]\n")
        snap = snapshot_workdir(str(wd))
        # Nothing under .codex/ shows up in the snapshot.
        assert all(not p.startswith(".codex") for p in snap)
        assert "AGENTS.md" in snap

    def test_layer2_passes_when_codex_writes_internals(self, tmp_path):
        """Bug #2 regression: codex may write `.codex/history.jsonl` etc
        for its own bookkeeping; that must not fail the file-system
        whitelist."""
        wd = self._setup(tmp_path)
        before = snapshot_workdir(str(wd))
        (wd / "skeleton/demo_rel_lib.v").write_text("Definition X : Type := nat.")
        (wd / "out/transcript.txt").write_text("done")
        # Codex emits its own state mid-run.
        codex_dir = wd / ".codex"
        codex_dir.mkdir()
        (codex_dir / "history.jsonl").write_text("{}\n")
        validate_workdir_filesystem(
            str(wd), before,
            expected_modified={"skeleton/demo_rel_lib.v"},
            expected_created={"out/transcript.txt"},
        )


class TestRocqMcpSetup:
    @pytest.fixture
    def cp(self, tmp_path):
        path = tmp_path / "_CoqProject"
        path.write_text("-R . Demo\n", encoding="utf-8")
        return path

    def test_write_rocq_mcp_config_registers_mcp_server(self, monkeypatch, tmp_path, cp):
        monkeypatch.setattr(
            "GenMonads.absprog.workdir.shutil.which",
            lambda name: "/usr/local/bin/rocq-mcp" if name == "rocq-mcp" else None,
        )
        path = _write_rocq_mcp_config(str(tmp_path / "wd"), str(cp))
        assert path.endswith(".codex/config.toml")
        body = open(path, encoding="utf-8").read()
        assert "[mcp_servers.rocq-mcp]" in body
        assert 'command = "/usr/local/bin/rocq-mcp"' in body
        # cwd resolves to where the _CoqProject lives so rocq-mcp picks up
        # the project's -R / -Q paths.
        assert f'cwd = "{cp.parent}"' in body or f'cwd = "{tmp_path}"' in body

    def test_prepare_workdir_auto_enables_rocq_mcp_when_available(self, monkeypatch, tmp_path, cp):
        monkeypatch.setattr(
            "GenMonads.absprog.workdir.shutil.which",
            lambda name: "/usr/local/bin/rocq-mcp" if name == "rocq-mcp" else None,
        )
        paths = prepare_workdir(
            parent_dir=str(tmp_path / "synth"),
            basename="demo",
            skeleton_text="",
            coq_project_src=str(cp),
        )
        assert paths["use_rocq_mcp"] is True
        assert os.path.isfile(os.path.join(paths["workdir"], ".codex/config.toml"))
        # AGENTS.md A3 points at rocq-mcp.
        md = open(paths["agents_md"], encoding="utf-8").read()
        assert "rocq-mcp" in md
        assert ".codex/config.toml" in md

    def test_prepare_workdir_skips_rocq_mcp_when_unavailable(self, monkeypatch, tmp_path, cp):
        monkeypatch.setattr(
            "GenMonads.absprog.workdir.shutil.which",
            lambda name: None,  # neither rocq-mcp nor anything else found
        )
        paths = prepare_workdir(
            parent_dir=str(tmp_path / "synth"),
            basename="demo",
            skeleton_text="",
            coq_project_src=str(cp),
        )
        assert paths["use_rocq_mcp"] is False
        assert not os.path.exists(os.path.join(paths["workdir"], ".codex/config.toml"))
        md = open(paths["agents_md"], encoding="utf-8").read()
        # Coqc-only guidance is shown; rocq-mcp is NOT mentioned.
        assert "rocq-mcp" not in md
        assert "coqc -arg-file _CoqProject" in md

    def test_prepare_workdir_explicit_override_wins_over_autodetect(self, monkeypatch, tmp_path, cp):
        # rocq-mcp IS available, but caller explicitly pins False.
        monkeypatch.setattr(
            "GenMonads.absprog.workdir.shutil.which",
            lambda name: "/usr/local/bin/rocq-mcp" if name == "rocq-mcp" else None,
        )
        paths = prepare_workdir(
            parent_dir=str(tmp_path / "synth"),
            basename="demo",
            skeleton_text="",
            coq_project_src=str(cp),
            use_rocq_mcp=False,
        )
        assert paths["use_rocq_mcp"] is False
        assert not os.path.exists(os.path.join(paths["workdir"], ".codex/config.toml"))

    def test_prepare_workdir_clears_stale_mcp_config_when_rocq_mcp_disappears(
        self, monkeypatch, tmp_path, cp,
    ):
        """If a prior attempt configured rocq-mcp but the host no longer has
        it, the stale ``.codex/config.toml`` must be removed so the agent
        isn't told to use a binary that's gone."""
        # First call with rocq-mcp present.
        monkeypatch.setattr(
            "GenMonads.absprog.workdir.shutil.which",
            lambda name: "/usr/local/bin/rocq-mcp" if name == "rocq-mcp" else None,
        )
        prepare_workdir(
            parent_dir=str(tmp_path / "synth"),
            basename="demo", skeleton_text="", coq_project_src=str(cp),
        )
        # Now rocq-mcp is gone.
        monkeypatch.setattr(
            "GenMonads.absprog.workdir.shutil.which",
            lambda name: None,
        )
        paths = prepare_workdir(
            parent_dir=str(tmp_path / "synth"),
            basename="demo", skeleton_text="", coq_project_src=str(cp),
        )
        assert paths["use_rocq_mcp"] is False
        assert not os.path.exists(os.path.join(paths["workdir"], ".codex/config.toml"))


class TestAgentsMdRocqMcpVariant:
    def test_coqc_only_variant_omits_rocq_mcp_mentions(self):
        md = render_agents_md("demo", use_rocq_mcp=False)
        assert "rocq-mcp" not in md
        assert "coqc -arg-file _CoqProject skeleton/demo_rel_lib.v" in md
        # Coqc-only guidance includes the Rocq vernacular hint.
        assert "Show." in md or "Search" in md

    def test_rocq_mcp_variant_recommends_mcp(self):
        md = render_agents_md("demo", use_rocq_mcp=True)
        assert "rocq-mcp" in md
        assert ".codex/config.toml" in md
        # Final coqc verification still required as the success gate.
        assert "coqc -arg-file _CoqProject skeleton/demo_rel_lib.v" in md


# ---------------------------------------------------------------------------
# Bug #3 backstop — validator resolves bare "MretTy" against the skeleton
# when the skeleton uses a scoped {fn}_MretTy.  This is the Option-B
# defense; the canonical fix lives in context._scoped_mretty_name.


from GenMonads.absprog.workdir import _resolve_mretty_in_skeleton


class TestMrettyValidatorBackstop:
    SCOPED_SKELETON = """\
Require Import Coq.ZArith.ZArith.

Parameter foo_MretTy : Type.

Parameter foo_M_loop_M1 : list Z -> MONAD foo_MretTy.
"""

    BARE_SKELETON = """\
Require Import Coq.ZArith.ZArith.

Parameter MretTy : Type.

Parameter foo_M_loop_M1 : list Z -> MONAD MretTy.
"""

    def test_resolves_bare_must_define_against_scoped_skeleton(self):
        rewritten = _resolve_mretty_in_skeleton(
            self.SCOPED_SKELETON, ["MretTy", "foo_M_loop_M1"],
        )
        assert rewritten == ["foo_MretTy", "foo_M_loop_M1"]

    def test_passes_through_when_skeleton_uses_bare_mretty(self):
        rewritten = _resolve_mretty_in_skeleton(
            self.BARE_SKELETON, ["MretTy", "foo_M_loop_M1"],
        )
        assert rewritten == ["MretTy", "foo_M_loop_M1"]

    def test_passes_through_when_must_define_lacks_mretty(self):
        # No MretTy in must_define — nothing to resolve.
        rewritten = _resolve_mretty_in_skeleton(
            self.SCOPED_SKELETON, ["foo_M_loop_M1"],
        )
        assert rewritten == ["foo_M_loop_M1"]

    def test_raises_on_ambiguous_scoping(self):
        multi = (
            "Parameter foo_MretTy : Type.\n\n"
            "Parameter bar_MretTy : Type.\n"
        )
        with pytest.raises(ValueError, match="Ambiguous MretTy scoping"):
            _resolve_mretty_in_skeleton(multi, ["MretTy"])

    def test_validate_skeleton_diff_accepts_scoped_replacement_with_bare_must_define(self):
        """End-to-end backstop: validator accepts a multi-function-scoped
        Definition even when the caller forgot to expand ``"MretTy"`` in
        must_define."""
        filled = self.SCOPED_SKELETON.replace(
            "Parameter foo_MretTy : Type.",
            "Definition foo_MretTy : Type := list Z.",
        ).replace(
            "Parameter foo_M_loop_M1 : list Z -> MONAD foo_MretTy.",
            "Definition foo_M_loop_M1 : list Z -> MONAD foo_MretTy := fun l => return l.",
        )
        # Must not raise — backstop normalises must_define internally.
        validate_skeleton_diff(
            self.SCOPED_SKELETON, filled,
            must_define=["MretTy", "foo_M_loop_M1"],
        )


# ---------------------------------------------------------------------------
# Symmetric MretTy backstop — handle BOTH directions of drift between
# must_define and the skeleton's MretTy scoping.


class TestSymmetricMrettyBackstop:
    BARE_SKEL = (
        "Parameter MretTy : Type.\n\n"
        "Parameter demo_M_loop_M1 : list Z -> MONAD MretTy.\n"
    )

    SCOPED_SKEL = (
        "Parameter demo_MretTy : Type.\n\n"
        "Parameter demo_M_loop_M1 : list Z -> MONAD demo_MretTy.\n"
    )

    def test_scoped_must_define_with_bare_skeleton_collapses_to_bare(self):
        """Bug 3 case: a buggy counter emitted ``demo_MretTy`` in
        must_define but the skeleton only declares bare ``MretTy``.  The
        backstop rewrites must_define so the validator sees the agreed
        bare name on both sides."""
        rewritten = _resolve_mretty_in_skeleton(
            self.BARE_SKEL, ["demo_MretTy", "demo_M_loop_M1"],
        )
        assert rewritten == ["MretTy", "demo_M_loop_M1"]

    def test_bare_must_define_with_scoped_skeleton_promotes_to_scoped(self):
        """Existing direction (Option B): bare must_define + scoped
        skeleton → must_define is rewritten to scoped."""
        rewritten = _resolve_mretty_in_skeleton(
            self.SCOPED_SKEL, ["MretTy", "demo_M_loop_M1"],
        )
        assert rewritten == ["demo_MretTy", "demo_M_loop_M1"]

    def test_both_bare_no_change(self):
        rewritten = _resolve_mretty_in_skeleton(
            self.BARE_SKEL, ["MretTy", "demo_M_loop_M1"],
        )
        assert rewritten == ["MretTy", "demo_M_loop_M1"]

    def test_both_scoped_no_change(self):
        rewritten = _resolve_mretty_in_skeleton(
            self.SCOPED_SKEL, ["demo_MretTy", "demo_M_loop_M1"],
        )
        assert rewritten == ["demo_MretTy", "demo_M_loop_M1"]

    def test_validate_skeleton_diff_accepts_bare_definition_when_must_define_scoped(self):
        """End-to-end: the buggy-must_define case from Bug 3.  The agent
        correctly produces ``Definition MretTy`` (matching the skeleton).
        With the symmetric backstop the validator accepts."""
        filled = self.BARE_SKEL.replace(
            "Parameter MretTy : Type.",
            "Definition MretTy : Type := list Z.",
        ).replace(
            "Parameter demo_M_loop_M1 : list Z -> MONAD MretTy.",
            "Definition demo_M_loop_M1 : list Z -> MONAD MretTy := fun l => return l.",
        )
        # Must not raise — the symmetric backstop collapses the scoped
        # must_define entry to bare so the validator sees a consistent pair.
        validate_skeleton_diff(
            self.BARE_SKEL, filled,
            must_define=["demo_MretTy", "demo_M_loop_M1"],
        )

    def test_preserves_ordering_when_renaming(self):
        """List order matters for stable prompt output — verify the
        rewrite is in-place rather than rebuilding from a set."""
        rewritten = _resolve_mretty_in_skeleton(
            self.BARE_SKEL,
            ["demo_M_loop_M1", "demo_MretTy", "demo_M_loop_M2"],
        )
        assert rewritten == ["demo_M_loop_M1", "MretTy", "demo_M_loop_M2"]
