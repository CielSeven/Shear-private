import textwrap

import pytest

from GenMonads.absprog import context as context_mod


def test_normalize_block_trims_outer_blank_lines_and_trailing_spaces():
    text = "\n  first line   \n    second line\t \n\n"

    assert context_mod._normalize_block(text) == "first line\n    second line"


def test_type_helpers_build_expected_coq_types():
    assert context_mod._tuple_type(["list Z"]) == "list Z"
    assert context_mod._tuple_type(["list Z", "Z"]) == "(list Z * Z)"
    assert context_mod._curried_type([]) == ""
    assert context_mod._curried_type(["list Z", "Z"]) == "list Z -> Z -> "
    assert context_mod._return_type_from_types([]) == "unit"
    assert context_mod._return_type_from_types(["list Z", "Z"]) == "(list Z * Z)"


def test_require_var_types_validates_presence_and_count():
    info = {
        "func_name": "demo",
        "require_var_count": 2,
        "require_var_types": ["list Z", "Z"],
    }

    assert context_mod._require_var_types(
        info, "require_var_types", "require_var_count"
    ) == ["list Z", "Z"]
    assert context_mod._require_var_types(
        {"func_name": "demo", "require_var_count": 0},
        "require_var_types",
        "require_var_count",
    ) == []

    with pytest.raises(ValueError, match="Missing require_var_types"):
        context_mod._require_var_types(
            {"func_name": "demo", "require_var_count": 1},
            "require_var_types",
            "require_var_count",
        )

    with pytest.raises(ValueError, match="expected 2, got 1"):
        context_mod._require_var_types(
            {
                "func_name": "demo",
                "require_var_count": 2,
                "require_var_types": ["list Z"],
            },
            "require_var_types",
            "require_var_count",
        )


def test_select_function_handles_single_and_multi_function_results():
    single = {"file": "single.c", "function": "only"}
    multi = {
        "file": "multi.c",
        "functions": [{"function": "left"}, {"function": "right"}],
    }

    assert context_mod._select_function(single, None)["function"] == "only"
    assert context_mod._select_function(multi, "right")["function"] == "right"

    with pytest.raises(ValueError, match="Function name is required for multi-function files"):
        context_mod._select_function(multi, None)

    with pytest.raises(ValueError, match="Function 'missing' not found in multi.c"):
        context_mod._select_function(multi, "missing")


def test_extract_function_source_ignores_prototypes_and_call_sites(tmp_path):
    c_file = tmp_path / "sample.c"
    c_file.write_text(
        textwrap.dedent(
            """\
            int helper(void) {
                return target(0);
            }

            int target(int x);

            int other(void) {
                return 1;
            }

            int target(int x)
            {
                if (x) {
                    return helper();
                }
                return other();
            }
            """
        ),
        encoding="utf-8",
    )

    assert context_mod._extract_function_source(str(c_file), "target") == textwrap.dedent(
        """\
        int target(int x)
        {
            if (x) {
                return helper();
            }
            return other();
        }"""
    )


def test_extract_function_source_raises_when_function_is_missing(tmp_path):
    c_file = tmp_path / "sample.c"
    c_file.write_text("int helper(void) { return 0; }\n", encoding="utf-8")

    with pytest.raises(ValueError, match="Could not find function signature for 'target'"):
        context_mod._extract_function_source(str(c_file), "target")


def test_predicate_family_prefers_more_specific_matches():
    assert context_mod._infer_predicate_family("store_tree(root, t)") == "store_tree"
    assert context_mod._infer_predicate_family("sll(x, l1) * sllseg(x, y, l2)") == "sllseg"
    assert context_mod._infer_predicate_family("tree(root, t)") == "tree"
    assert context_mod._infer_predicate_family("plain text only") is None


def test_has_segment_predicate_detects_any_segment_shape():
    assert context_mod._has_segment_predicate("sllseg(x, y, l1)")
    assert context_mod._has_segment_predicate("dllseg(x, y, l1)")
    assert context_mod._has_segment_predicate("lseg(x, y)")
    assert not context_mod._has_segment_predicate("sll(x, l1) * dll(y, l2)")


def test_collect_synthesis_context_matches_sll_reverse_fixture():
    ctx = context_mod.collect_synthesis_context("shape_invdataset/sll/sll_reverse.c")

    assert ctx["id"] == "sll_reverse"
    assert ctx["source"]["c_file"] == "shape_invdataset/sll/sll_reverse.c"
    assert ctx["predicate_family"] == "sll"
    assert ctx["summary"]["func_name"] == "sll_reverse"
    assert ctx["features"] == {
        "loop_count": 1,
        "require_var_count": 1,
        "inv_var_count": 2,
        "ensure_var_count": 1,
        "has_seg_predicate": False,
        "has_multi_return": False,
    }
    assert ctx["prompt_context"]["c_source"].startswith("struct list* sll_reverse")
    assert ctx["prompt_context"]["with_clause"] == "X l1"
    assert ctx["prompt_context"]["require_with_safeexec"] == (
        "safeExec(ATrue, sll_reverse_M(l1), X) && sll(head, l1)"
    )
    assert ctx["prompt_context"]["ensure_with_safeexec"] == (
        "exists l2, safeExec(ATrue, return(l2), X) && sll(__return, l2)"
    )
    assert ctx["prompt_context"]["loop_condition"] == "curr != (void *) 0"
    assert ctx["prompt_context"]["guard_coq"] == "fun a =>\n  let '(l1, l2) := a in\n  l2 <> []"
    assert "bind(sll_reverse_M_loop(l1,l2), sll_reverse_M_loop_end)" in ctx["prompt_context"][
        "loop_invariant_with_safeexec"
    ]
    assert ctx["control_flow"]["template_case"] == "none"
    assert ctx["control_flow"]["has_top_level_loop"] is True
    assert ctx["signatures"] == {
        "M_loop_before": "list Z -> MONAD (list Z * list Z)",
        "M_1": "(list Z * list Z) -> MONAD MretTy",
        "M_2": "(list Z * list Z) -> MONAD (list Z * list Z)",
        "M_loop_end": "MretTy -> MONAD (list Z)",
        "M": "list Z -> MONAD (list Z)",
    }


def test_collect_synthesis_context_captures_multi_return_copy_shape():
    ctx = context_mod.collect_synthesis_context("shape_invdataset/sll/sll_copy.c")

    assert ctx["predicate_family"] == "sllseg"
    assert ctx["summary"]["func_name"] == "sll_copy"
    assert ctx["features"]["has_seg_predicate"] is True
    assert ctx["features"]["has_multi_return"] is True
    assert ctx["features"]["ensure_var_count"] == 2
    assert ctx["prompt_context"]["loop_condition"] == "p"
    assert "return(maketuple(l2, l3))" in ctx["prompt_context"]["ensure_with_safeexec"]
    assert "sllseg(x@pre, p, l1)" in ctx["prompt_context"]["loop_invariant_with_safeexec"]
    assert ctx["signatures"]["M_loop_end"] == "MretTy -> MONAD ((list Z * list Z))"
    assert ctx["signatures"]["M"] == "list Z -> MONAD ((list Z * list Z))"


def test_collect_synthesis_context_requires_function_name_for_multifunction_file():
    with pytest.raises(ValueError, match="Function name is required for multi-function files"):
        context_mod.collect_synthesis_context("shape_invdataset/sll/sll_rotate.c")

    left = context_mod.collect_synthesis_context(
        "shape_invdataset/sll/sll_rotate.c", func_name="sll_rotate_left"
    )
    right = context_mod.collect_synthesis_context(
        "shape_invdataset/sll/sll_rotate.c", func_name="sll_rotate_right"
    )

    assert left["id"] == "sll_rotate_left"
    assert left["summary"]["func_name"] == "sll_rotate_left"
    assert left["features"]["inv_var_count"] == 3  # l1, l2 + data witness w
    assert right["id"] == "sll_rotate_right"
    assert right["summary"]["func_name"] == "sll_rotate_right"
    assert right["features"]["inv_var_count"] == 4  # l1, l2, l3 + data witness w


def test_collect_file_synthesis_manifest_tracks_targets_and_callees():
    manifest = context_mod.collect_file_synthesis_manifest("shape_invdataset/sll/sll_multi_merge.c")

    assert manifest["file_id"] == "sll_multi_merge"
    assert manifest["targets"] == ["sll_multi_merge"]
    funcs = {entry["func_name"]: entry for entry in manifest["functions"]}

    assert funcs["sll_merge"]["should_synthesize"] is False
    assert funcs["sll_merge"]["called_by"] == ["sll_multi_merge"]
    assert funcs["sll_merge"]["externals"]["M"] == "list Z -> list Z -> MONAD (list Z)"
    assert funcs["sll_multi_merge"]["should_synthesize"] is True
    assert funcs["sll_multi_merge"]["calls"] == ["sll_merge"]
    assert funcs["sll_multi_merge"]["summary"]["func_name"] == "sll_multi_merge"


def test_collect_synthesis_context_includes_available_callees_for_target():
    ctx = context_mod.collect_synthesis_context(
        "shape_invdataset/sll/sll_multi_merge.c",
        func_name="sll_multi_merge",
    )

    assert ctx["target"]["func_name"] == "sll_multi_merge"
    assert ctx["file_overview"]["targets"] == ["sll_multi_merge"]
    assert ctx["available_callees"][0]["func_name"] == "sll_merge"
    assert ctx["available_callees"][0]["externals"]["M"] == "list Z -> list Z -> MONAD (list Z)"
    assert ctx["available_callees"][0]["should_synthesize_elsewhere"] is False
    assert "sll_merge(y, z)" in " ".join(ctx["available_callees"][0]["call_sites"])
    assert ctx["generation_policy"]["opaque_external_programs"] == ["sll_merge_M"]
    assert ctx["generation_policy"]["generated_scaffolding"] == ["sll_multi_merge_M_after_loop"]
    assert ctx["opaque_call_obligations"][0]["callee"] == "sll_merge_M"
    assert ctx["opaque_call_obligations"][0]["must_use_placeholder"] is True
    assert ctx["control_flow"]["template_case"] == "both"
    assert ctx["control_flow"]["has_pre_loop_early_return"] is True
    assert ctx["control_flow"]["has_loop_body_early_return"] is True
    assert ctx["control_flow"]["prompt_signatures"]["M_loop_M1"] == (
        "(list Z * list Z * list Z * list Z * Z) -> MONAD MretTy"
    )
    assert ctx["control_flow"]["prompt_signatures"]["M_loop_M2"] == (
        "(list Z * list Z * list Z * list Z * Z) -> MONAD (early_result (list Z * list Z * list Z * list Z * Z) (list Z))"
    )
    assert "break (Continue r)" in ctx["control_flow"]["template"]["loop_body_definition"]
    assert "| ReturnNow r' => break (ReturnNow r')" in ctx["control_flow"]["template"]["loop_body_definition"]
    assert "sll_multi_merge_M_after_loop" in ctx["prompt_context"]["loop_invariant_with_safeexec"]
    assert "match e with" in ctx["control_flow"]["template"]["top_level"]


def test_collect_synthesis_context_raises_pipeline_error(monkeypatch):
    monkeypatch.setattr(
        context_mod,
        "process_and_translate_file",
        lambda *_args, **_kwargs: {"error": "broken pipeline"},
    )

    with pytest.raises(ValueError, match="broken pipeline"):
        context_mod.collect_synthesis_context("demo.c")


def test_collect_synthesis_context_rejects_functions_without_loop_invariants(monkeypatch):
    monkeypatch.setattr(
        context_mod,
        "process_and_translate_file",
        lambda *_args, **_kwargs: {"file": "demo.c", "function": "demo", "inner_assertions": []},
    )

    with pytest.raises(ValueError, match="Function 'demo' has no loop invariants"):
        context_mod.collect_synthesis_context("demo.c")


def test_collect_synthesis_context_uses_first_invariant_for_prompt_fields(monkeypatch):
    monkeypatch.setattr(
        context_mod,
        "process_and_translate_file",
        lambda *_args, **_kwargs: {
            "file": "demo.c",
            "function": "demo",
            "funcspec": {
                "require": {"translated": "sll(x, ?l1)"},
                "ensure": {"translated": "sll(__return, ?l2)"},
            },
            "inner_assertions": [
                {
                    "type": "Inv",
                    "variables": ["l1"],
                    "variable_types": ["list Z"],
                    "command_guard": "first_guard",
                    "coq_guard": "fun a => True",
                },
                {
                    "type": "Inv",
                    "translated": "exists l1, sll(x, l1)",
                    "variables": ["l1"],
                    "variable_types": ["list Z"],
                    "command_guard": "second_guard",
                    "coq_guard": "fun a => False",
                },
            ],
        },
    )
    monkeypatch.setattr(
        context_mod,
        "collect_func_extern_info",
        lambda _func_data: {
            "func_name": "demo",
            "require_var_count": 1,
            "require_var_types": ["list Z"],
            "inv_var_count": 1,
            "inv_var_types": ["list Z"],
            "ensure_var_count": 1,
            "ensure_var_types": ["list Z"],
        },
    )
    monkeypatch.setattr(
        context_mod,
        "process_funcspec_with_safeexec",
        lambda _funcspec, _program: {
            "with": {"translated": "X l1"},
            "require": {"with_safeexec": "REQ"},
            "ensure": {"with_safeexec": "ENS"},
        },
    )
    monkeypatch.setattr(context_mod, "_extract_function_source", lambda *_args, **_kwargs: "int demo(void) {}")

    ctx = context_mod.collect_synthesis_context("demo.c")

    assert ctx["features"]["loop_count"] == 2
    assert ctx["prompt_context"]["loop_condition"] == "first_guard"
    assert ctx["prompt_context"]["guard_coq"] == "fun a => True"
    assert ctx["prompt_context"]["loop_invariant_with_safeexec"] == ""
    assert ctx["prompt_context"]["require_with_safeexec"] == "REQ"
    assert ctx["prompt_context"]["ensure_with_safeexec"] == "ENS"
