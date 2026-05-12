import sys

import pytest

from GenMonads.absprog.gen_func_residual import (
    ResidualSegment,
    append_func_residual_definitions,
    generate_func_residual_entries,
    generate_func_residual_segments,
    polish_residual_segment,
    promote_captured_identifiers_to_arguments,
)


def test_generate_func_residual_segments_for_nested_bind_in_m1(tmp_path):
    coq_file = tmp_path / "demo_rel_lib.v"
    coq_file.write_text(
        """Parameter callee_M : A -> B -> MONAD R.

Definition caller_M : A -> MONAD T :=
  fun a =>
    x <- (y <- callee_M arg1 arg2;;
          m12 y);;
    m2 x.
""",
        encoding="utf-8",
    )

    segments = generate_func_residual_segments(str(coq_file), "callee_M", "caller_M")

    assert len(segments) == 1
    assert "Definition residual_prog_in_caller_M_call_1 : R -> MONAD (T) :=" in segments[0]
    assert "fun y =>" in segments[0]
    assert "x <- m12 y;;" in segments[0]
    assert "m2 x" in segments[0]


def test_generate_func_residual_segments_for_call_in_left_branch_of_top_bind(tmp_path):
    coq_file = tmp_path / "demo_rel_lib.v"
    coq_file.write_text(
        """Parameter callee_M : A -> B -> MONAD R.

Definition caller_M : A -> MONAD T :=
  fun a =>
    r <- callee_M arg1 arg2;;
    k r.
""",
        encoding="utf-8",
    )

    segments = generate_func_residual_segments(str(coq_file), "callee_M", "caller_M")

    assert len(segments) == 1
    assert "Definition residual_prog_in_caller_M_call_1 : R -> MONAD (T) :=" in segments[0]
    assert "fun r =>" in segments[0]
    assert "k r" in segments[0]


def test_generate_func_residual_segments_for_call_in_tail_has_no_residual(tmp_path):
    coq_file = tmp_path / "demo_rel_lib.v"
    coq_file.write_text(
        """Parameter callee_M : T -> MONAD R.

Definition caller_M : A -> MONAD T :=
  fun a =>
    x <- m1 a;;
    callee_M x.
""",
        encoding="utf-8",
    )

    segments = generate_func_residual_segments(str(coq_file), "callee_M", "caller_M")

    assert len(segments) == 1
    assert "Definition residual_prog_in_caller_M_call_1 : R -> MONAD (T) :=" in segments[0]
    assert "fun r =>" in segments[0]
    assert "return r" in segments[0]


def test_generate_func_residual_segments_descends_into_match_without_extra_residual(tmp_path):
    coq_file = tmp_path / "demo_rel_lib.v"
    coq_file.write_text(
        """Parameter callee_M : X -> Y -> MONAD R.

Definition caller_M : A -> MONAD T :=
  fun a =>
    match a with
    | nil =>
        r <- callee_M x y;;
        k r
    | _ =>
        return z
    end.
""",
        encoding="utf-8",
    )

    segments = generate_func_residual_segments(str(coq_file), "callee_M", "caller_M")

    assert len(segments) == 1
    assert "Definition residual_prog_in_caller_M_call_1 : R -> MONAD (T) :=" in segments[0]
    assert "fun r =>" in segments[0]
    assert "k r" in segments[0]


def test_generate_func_residual_segments_descends_into_choice_without_extra_residual(tmp_path):
    coq_file = tmp_path / "demo_rel_lib.v"
    coq_file.write_text(
        """Parameter callee_M : P -> Q -> MONAD R.

Definition caller_M : A -> MONAD T :=
  fun a =>
    x <- choice (r <- callee_M p q;;
                 k r)
                (return alt);;
    m x.
""",
        encoding="utf-8",
    )

    segments = generate_func_residual_segments(str(coq_file), "callee_M", "caller_M")

    assert len(segments) == 1
    assert "Definition residual_prog_in_caller_M_call_1 : R -> MONAD (T) :=" in segments[0]
    assert "fun r =>" in segments[0]
    assert "x <- k r;;" in segments[0]
    assert "m x" in segments[0]


def test_generate_func_residual_segments_repeat_break_accumulates_repeat_tail(tmp_path):
    coq_file = tmp_path / "demo_rel_lib.v"
    coq_file.write_text(
        """Parameter callee_M : A -> B -> MONAD R.

Definition body : S -> MONAD (CntOrBrk S T) :=
  fun l =>
    r <- callee_M arg1 arg2;;
    return (by_continue r).

Definition caller_M : S -> MONAD U :=
  fun l =>
    x <- repeat_break body l;;
    m x.
""",
        encoding="utf-8",
    )

    segments = generate_func_residual_segments(str(coq_file), "callee_M", "caller_M")

    assert len(segments) == 1
    assert "Definition residual_prog_in_caller_M_call_1 : R -> MONAD (U) :=" in segments[0]
    assert "fun r =>" in segments[0]
    assert "return (by_continue r)" in segments[0]
    assert "x <- match step with" in segments[0]
    assert "| by_continue a' => repeat_break body a'" in segments[0]
    assert "| by_break b => ret b" in segments[0]
    assert "m x" in segments[0]


def test_generate_func_residual_entries_record_captured_identifiers(tmp_path):
    coq_file = tmp_path / "demo_rel_lib.v"
    coq_file.write_text(
        """Parameter callee_M : A -> B -> MONAD R.

Definition caller_M : X -> MONAD Y :=
  fun a =>
    r <- callee_M arg1 arg2;;
    return (ReturnNow (l4 ++ (y0 :: r))).
""",
        encoding="utf-8",
    )

    entries = generate_func_residual_entries(str(coq_file), "callee_M", "caller_M")

    assert len(entries) == 1
    assert entries[0].caller_component == "caller_M"
    assert entries[0].call_index == 1
    assert entries[0].captured_identifiers == ["l4", "y0"]
    assert entries[0].captured_identifier_types == {}
    assert "Definition residual_prog_in_caller_M_call_1 : R -> MONAD (Y) :=" in entries[0].definition
    assert "return (ReturnNow (l4 ++ (y0 :: r)))" in entries[0].definition


def test_generate_func_residual_entries_record_captured_identifier_types_from_origin_definition(tmp_path):
    coq_file = tmp_path / "demo_rel_lib.v"
    coq_file.write_text(
        """Definition loop_M2
  : (list Z * list Z) -> MONAD (list Z) :=
  fun '(l4, l1) =>
    match l1 with
    | nil =>
        r <- callee_M l4 l1;;
        return (l4 ++ r)
    | y0 :: y' =>
        r <- callee_M l4 y';;
        return (y0 :: r)
    end.

Definition caller_M :=
  fun s => loop_M2 s.
""",
        encoding="utf-8",
    )

    entries = generate_func_residual_entries(str(coq_file), "callee_M", "caller_M")

    assert len(entries) == 2
    assert entries[0].captured_identifier_types == {"l4": "list Z"}
    assert entries[1].captured_identifier_types == {"y0": "Z"}


def test_promote_captured_identifiers_to_arguments_adds_args_to_definition_header():
    definition = """Definition residual_prog_in_sll_multi_merge_M_loop_M1_call_1 :=
  fun r =>
    return (l4 ++ r)."""

    promoted = promote_captured_identifiers_to_arguments(
        definition,
        ["l4"],
        {"l4": "list Z"},
    )

    assert promoted.startswith(
        "Definition residual_prog_in_sll_multi_merge_M_loop_M1_call_1 (l4 : list Z) :="
    )
    assert "fun r =>" in promoted


def test_promote_captured_identifiers_to_arguments_keeps_untyped_names_plain():
    definition = """Definition residual_prog_in_demo_call_1 :=
  fun r =>
    return (l4 ++ r)."""

    promoted = promote_captured_identifiers_to_arguments(
        definition,
        ["l4", "y0"],
        {"l4": "list Z"},
    )

    assert promoted.startswith(
        "Definition residual_prog_in_demo_call_1 (l4 : list Z) y0 :="
    )


def test_promote_captured_identifiers_to_arguments_is_noop_when_none():
    definition = """Definition residual_prog_in_sll_multi_merge_M_loop_before_call_1 :=
  fun r =>
    return (ReturnNow r)."""

    promoted = promote_captured_identifiers_to_arguments(definition, [])

    assert promoted == definition


def test_polish_residual_segment_keeps_fun_underscore_argument():
    entry = ResidualSegment(
        caller_component="caller_M",
        call_index=1,
        binder="_",
        body="return a",
        definition="Definition residual_prog_in_caller_M_call_1 :=\n  fun _ =>\n    return a.",
        captured_identifiers=[],
        captured_identifier_types={},
        callee_return_type=None,
        caller_return_type=None,
        origin_component="caller_M",
        origin_start=0,
    )

    polished = polish_residual_segment(entry)

    assert polished.definition == (
        "Definition residual_prog_in_caller_M_call_1 :=\n  fun _ =>\n    return a."
    )


def test_polish_residual_segment_simplifies_bind_over_return():
    entry = ResidualSegment(
        caller_component="caller_M",
        call_index=1,
        binder="x",
        body="y <- return a;;\nm y",
        definition="Definition residual_prog_in_caller_M_call_1 :=\n  fun x =>\n    y <- return a;;\n    m y.",
        captured_identifiers=[],
        captured_identifier_types={},
        callee_return_type=None,
        caller_return_type=None,
        origin_component="caller_M",
        origin_start=0,
    )

    polished = polish_residual_segment(entry)

    assert "y <- return a" not in polished.definition
    assert "m a" in polished.definition


def test_polish_residual_segment_substitutes_identifiers_with_apostrophes():
    entry = ResidualSegment(
        caller_component="caller_M",
        call_index=1,
        binder="r",
        body="""s' <- return (ReturnNow (l4 ++ r));;
step <- match s' with
            | Continue s'' => continue s''
            | ReturnNow r' => break (ReturnNow r')
            end""",
        definition="",
        captured_identifiers=["l4"],
        captured_identifier_types={"l4": "list Z"},
        callee_return_type=None,
        caller_return_type=None,
        origin_component="caller_M",
        origin_start=0,
    )

    polished = polish_residual_segment(entry)

    assert "s' <- return" not in polished.definition
    assert "match (ReturnNow (l4 ++ r)) with" in polished.definition


def test_polish_residual_segment_respects_nested_match_branch_binders():
    entry = ResidualSegment(
        caller_component="sll_multi_merge_M",
        call_index=3,
        binder="r",
        body="""a' <- return (ReturnNow (l4 ++ r));;
step <- match a' with
            | Continue a'' => continue a''
            | ReturnNow r' => break (ReturnNow r')
            end;;
re <- match step with
        | by_continue a' => repeat_break sll_multi_merge_M_loop_body a'
        | by_break b => ret b
        end;;
sll_multi_merge_M_after_loop re""",
        definition="",
        captured_identifiers=["l4"],
        captured_identifier_types={"l4": "list Z"},
        callee_return_type=None,
        caller_return_type=None,
        origin_component="sll_multi_merge_M_loop_M2",
        origin_start=0,
    )

    polished = polish_residual_segment(entry)

    assert "a' <- return" not in polished.definition
    assert "match (ReturnNow (l4 ++ r)) with" in polished.definition
    assert "| by_continue a' => repeat_break sll_multi_merge_M_loop_body a'" in polished.definition
    assert "| by_continue (ReturnNow (l4 ++ r))" not in polished.definition
    assert "fun r =>" in polished.definition
    assert "break (ReturnNow r')" in polished.definition


def test_polish_residual_segment_preserves_parentheses_for_constructor_arguments():
    entry = ResidualSegment(
        caller_component="sll_multi_merge_M",
        call_index=2,
        binder="r",
        body="""x <- return (Continue (l4 ++ r));;
step <- break x""",
        definition="",
        captured_identifiers=["l4"],
        captured_identifier_types={"l4": "list Z"},
        callee_return_type=None,
        caller_return_type=None,
        origin_component="sll_multi_merge_M_loop_M1",
        origin_start=0,
    )

    polished = polish_residual_segment(entry)

    assert "x <- return" not in polished.definition
    assert "break (Continue (l4 ++ r))" in polished.definition
    assert "break Continue (l4 ++ r)" not in polished.definition


def test_append_func_residual_definitions_appends_promoted_definitions(tmp_path):
    coq_file = tmp_path / "demo_rel_lib.v"
    coq_file.write_text(
        """Parameter callee_M : A -> B -> MONAD X.

Definition caller_M : (list Z * T) -> MONAD Y :=
  fun '(l4, a) =>
    r <- callee_M arg1 arg2;;
    return (l4 ++ r).
""",
        encoding="utf-8",
    )

    appended = append_func_residual_definitions(str(coq_file), "callee_M", "caller_M")
    updated = coq_file.read_text(encoding="utf-8")

    assert len(appended) == 1
    assert appended[0].startswith(
        "Definition residual_prog_in_caller_M_call_1 (l4 : list Z) : X -> MONAD (Y) :="
    )
    assert updated.endswith(appended[0] + "\n")
    assert "Definition caller_M : (list Z * T) -> MONAD Y :=" in updated


def test_append_func_residual_definitions_returns_empty_when_no_calls(tmp_path):
    coq_file = tmp_path / "demo_rel_lib.v"
    original = """Definition caller_M :=
  fun a =>
    return a.
"""
    coq_file.write_text(original, encoding="utf-8")

    appended = append_func_residual_definitions(str(coq_file), "callee_M", "caller_M")

    assert appended == []
    assert coq_file.read_text(encoding="utf-8") == original


def test_residual_cli_accepts_uppercase_flags(monkeypatch, tmp_path, capsys):
    from GenMonads.absprog import residual_cli

    calls = {}

    def fake_append(file_path, callee, caller, polish):
        calls["args"] = (file_path, callee, caller, polish)
        return ["Definition residual_prog_in_caller_M_call_1 :=\n  fun r =>\n    None."]

    monkeypatch.setattr(residual_cli, "append_func_residual_definitions", fake_append)
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "llm4pv-residual",
            f"--FILE={tmp_path / 'demo.v'}",
            "--CALLEE=callee_M",
            "--CALLER=caller_M",
        ],
    )

    residual_cli.main()

    assert calls["args"] == (str(tmp_path / "demo.v"), "callee_M", "caller_M", True)
    captured = capsys.readouterr()
    assert "Appended 1 residual definition(s)" in captured.out
    assert "Definition residual_prog_in_caller_M_call_1" not in captured.out


def test_residual_cli_defaults_to_polish(monkeypatch, tmp_path):
    from GenMonads.absprog import residual_cli

    calls = {}

    def fake_append(file_path, callee, caller, polish):
        calls["args"] = (file_path, callee, caller, polish)
        return []

    monkeypatch.setattr(residual_cli, "append_func_residual_definitions", fake_append)
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "llm4pv-residual",
            f"--FILE={tmp_path / 'demo.v'}",
            "--CALLEE=callee_M",
            "--CALLER=caller_M",
        ],
    )

    residual_cli.main()

    assert calls["args"] == (str(tmp_path / "demo.v"), "callee_M", "caller_M", True)


def test_residual_cli_accepts_no_polish_flag(monkeypatch, tmp_path):
    from GenMonads.absprog import residual_cli

    calls = {}

    def fake_append(file_path, callee, caller, polish):
        calls["args"] = (file_path, callee, caller, polish)
        return []

    monkeypatch.setattr(residual_cli, "append_func_residual_definitions", fake_append)
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "llm4pv-residual",
            f"--FILE={tmp_path / 'demo.v'}",
            "--CALLEE=callee_M",
            "--CALLER=caller_M",
            "--NO-POLISH",
        ],
    )

    residual_cli.main()

    assert calls["args"] == (str(tmp_path / "demo.v"), "callee_M", "caller_M", False)


def test_residual_cli_accepts_positional_arguments(monkeypatch, tmp_path):
    from GenMonads.absprog import residual_cli

    calls = {}

    def fake_append(file_path, callee, caller, polish):
        calls["args"] = (file_path, callee, caller, polish)
        return []

    monkeypatch.setattr(residual_cli, "append_func_residual_definitions", fake_append)
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "llm4pv-residual",
            str(tmp_path / "demo.v"),
            "callee_M",
            "caller_M",
        ],
    )

    residual_cli.main()

    assert calls["args"] == (str(tmp_path / "demo.v"), "callee_M", "caller_M", True)


def test_residual_cli_help_uses_clear_metavars(monkeypatch, capsys):
    from GenMonads.absprog import residual_cli

    monkeypatch.setattr(
        sys,
        "argv",
        [
            "llm4pv-residual",
            "--help",
        ],
    )

    with pytest.raises(SystemExit) as excinfo:
        residual_cli.main()

    assert excinfo.value.code == 0
    captured = capsys.readouterr()
    assert "[FILE] [CALLEE] [CALLER]" in captured.out


def test_generate_func_residual_entries_preserves_args_when_unfolding_named_definition(tmp_path):
    coq_file = tmp_path / "demo_rel_lib.v"
    coq_file.write_text(
        """Definition body :=
  fun s =>
    r <- callee_M s z;;
    return r.

Definition caller_M :=
  fun x =>
    body x.
""",
        encoding="utf-8",
    )

    entries = generate_func_residual_entries(str(coq_file), "callee_M", "caller_M")

    assert len(entries) == 1
    assert "return r" in entries[0].definition
    assert entries[0].captured_identifiers == []


def test_generate_func_residual_entries_beta_reduces_simple_fun_application(tmp_path):
    coq_file = tmp_path / "demo_rel_lib.v"
    coq_file.write_text(
        """Definition body :=
  fun a =>
    assume!! (guard a);;
    r <- callee_M a z;;
    return r.

Definition caller_M :=
  fun s =>
    body s.
""",
        encoding="utf-8",
    )

    entries = generate_func_residual_entries(str(coq_file), "callee_M", "caller_M")

    assert len(entries) == 1
    assert "callee_M s z" not in entries[0].definition
    assert "assume!! (guard s)" not in entries[0].definition
    assert "return r" in entries[0].definition


def test_generate_func_residual_entries_uses_let_for_pattern_fun_application(tmp_path):
    coq_file = tmp_path / "demo_rel_lib.v"
    coq_file.write_text(
        """Definition body :=
  fun '(l1, l2) =>
    r <- callee_M l1 l2;;
    return r.

Definition caller_M :=
  fun s =>
    body s.
""",
        encoding="utf-8",
    )

    entries = generate_func_residual_entries(str(coq_file), "callee_M", "caller_M")

    assert len(entries) == 1
    assert "return r" in entries[0].definition


def test_generate_func_residual_entries_finds_all_calls_from_whole_sll_multi_merge_shape(tmp_path):
    coq_file = tmp_path / "sll_multi_merge_rel_lib.v"
    coq_file.write_text(
        """Parameter sll_merge_M : list Z -> list Z -> MONAD (list Z).

Definition sll_multi_merge_M_loop_M1
  : (list Z * list Z * list Z * list Z) -> MONAD MretTy :=
  fun '(l1, l2, l3, l4) =>
    r <- sll_merge_M l1 l2;;
    return (l4 ++ r).

Definition sll_multi_merge_M_loop_M2
  : (list Z * list Z * list Z * list Z)
    -> MONAD (early_result (list Z * list Z * list Z * list Z) (list Z)) :=
  fun '(l1, l2, l3, l4) =>
    match l3 with
    | nil =>
        return (Continue (l1, l2, l3, l4))
    | u0 :: u' =>
        match l1 with
        | nil =>
            r <- sll_merge_M l3 l2;;
            return (ReturnNow (l4 ++ r))
        | y0 :: y' =>
            match l2 with
            | nil =>
                r <- sll_merge_M l3 y';;
                return (ReturnNow (l4 ++ (y0 :: r)))
            | z0 :: z' =>
                return (Continue (y', z', u', l4 ++ (y0 :: z0 :: u0 :: nil)))
            end
        end
    end.

Definition sll_multi_merge_M_loop_body :=
  fun a =>
    choice (assume!! (~ guard);; r <- sll_multi_merge_M_loop_M1 a ;; break (Continue r))
           (assume!! guard;;
            a' <- sll_multi_merge_M_loop_M2 a ;;
            match a' with
            | Continue a'' => continue a''
            | ReturnNow r' => break (ReturnNow r')
            end).

Definition sll_multi_merge_M_loop_aux :=
  repeat_break sll_multi_merge_M_loop_body.

Definition sll_multi_merge_M_loop_before :=
  fun l1 l2 l3 =>
    match l1 with
    | nil =>
        r <- sll_merge_M l2 l3;;
        return (ReturnNow r)
    | xh :: xt =>
        return (Continue (l2, l3, xt, xh :: nil))
    end.

Definition sll_multi_merge_M : list Z -> list Z -> list Z -> MONAD (list Z) :=
  fun l1 l2 l3 =>
    e <- sll_multi_merge_M_loop_before l1 l2 l3;;
    match e with
    | Continue s =>
        re <- sll_multi_merge_M_loop_aux s;;
        sll_multi_merge_M_after_loop re
    | ReturnNow r =>
        return r
    end.
""",
        encoding="utf-8",
    )

    entries = generate_func_residual_entries(str(coq_file), "sll_merge_M", "sll_multi_merge_M")

    assert len(entries) == 4
    assert entries[0].definition.startswith(
        "Definition residual_prog_in_sll_multi_merge_M_call_1 : list Z -> MONAD (list Z) :="
    )
    assert entries[1].definition.startswith(
        "Definition residual_prog_in_sll_multi_merge_M_call_2 : list Z -> MONAD (list Z) :="
    )
    assert entries[2].definition.startswith(
        "Definition residual_prog_in_sll_multi_merge_M_call_3 : list Z -> MONAD (list Z) :="
    )
    assert entries[3].definition.startswith(
        "Definition residual_prog_in_sll_multi_merge_M_call_4 : list Z -> MONAD (list Z) :="
    )
    assert [entry.origin_component for entry in entries] == [
        "sll_multi_merge_M_loop_before",
        "sll_multi_merge_M_loop_M1",
        "sll_multi_merge_M_loop_M2",
        "sll_multi_merge_M_loop_M2",
    ]
    assert entries[1].captured_identifier_types == {"l4": "list Z"}
    assert entries[2].captured_identifier_types == {"l4": "list Z"}
    assert entries[3].captured_identifier_types == {"l4": "list Z", "y0": "Z"}


def test_generate_func_residual_entries_parses_multiline_parameter_signature(tmp_path):
    coq_file = tmp_path / "demo_rel_lib.v"
    coq_file.write_text(
        """Parameter callee_M
  : list Z -> list Z
    -> MONAD (list Z).

Definition caller_M : list Z -> MONAD (list Z) :=
  fun a =>
    r <- callee_M a a;;
    return r.
""",
        encoding="utf-8",
    )

    entries = generate_func_residual_entries(str(coq_file), "callee_M", "caller_M")

    assert len(entries) == 1
    assert entries[0].callee_return_type is not None
    assert "list Z" in entries[0].callee_return_type
    assert "list Z -> MONAD" in entries[0].definition


def test_generate_func_residual_entries_infers_types_through_nested_fun_layers(tmp_path):
    coq_file = tmp_path / "demo_rel_lib.v"
    coq_file.write_text(
        """Parameter callee_M : list Z -> MONAD (list Z).

Definition caller_M : list Z -> list Z -> MONAD (list Z) :=
  fun l1 =>
    fun l2 =>
      r <- callee_M l1;;
      return (l2 ++ r).
""",
        encoding="utf-8",
    )

    entries = generate_func_residual_entries(str(coq_file), "callee_M", "caller_M")

    assert len(entries) == 1
    assert entries[0].captured_identifiers == ["l2"]
    assert entries[0].captured_identifier_types == {"l2": "list Z"}


def test_generate_func_residual_entries_handles_tuple_destructuring_bind(tmp_path):
    coq_file = tmp_path / "demo_rel_lib.v"
    coq_file.write_text(
        """Parameter callee_M : A -> B -> MONAD (list Z * list Z).

Definition caller_M : A -> MONAD (list Z) :=
  fun a =>
    '(x, y) <- callee_M arg1 arg2;;
    return (x ++ y).
""",
        encoding="utf-8",
    )

    entries = generate_func_residual_entries(str(coq_file), "callee_M", "caller_M")

    assert len(entries) == 1
    assert "fun v =>" in entries[0].definition
    assert "let '(x, y) := v in" in entries[0].definition
    assert "return (x ++ y)" in entries[0].definition
    assert entries[0].captured_identifiers == []


def test_generate_func_residual_entries_tuple_bind_with_continuation(tmp_path):
    coq_file = tmp_path / "demo_rel_lib.v"
    coq_file.write_text(
        """Parameter callee_M : A -> MONAD (list Z * list Z).

Definition caller_M : A -> MONAD (list Z) :=
  fun a =>
    '(x, y) <- callee_M a;;
    z <- m x;;
    return (z ++ y).
""",
        encoding="utf-8",
    )

    entries = generate_func_residual_entries(str(coq_file), "callee_M", "caller_M")

    assert len(entries) == 1
    defn = entries[0].definition
    assert "fun v =>" in defn
    assert "let '(x, y) := v in" in defn
    assert "z <- m x" in defn
    assert "return (z ++ y)" in defn


def test_hygienic_renaming_preserves_callee_result_binder_in_nested_composition(tmp_path):
    coq_file = tmp_path / "demo_rel_lib.v"
    coq_file.write_text(
        """Definition loop_m1 :=
  fun a =>
    r <- callee_M a;;
    return (l4 ++ r).

Definition loop_body :=
  fun a =>
    choice (assume!! guard;;
            r <- loop_m1 a;;
            break (Continue r))
           (return alt).

Definition loop_aux :=
  repeat_break loop_body.

Definition caller_M :=
  fun s =>
    re <- loop_aux s;;
    after re.
""",
        encoding="utf-8",
    )

    entries = generate_func_residual_entries(str(coq_file), "callee_M", "caller_M")
    polished = [polish_residual_segment(entry) for entry in entries]

    assert len(polished) == 1
    assert "fun r =>" in polished[0].definition


def test_residual_entries_use_extra_signatures_for_cross_file_callee(tmp_path):
    """A callee imported via ``Require Import`` is not present in the file's
    Definition/Parameter list, so its signature must be supplied via
    ``extra_signatures`` to get a typed residual definition.
    """
    coq_file = tmp_path / "caller_rel_lib.v"
    coq_file.write_text(
        """\
Require Import callee_rel_lib.

Definition caller_M : list Z -> MONAD (list Z) :=
  fun l =>
    r <- callee_M l ;;
    return r.
""",
        encoding="utf-8",
    )

    # Without extra_signatures: callee return type is unknown, so the
    # residual definition lacks a type annotation.
    entries_untyped = generate_func_residual_entries(str(coq_file), "callee_M", "caller_M")
    assert entries_untyped, "expected at least one residual entry"
    assert ": list Z -> MONAD" not in entries_untyped[0].definition

    # With extra_signatures: the cross-file callee's return type is known
    # and the residual definition becomes fully typed.
    entries_typed = generate_func_residual_entries(
        str(coq_file),
        "callee_M",
        "caller_M",
        extra_signatures={"callee_M": "list Z -> MONAD (list Z)"},
    )
    assert entries_typed
    assert (
        "Definition residual_prog_in_caller_M_call_1 : list Z -> MONAD (list Z) :="
        in entries_typed[0].definition
    )
