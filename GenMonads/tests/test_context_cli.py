import json
import sys

from GenMonads.absprog import context as context_mod
from GenMonads.absprog import context_cli


def test_collect_all_synthesis_contexts_expands_multifunction_files():
    contexts = context_mod.collect_all_synthesis_contexts("shape_invdataset/sll/sll_rotate.c")

    assert [ctx["id"] for ctx in contexts] == ["sll_rotate_left", "sll_rotate_right"]
    assert [ctx["summary"]["func_name"] for ctx in contexts] == [
        "sll_rotate_left",
        "sll_rotate_right",
    ]


def test_collect_all_synthesis_contexts_skips_helper_functions_without_invariants():
    contexts = context_mod.collect_all_synthesis_contexts("shape_invdataset/sll/sll_multi_merge.c")

    assert [ctx["id"] for ctx in contexts] == ["sll_multi_merge"]
    assert [ctx["summary"]["func_name"] for ctx in contexts] == ["sll_multi_merge"]


def test_write_synthesis_context_writes_json_file(tmp_path):
    output_path = tmp_path / "sll_reverse.auto.json"

    context = context_mod.write_synthesis_context(
        "shape_invdataset/sll/sll_reverse.c", str(output_path)
    )

    assert output_path.exists()
    written = json.loads(output_path.read_text(encoding="utf-8"))
    assert written["id"] == "sll_reverse"
    assert written["summary"]["func_name"] == "sll_reverse"
    assert written == context


def test_context_cli_writes_single_file_output(monkeypatch, tmp_path, capsys):
    output_path = tmp_path / "single.auto.json"

    monkeypatch.setattr(
        context_cli,
        "write_synthesis_context",
        lambda input_file, target_path: {
            "id": "demo",
            "summary": {"func_name": "demo"},
            "source": {"c_file": input_file},
            "written_to": target_path,
        },
    )
    monkeypatch.setattr(
        sys,
        "argv",
        ["llm4pv-context", "input/demo.c", str(output_path)],
    )

    context_cli.main()

    captured = capsys.readouterr()
    assert f"Generated: {output_path} (demo)" in captured.out


def test_context_cli_writes_directory_outputs(monkeypatch, tmp_path, capsys):
    input_dir = tmp_path / "inputs"
    output_dir = tmp_path / "outputs"
    input_dir.mkdir()
    (input_dir / "alpha.c").write_text("int alpha(void) { return 0; }\n", encoding="utf-8")
    (input_dir / "ignore.txt").write_text("skip\n", encoding="utf-8")

    monkeypatch.setattr(
        context_cli,
        "collect_all_synthesis_contexts",
        lambda input_file: [
            {"id": "alpha", "summary": {"func_name": "alpha"}},
            {"id": "alpha_helper", "summary": {"func_name": "alpha_helper"}},
        ],
    )
    monkeypatch.setattr(
        sys,
        "argv",
        ["llm4pv-context", str(input_dir), str(output_dir)],
    )

    context_cli.main()

    alpha_path = output_dir / "alpha.auto.json"
    helper_path = output_dir / "alpha_helper.auto.json"
    assert alpha_path.exists()
    assert helper_path.exists()
    assert json.loads(alpha_path.read_text(encoding="utf-8"))["id"] == "alpha"
    assert json.loads(helper_path.read_text(encoding="utf-8"))["id"] == "alpha_helper"

    captured = capsys.readouterr()
    assert f"Generated: {alpha_path}" in captured.out
    assert f"Generated: {helper_path}" in captured.out


def test_context_cli_accepts_alias_flags(monkeypatch, tmp_path, capsys):
    output_path = tmp_path / "single.auto.json"

    monkeypatch.setattr(
        context_cli,
        "write_synthesis_context",
        lambda input_file, target_path: {
            "id": "demo",
            "summary": {"func_name": "demo"},
            "source": {"c_file": input_file},
            "written_to": target_path,
        },
    )
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "llm4pv-context",
            "--FILE=input/demo.c",
            f"--OUTPUT_PATH={output_path}",
        ],
    )

    context_cli.main()

    captured = capsys.readouterr()
    assert f"Generated: {output_path} (demo)" in captured.out


def test_context_cli_reports_skipped_file_when_no_contexts(monkeypatch, tmp_path, capsys):
    input_dir = tmp_path / "inputs"
    output_dir = tmp_path / "outputs"
    input_dir.mkdir()
    (input_dir / "alpha.c").write_text("int alpha(void) { return 0; }\n", encoding="utf-8")

    monkeypatch.setattr(context_cli, "collect_all_synthesis_contexts", lambda _input_file: [])
    monkeypatch.setattr(
        sys,
        "argv",
        ["llm4pv-context", str(input_dir), str(output_dir)],
    )

    context_cli.main()

    captured = capsys.readouterr()
    assert f"Skipped: {input_dir / 'alpha.c'} (no loop-invariant contexts)" in captured.err
