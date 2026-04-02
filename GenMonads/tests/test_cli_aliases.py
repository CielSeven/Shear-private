import argparse
import sys
import importlib

import pytest

from GenMonads.absprog import cli as rellib_cli
from GenMonads.guardgen import cli as guard_cli
from GenMonads.cli_common import add_output_path_argument, resolve_cli_value

translate_cli = importlib.import_module("GenMonads.translate_c_file")


def test_translate_cli_accepts_file_and_output_aliases(monkeypatch, capsys):
    calls = {}

    def fake_translate(input_path, output_path):
        calls["args"] = (input_path, output_path)
        return True

    monkeypatch.setattr(translate_cli, "translate_c_file", fake_translate)
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "llm4pv",
            "--FILE=input/demo.c",
            "--OUTPUT_PATH=output/demo_rel.c",
        ],
    )

    translate_cli.main()

    assert calls["args"] == ("input/demo.c", "output/demo_rel.c")
    captured = capsys.readouterr()
    assert "Translation successful: output/demo_rel.c" in captured.out


def test_translate_cli_exits_nonzero_on_single_file_failure(monkeypatch, capsys):
    monkeypatch.setattr(translate_cli, "translate_c_file", lambda *_args: False)
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "llm4pv",
            "--FILE=input/demo.c",
            "--OUTPUT_PATH=output/demo_rel.c",
        ],
    )

    with pytest.raises(SystemExit) as excinfo:
        translate_cli.main()

    assert excinfo.value.code == 1
    captured = capsys.readouterr()
    assert "Translation failed" in captured.err


def test_translate_cli_exits_nonzero_on_directory_failure(monkeypatch, tmp_path, capsys):
    input_dir = tmp_path / "inputs"
    output_dir = tmp_path / "outputs"
    input_dir.mkdir()
    output_dir.mkdir()

    monkeypatch.setattr(
        translate_cli,
        "translate_directory",
        lambda *_args: {"alpha.c": True, "beta.c": False},
    )
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "llm4pv",
            str(input_dir),
            str(output_dir),
        ],
    )

    with pytest.raises(SystemExit) as excinfo:
        translate_cli.main()

    assert excinfo.value.code == 1
    captured = capsys.readouterr()
    assert "Summary: 1/2 files translated successfully" in captured.out


def test_resolve_cli_value_returns_normalized_path():
    parser = argparse.ArgumentParser(prog="demo")
    add_output_path_argument(parser, "output", "Output file or directory")
    args = parser.parse_args(["foo/../bar"])

    resolved = resolve_cli_value(
        args,
        parser,
        "output",
        ("output_path",),
        "missing output",
        is_path=True,
    )

    assert resolved == "bar"


def test_rellib_cli_accepts_file_and_output_aliases(monkeypatch, tmp_path, capsys):
    calls = {}

    def fake_generate(input_path, output_dir):
        calls["args"] = (input_path, output_dir)
        return str(tmp_path / "demo_rel_lib.v")

    monkeypatch.setattr(rellib_cli, "generate_rel_lib_for_file", fake_generate)
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "llm4pv-rellib",
            "--FILE=input/demo.c",
            f"--OUTPUT_PATH={tmp_path}",
        ],
    )

    rellib_cli.main()

    assert calls["args"] == ("input/demo.c", str(tmp_path))
    captured = capsys.readouterr()
    assert f"Generated: {tmp_path / 'demo_rel_lib.v'}" in captured.out


def test_rellib_cli_normalizes_default_output_dir(monkeypatch, tmp_path, capsys):
    calls = {}
    default_dir = tmp_path / "out" / ".." / "libs"

    def fake_generate(input_path, output_dir):
        calls["args"] = (input_path, output_dir)
        return str(tmp_path / "demo_rel_lib.v")

    monkeypatch.setattr(rellib_cli, "_default_output_dir", lambda: str(default_dir))
    monkeypatch.setattr(rellib_cli, "generate_rel_lib_for_file", fake_generate)
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "llm4pv-rellib",
            "input/demo.c",
        ],
    )

    rellib_cli.main()

    assert calls["args"] == ("input/demo.c", str(tmp_path / "libs"))
    captured = capsys.readouterr()
    assert f"Generated: {tmp_path / 'demo_rel_lib.v'}" in captured.out


@pytest.mark.parametrize(
    ("argv_tail", "expected_output"),
    [
        (["input/demo.c", "output/libs"], "output/libs"),
        (["input/demo.c", "--OUTPUT_PATH=output/libs"], "output/libs"),
        (["input/demo.c", "-o", "output/libs"], "output/libs"),
        (["input/demo.c", "--output-dir=output/libs"], "output/libs"),
    ],
)
def test_rellib_cli_accepts_all_output_forms(monkeypatch, tmp_path, capsys, argv_tail, expected_output):
    calls = {}

    def fake_generate(input_path, output_dir):
        calls["args"] = (input_path, output_dir)
        return str(tmp_path / "demo_rel_lib.v")

    monkeypatch.setattr(rellib_cli, "generate_rel_lib_for_file", fake_generate)
    monkeypatch.setattr(sys, "argv", ["llm4pv-rellib", *argv_tail])

    rellib_cli.main()

    assert calls["args"] == ("input/demo.c", expected_output)
    captured = capsys.readouterr()
    assert f"Generated: {tmp_path / 'demo_rel_lib.v'}" in captured.out


def test_rellib_cli_rejects_conflicting_output_values(monkeypatch, capsys):
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "llm4pv-rellib",
            "input/demo.c",
            "output/one",
            "--OUTPUT_PATH=output/two",
        ],
    )

    with pytest.raises(SystemExit) as excinfo:
        rellib_cli.main()

    assert excinfo.value.code == 2
    captured = capsys.readouterr()
    assert "Conflicting values provided for output_dir" in captured.err


def test_guard_cli_accepts_named_aliases(monkeypatch, capsys):
    seen = {}

    def fake_guard(inv, cond):
        seen["args"] = (inv, cond)
        return "guardP"

    monkeypatch.setattr(guard_cli, "gen_coq_guard", fake_guard)
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "llm4pv-guard",
            "--INV=sll(p, l1)",
            "--COND=p != null",
        ],
    )

    guard_cli.main()

    assert seen["args"] == ("sll(p, l1)", "p != null")
    captured = capsys.readouterr()
    assert captured.out.strip() == "guardP"
