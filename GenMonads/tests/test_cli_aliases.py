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

    def fake_translate(input_path, output_path, monad="staterel"):
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
            "--no-rel-lib",
            "--no-synth",
        ],
    )

    translate_cli.main()

    assert calls["args"] == ("input/demo.c", "output/demo_rel.c")
    captured = capsys.readouterr()
    assert "Translation successful: output/demo_rel.c" in captured.out


def test_translate_cli_exits_nonzero_on_single_file_failure(monkeypatch, capsys):
    monkeypatch.setattr(translate_cli, "translate_c_file", lambda *_args, **_kw: False)
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "llm4pv",
            "--FILE=input/demo.c",
            "--OUTPUT_PATH=output/demo_rel.c",
            "--no-rel-lib",
            "--no-synth",
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
        lambda *_args, **_kw: {"alpha.c": True, "beta.c": False},
    )
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "llm4pv",
            str(input_dir),
            str(output_dir),
            "--no-rel-lib",
            "--no-synth",
        ],
    )

    with pytest.raises(SystemExit) as excinfo:
        translate_cli.main()

    assert excinfo.value.code == 1
    captured = capsys.readouterr()
    assert "Summary: 1/2 files translated successfully" in captured.out


def test_translate_cli_runs_all_three_stages_with_default_synth_command(monkeypatch, tmp_path, capsys):
    """Default `llm4pv` should translate, generate the rel_lib template, and
    invoke synthesis with the codex command backend."""
    monkeypatch.setattr(translate_cli, "translate_c_file", lambda *_args, **_kw: True)
    lib_calls = []

    def fake_gen_lib(c_file, lib_dir, sibling_dirs=None, monad="staterel", **kw):
        lib_calls.append((c_file, lib_dir))
        return str(tmp_path / "lib" / "demo_rel_lib.v")

    synth_calls = {}

    def fake_synth_main():
        synth_calls["argv"] = list(sys.argv)

    monkeypatch.setattr(translate_cli, "_run_stage2", fake_gen_lib)
    monkeypatch.setattr(
        "GenMonads.absprog.context.collect_all_synthesis_contexts",
        lambda _src, sibling_dirs=None: [{"id": "demo"}],
    )
    monkeypatch.setattr(
        "GenMonads.absprog.synth_cli.main", fake_synth_main
    )
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "llm4pv",
            "--FILE=input/demo.c",
            "--OUTPUT_PATH=output/demo_rel.c",
            f"--coq-lib-dir={tmp_path / 'lib'}",
            f"--synth-output-dir={tmp_path / 'synth'}",
        ],
    )

    translate_cli.main()

    assert lib_calls == [("input/demo.c", str(tmp_path / "lib"))]
    argv = synth_calls["argv"]
    assert "--backend=command" in argv
    # Workdir-mode owns the codex invocation; no shell-template string is
    # passed via --command anymore.  The default is left as an empty stub
    # for CLI backwards-compat only.
    assert translate_cli.LLM4PV_DEFAULT_COMMAND == ""
    assert "--patch-rel-c" in argv
    assert f"--rel-c-path=output/demo_rel.c" in argv
    assert any(a.startswith("--max-retries=") for a in argv)


def test_translate_cli_no_rel_lib_with_default_synth_errors(monkeypatch, capsys):
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "llm4pv",
            "--FILE=input/demo.c",
            "--OUTPUT_PATH=output/demo_rel.c",
            "--no-rel-lib",
        ],
    )

    with pytest.raises(SystemExit) as excinfo:
        translate_cli.main()

    assert excinfo.value.code == 2
    captured = capsys.readouterr()
    assert "synth requires the rel_lib template" in captured.err


def test_translate_cli_stage2_failure_exits_with_code_2(monkeypatch, tmp_path, capsys):
    monkeypatch.setattr(translate_cli, "translate_c_file", lambda *_args, **_kw: True)
    monkeypatch.setattr(translate_cli, "_run_stage2", lambda *_args, **_kw: None)
    monkeypatch.setattr(
        "GenMonads.absprog.context.collect_all_synthesis_contexts",
        lambda _src, sibling_dirs=None: [{"id": "demo"}],
    )
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "llm4pv",
            "--FILE=input/demo.c",
            "--OUTPUT_PATH=output/demo_rel.c",
            f"--coq-lib-dir={tmp_path}",
            "--no-synth",
        ],
    )

    with pytest.raises(SystemExit) as excinfo:
        translate_cli.main()

    assert excinfo.value.code == 2
    captured = capsys.readouterr()
    assert "rel_lib generation failed" in captured.err


def test_translate_cli_no_synth_skips_stage3(monkeypatch, tmp_path):
    monkeypatch.setattr(translate_cli, "translate_c_file", lambda *_args, **_kw: True)
    monkeypatch.setattr(translate_cli, "_run_stage2", lambda *_args, **_kw: str(tmp_path / "lib.v"))
    monkeypatch.setattr(
        "GenMonads.absprog.context.collect_all_synthesis_contexts",
        lambda _src, sibling_dirs=None: [{"id": "demo"}],
    )

    called = {"synth": False}

    def fail_synth(*_a, **_k):
        called["synth"] = True
        return 0

    monkeypatch.setattr(translate_cli, "_run_stage3", fail_synth)
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "llm4pv",
            "--FILE=input/demo.c",
            "--OUTPUT_PATH=output/demo_rel.c",
            f"--coq-lib-dir={tmp_path}",
            "--no-synth",
        ],
    )

    translate_cli.main()

    assert called["synth"] is False


def test_topo_sort_orders_callee_before_caller(tmp_path):
    """Caller and callee live in the same directory.  Topological sort must
    place the callee first so its rel_lib is available when the caller's
    synthesis runs.
    """
    callee = tmp_path / "list_append_raw.c"
    callee.write_text(
        '#include "h.h"\n'
        'struct list *list_append_raw(struct list *x, struct list *y)\n'
        '/*@ Require listrep(x) * listrep(y)\n'
        '    Ensure  listrep(__return)\n'
        ' */\n'
        '{ return x; }\n'
    )
    caller = tmp_path / "glibc_slist_multi_append.c"
    caller.write_text(
        '#include "h.h"\n'
        'struct list *glibc_slist_multi_append(struct list *x, struct list *y)\n'
        '/*@ Require listrep(x) * listrep(y)\n'
        '    Ensure  listrep(__return)\n'
        ' */\n'
        '{ return list_append_raw(x, y); }\n'
    )
    c_files = [
        (str(caller), str(tmp_path / "glibc_slist_multi_append_rel.c")),
        (str(callee), str(tmp_path / "list_append_raw_rel.c")),
    ]
    ordered = translate_cli._topo_sort_c_files(c_files)
    names = [s[0].rsplit("/", 1)[-1] for s in ordered]
    assert names == ["list_append_raw.c", "glibc_slist_multi_append.c"]


def test_topo_sort_falls_back_on_cycle(tmp_path, capsys):
    """A → B → A cycle should fall back to alphabetical order with a warning."""
    a = tmp_path / "a.c"
    a.write_text(
        '#include "h.h"\n'
        'struct list *a(struct list *x)\n'
        '/*@ Require listrep(x)\n'
        '    Ensure  listrep(__return)\n'
        ' */\n'
        '{ return b(x); }\n'
    )
    b = tmp_path / "b.c"
    b.write_text(
        '#include "h.h"\n'
        'struct list *b(struct list *x)\n'
        '/*@ Require listrep(x)\n'
        '    Ensure  listrep(__return)\n'
        ' */\n'
        '{ return a(x); }\n'
    )
    c_files = [(str(a), str(a) + "_rel.c"), (str(b), str(b) + "_rel.c")]
    ordered = translate_cli._topo_sort_c_files(c_files)
    captured = capsys.readouterr()
    assert "cyclic" in captured.err
    assert [p[0] for p in ordered] == sorted([str(a), str(b)])


def test_translate_cli_skips_files_with_no_synthesis_targets(monkeypatch, tmp_path, capsys):
    """A file translated successfully in stage 1 but with no synthesis
    targets (e.g. callee-only declaration) should be skipped silently in
    stages 2 and 3 rather than treated as a stage 2 failure.
    """
    monkeypatch.setattr(translate_cli, "translate_c_file", lambda *_args, **_kw: True)

    stage2_calls = []
    monkeypatch.setattr(
        translate_cli,
        "_run_stage2",
        lambda src, _dir, sibling_dirs=None, monad="staterel": (stage2_calls.append(src), str(tmp_path / "x.v"))[1],
    )
    monkeypatch.setattr(
        "GenMonads.absprog.context.collect_all_synthesis_contexts",
        lambda _src, sibling_dirs=None: [],  # no targets
    )
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "llm4pv",
            "--FILE=input/demo.c",
            "--OUTPUT_PATH=output/demo_rel.c",
            f"--coq-lib-dir={tmp_path}",
            "--no-synth",
        ],
    )

    translate_cli.main()

    assert stage2_calls == []
    captured = capsys.readouterr()
    assert "Skipped (no synthesis targets): input/demo.c" in captured.out


def test_translate_cli_directory_mode_processes_callees_first(monkeypatch, tmp_path, capsys):
    input_dir = tmp_path / "inputs"
    output_dir = tmp_path / "outputs"
    input_dir.mkdir()
    (input_dir / "z_caller.c").write_text(
        '#include "h.h"\n'
        'struct list *z_caller(struct list *x)\n'
        '/*@ Require listrep(x)\n'
        '    Ensure  listrep(__return)\n'
        ' */\n'
        '{ return a_callee(x); }\n'
    )
    (input_dir / "a_callee.c").write_text(
        '#include "h.h"\n'
        'struct list *a_callee(struct list *x)\n'
        '/*@ Require listrep(x)\n'
        '    Ensure  listrep(__return)\n'
        ' */\n'
        '{ return x; }\n'
    )

    monkeypatch.setattr(
        translate_cli,
        "translate_directory",
        lambda *_a, **_kw: {"z_caller.c": True, "a_callee.c": True},
    )
    lib_order = []
    monkeypatch.setattr(
        translate_cli,
        "_run_stage2",
        lambda src, _dir, sibling_dirs=None, monad="staterel", **kw: (lib_order.append(src.rsplit("/", 1)[-1]), "x.v")[1],
    )
    monkeypatch.setattr(
        "GenMonads.absprog.context.collect_all_synthesis_contexts",
        lambda _src, sibling_dirs=None: [{"id": "demo"}],
    )
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "llm4pv",
            str(input_dir),
            str(output_dir),
            f"--coq-lib-dir={tmp_path}",
            "--no-synth",
        ],
    )

    translate_cli.main()

    assert lib_order == ["a_callee.c", "z_caller.c"]
    captured = capsys.readouterr()
    assert "Processing order (callees first): a_callee.c, z_caller.c" in captured.out


def test_translate_cli_requires_synth_output_dir_when_synth_enabled(monkeypatch, tmp_path, capsys):
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "llm4pv",
            "--FILE=input/demo.c",
            "--OUTPUT_PATH=output/demo_rel.c",
            f"--coq-lib-dir={tmp_path}",
        ],
    )

    with pytest.raises(SystemExit) as excinfo:
        translate_cli.main()

    assert excinfo.value.code == 2
    captured = capsys.readouterr()
    assert "--synth-output-dir is required" in captured.err


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

    def fake_generate(input_path, output_dir, sibling_dirs=None, monad="staterel", **kw):
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

    def fake_generate(input_path, output_dir, sibling_dirs=None, monad="staterel", **kw):
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

    def fake_generate(input_path, output_dir, sibling_dirs=None, monad="staterel", **kw):
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
