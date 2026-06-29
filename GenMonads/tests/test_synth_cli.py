import sys

import pytest

from GenMonads.absprog import synth_cli


def test_synth_cli_accepts_alias_flags_for_single_input(monkeypatch, tmp_path, capsys):
    # The CLI argparse normalizes paths; the underlying pipeline is mocked
    # so the file does not need to be a real source.  Use a tmp_path file
    # to keep the test self-contained.
    c_file = tmp_path / "demo.c"
    c_file.write_text("int demo(void) { return 0; }\n", encoding="utf-8")
    output_dir = tmp_path / "out"

    calls = {}

    def fake_run(**kwargs):
        calls["kwargs"] = kwargs
        return {
            "status": "passed",
            "attempt_count": 1,
            "files": {
                "context": "ctx.json",
                "prompt": "prompt.txt",
                "prompt_payload": "prompt.json",
                "response": "response.txt",
                "parsed": "parsed.json",
                "assembled_rel_lib": "lib.v",
                "summary": "summary.json",
            },
            "check": {"status": "passed", "reason": ""},
        }

    monkeypatch.setattr(synth_cli, "run_synthesis_pipeline", fake_run)
    monkeypatch.setattr(sys, "argv", [
        "llm4pv-synth",
        f"--C_DIR={c_file}",
        f"--OUTPUT_PATH={output_dir}",
        "--max-retries=2",
        "--no-check",
        # Force LLM-style pipeline; segcodegen (the default) routes
        # through ``run_segcodegen_pipeline`` and bypasses the mocked
        # ``run_synthesis_pipeline``.
        "--backend=command",
    ])

    synth_cli.main()

    assert calls["kwargs"]["input_path"] == str(c_file)
    assert calls["kwargs"]["output_dir"] == str(output_dir)
    assert calls["kwargs"]["max_retries"] == 2
    assert calls["kwargs"]["run_check"] is False
    captured = capsys.readouterr()
    assert "Status: passed" in captured.out


def test_synth_cli_accepts_file_alias_for_single_input(monkeypatch, tmp_path, capsys):
    c_file = tmp_path / "demo.c"
    c_file.write_text("int demo(void) { return 0; }\n", encoding="utf-8")
    output_dir = tmp_path / "out"

    calls = {}

    def fake_run(**kwargs):
        calls["kwargs"] = kwargs
        return {
            "status": "passed",
            "attempt_count": 1,
            "files": {},
            "check": {"status": "passed", "reason": ""},
        }

    monkeypatch.setattr(synth_cli, "run_synthesis_pipeline", fake_run)
    monkeypatch.setattr(sys, "argv", [
        "llm4pv-synth",
        f"--FILE={c_file}",
        f"--OUTPUT_PATH={output_dir}",
        # Force the LLM-style pipeline so the mocked
        # ``run_synthesis_pipeline`` is exercised; default is now segcodegen,
        # which routes through ``run_segcodegen_pipeline`` instead.
        "--backend=command",
    ])

    synth_cli.main()

    assert calls["kwargs"]["input_path"] == str(c_file)
    assert calls["kwargs"]["output_dir"] == str(output_dir)
    captured = capsys.readouterr()
    assert "Status: passed" in captured.out


def test_synth_cli_directory_mode_uses_exclude_and_contexts(monkeypatch, tmp_path, capsys):
    input_dir = tmp_path / "inputs"
    output_dir = tmp_path / "outputs"
    input_dir.mkdir()
    (input_dir / "alpha.c").write_text("int alpha(void) { return 0; }\n", encoding="utf-8")
    (input_dir / "beta.c").write_text("int beta(void) { return 0; }\n", encoding="utf-8")

    monkeypatch.setattr(
        synth_cli,
        "collect_all_synthesis_contexts",
        lambda c_file, sibling_dirs=None: [
            {"id": "alpha", "summary": {"func_name": "alpha"}}
        ] if c_file.endswith("alpha.c") else [
            {"id": "beta_left", "summary": {"func_name": "beta_left"}},
            {"id": "beta_right", "summary": {"func_name": "beta_right"}},
        ],
    )

    seen = []

    def fake_run(**kwargs):
        seen.append((kwargs["input_path"], kwargs["func_name"], kwargs["output_dir"]))
        return {
            "status": "passed",
            "attempt_count": 1,
            "check": {"status": "passed"},
        }

    monkeypatch.setattr(synth_cli, "run_synthesis_pipeline", fake_run)
    monkeypatch.setattr(sys, "argv", [
        "llm4pv-synth",
        f"--C_DIR={input_dir}",
        f"--OUTPUT_PATH={output_dir}",
        "--exclude=alpha.c",
        "--backend=command",
    ])

    try:
        synth_cli.main()
    except SystemExit as exc:
        assert exc.code == 0

    assert seen == [
        (str(input_dir / "beta.c"), "beta_left", str(output_dir / "beta_left")),
        (str(input_dir / "beta.c"), "beta_right", str(output_dir / "beta_right")),
    ]
    captured = capsys.readouterr()
    assert f"Skipped: {input_dir / 'alpha.c'}" in captured.out
    assert "beta_left: passed (attempts=1, rocq=passed)" in captured.out
    assert "beta_right: passed (attempts=1, rocq=passed)" in captured.out


def test_synth_cli_directory_mode_parallelizes_per_c_file(monkeypatch, tmp_path, capsys):
    input_dir = tmp_path / "inputs"
    output_dir = tmp_path / "outputs"
    input_dir.mkdir()
    (input_dir / "alpha.c").write_text("int alpha(void) { return 0; }\n", encoding="utf-8")
    (input_dir / "beta.c").write_text("int beta(void) { return 0; }\n", encoding="utf-8")

    submitted = []
    seen = []

    class FakeFuture:
        def __init__(self, result):
            self._result = result

        def result(self):
            return self._result

    class FakeExecutor:
        def __init__(self, max_workers):
            self.max_workers = max_workers

        def __enter__(self):
            submitted.append(("workers", self.max_workers))
            return self

        def __exit__(self, exc_type, exc, tb):
            return False

        def submit(self, fn, c_file, output_dir_arg, args):
            submitted.append(("submit", c_file))
            return FakeFuture(fn(c_file, output_dir_arg, args))

    monkeypatch.setattr(synth_cli, "ThreadPoolExecutor", FakeExecutor)
    monkeypatch.setattr(synth_cli, "as_completed", lambda futures: futures)

    def fake_run_batch_for_file(c_file, output_dir_arg, args):
        seen.append((c_file, output_dir_arg, args.jobs))
        return [f"done {c_file}"], [], []

    monkeypatch.setattr(synth_cli, "_run_batch_for_file", fake_run_batch_for_file)
    monkeypatch.setattr(sys, "argv", [
        "llm4pv-synth",
        f"--C_DIR={input_dir}",
        f"--OUTPUT_PATH={output_dir}",
        "--jobs=2",
        "--backend=command",
    ])

    try:
        synth_cli.main()
    except SystemExit as exc:
        assert exc.code == 0

    assert submitted[0] == ("workers", 2)
    assert submitted[1:] == [
        ("submit", str(input_dir / "alpha.c")),
        ("submit", str(input_dir / "beta.c")),
    ]
    assert seen == [
        (str(input_dir / "alpha.c"), str(output_dir), 2),
        (str(input_dir / "beta.c"), str(output_dir), 2),
    ]
    captured = capsys.readouterr()
    assert f"done {input_dir / 'alpha.c'}" in captured.out
    assert f"done {input_dir / 'beta.c'}" in captured.out


def test_synth_cli_reports_precise_missing_output_error(monkeypatch, tmp_path, capsys):
    c_file = tmp_path / "demo.c"
    c_file.write_text("int demo(void) { return 0; }\n", encoding="utf-8")
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "llm4pv-synth",
            f"--FILE={c_file}",
            # Force the LLM-style path — segcodegen (the default) doesn't
            # require ``--OUTPUT_PATH`` because it writes straight into
            # ``--coq-lib-dir``.
            "--backend=command",
        ],
    )

    with pytest.raises(SystemExit) as excinfo:
        synth_cli.main()

    assert excinfo.value.code == 2
    captured = capsys.readouterr()
    assert "Provide an output directory via positional output_dir or --OUTPUT_PATH." in captured.err
    assert "--FILE/--C_DIR" not in captured.err
