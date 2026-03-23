import json
import subprocess

from GenMonads.absprog.assemble import assemble_rel_lib_from_blocks
from GenMonads.absprog.parse_coq import parse_synthesized_components
from GenMonads.absprog.synthesize import generate_candidate_response, run_synthesis_pipeline
from GenMonads.absprog.templates import render_prompt, render_repair_prompt


def _load_example():
    with open("few-shot-examples/absprog/sll_reverse.auto.json", "r", encoding="utf-8") as f:
        return json.load(f)


def test_render_prompt_uses_actual_context_schema():
    example = _load_example()

    prompt = render_prompt(example, [example])

    assert "Function: sll_reverse" in prompt
    assert "Require with safeExec: safeExec(ATrue, sll_reverse_M(l1), X) && sll(head, l1)" in prompt
    assert "M_loop_before: list Z -> MONAD (list Z * list Z)" in prompt
    assert "### Example: sll_reverse" in prompt
    assert "Definition MretTy : Type := list Z." in prompt


def test_render_repair_prompt_includes_failure_feedback():
    example = _load_example()

    prompt = render_repair_prompt(
        example,
        previous_response="Definition broken := True.",
        failure_kind="parse",
        failure_message="Could not find Definition 'foo'",
        few_shot_examples=[example],
    )

    assert "## Repair Feedback" in prompt
    assert "Failure kind: parse" in prompt
    assert "Could not find Definition 'foo'" in prompt
    assert "Definition broken := True." in prompt


def test_parse_synthesized_components_extracts_blocks_from_response():
    response = """```coq
Definition MretTy : Type := list Z.
Definition sll_reverse_M_loop_before : list Z -> MONAD (list Z * list Z) :=
  fun l => return (nil, l).
Definition sll_reverse_M_loop_M1 : (list Z * list Z) -> MONAD MretTy:=
  fun '(l1,l2) => return l1.
Definition sll_reverse_M_loop_M2 : (list Z * list Z) -> MONAD (list Z * list Z) :=
  fun '(l1,l2) =>
    match l2 with
    | nil => return (l1,l2)
    | v :: l2' => return (v :: l1, l2')
    end.
Definition sll_reverse_M_loop_end : MretTy -> MONAD (list Z):=
  fun l => return l.
```"""

    blocks = parse_synthesized_components(response, "sll_reverse")

    assert blocks["MretTy"] == "Definition MretTy : Type := list Z."
    assert "Definition sll_reverse_M_loop_before" in blocks["M_loop_before"]
    assert "Definition sll_reverse_M_loop_M1" in blocks["M_1"]
    assert "Definition sll_reverse_M_loop_M2" in blocks["M_2"]
    assert "Definition sll_reverse_M_loop_end" in blocks["M_loop_end"]


def test_parse_synthesized_components_accepts_multiline_definition_headers():
    response = """```coq
Definition MretTy : Type := (list Z * list Z)%type.

Definition sll_copy_double_M_loop_before
  : list Z -> MONAD (list Z * list Z * list Z) :=
  fun l => return (nil, l, nil).

Definition sll_copy_double_M_loop_M1
  : (list Z * list Z * list Z) -> MONAD MretTy :=
  fun '(l1, l2, l3) => return (l3, l1).

Definition sll_copy_double_M_loop_M2
  : (list Z * list Z * list Z) -> MONAD (list Z * list Z * list Z) :=
  fun '(l1, l2, l3) => return (l1, l2, l3).

Definition sll_copy_double_M_loop_end
  : MretTy -> MONAD (list Z * list Z) :=
  fun r => return r.
```"""

    blocks = parse_synthesized_components(response, "sll_copy_double")

    assert "Definition sll_copy_double_M_loop_before" in blocks["M_loop_before"]
    assert "Definition sll_copy_double_M_loop_M1" in blocks["M_1"]
    assert "Definition sll_copy_double_M_loop_M2" in blocks["M_2"]
    assert "Definition sll_copy_double_M_loop_end" in blocks["M_loop_end"]


def test_assemble_rel_lib_from_blocks_replaces_parameters():
    example = _load_example()
    blocks = {"MretTy": f"Definition MretTy : Type := {example['gold']['MretTy']}."}
    blocks.update(example["gold"]["components"])

    content = assemble_rel_lib_from_blocks(
        "shape_invdataset/sll/sll_reverse.c",
        "sll_reverse",
        blocks,
    )

    assert "Parameter MretTy : Type." not in content
    assert "Parameter sll_reverse_M_loop_before" not in content
    assert "Definition MretTy : Type := list Z." in content
    assert "Definition sll_reverse_M_loop_before : list Z -> MONAD (list Z * list Z) :=" in content
    assert "Definition sll_reverse_M_loop_M1 : (list Z * list Z) -> MONAD MretTy:=" in content


def test_run_synthesis_pipeline_replay_backend_writes_artifacts(tmp_path):
    output_dir = tmp_path / "synth"

    summary = run_synthesis_pipeline(
        input_path="few-shot-examples/absprog/sll_reverse.auto.json",
        output_dir=str(output_dir),
        backend="gold-example",
        few_shot_paths=["few-shot-examples/absprog/sll_reverse.auto.json"],
        run_check=False,
    )

    assert summary["status"] == "assembled"
    files = summary["files"]
    assert (output_dir / "sll_reverse.prompt.txt").exists()
    assert (output_dir / "sll_reverse.response.txt").exists()
    assert (output_dir / "sll_reverse.parsed.json").exists()
    assert (output_dir / "sll_reverse_rel_lib.v").exists()
    assert files["context"] == "few-shot-examples/absprog/sll_reverse.auto.json"

    assembled = (output_dir / "sll_reverse_rel_lib.v").read_text(encoding="utf-8")
    assert "Definition MretTy : Type := list Z." in assembled
    assert "Definition sll_reverse_M_loop_M2 : (list Z * list Z) -> MONAD (list Z * list Z) :=" in assembled

    summary_json = json.loads((output_dir / "sll_reverse.summary.json").read_text(encoding="utf-8"))
    assert summary_json["check"]["status"] == "skipped"


def test_generate_candidate_response_command_backend_uses_stdin_and_placeholders(monkeypatch, tmp_path):
    example = _load_example()
    prompt_file = tmp_path / "prompt.txt"
    context_file = tmp_path / "context.json"
    prompt_text = "PROMPT CONTENT"

    seen = {}

    def fake_run(cmd, shell, text, input, capture_output):
        seen["cmd"] = cmd
        seen["shell"] = shell
        seen["text"] = text
        seen["input"] = input
        seen["capture_output"] = capture_output
        return subprocess.CompletedProcess(
            args=cmd,
            returncode=0,
            stdout="```coq\nDefinition MretTy : Type := list Z.\n```",
            stderr="",
        )

    monkeypatch.setattr("GenMonads.absprog.synthesize.subprocess.run", fake_run)

    response = generate_candidate_response(
        example,
        backend="command",
        prompt_text=prompt_text,
        prompt_file=str(prompt_file),
        context_file=str(context_file),
        output_dir=str(tmp_path),
        backend_response_file=str(tmp_path / "backend.txt"),
        command="echo using {prompt_file} for {func_name}",
    )

    assert "Definition MretTy" in response
    assert seen["input"] == prompt_text
    assert seen["shell"] is True
    assert str(prompt_file) in seen["cmd"]
    assert "sll_reverse" in seen["cmd"]


def test_run_synthesis_pipeline_command_backend_writes_artifacts(monkeypatch, tmp_path):
    example = _load_example()
    output_dir = tmp_path / "synth"
    response_text = "\n".join(
        [
            "```coq",
            f"Definition MretTy : Type := {example['gold']['MretTy']}.",
            example["gold"]["components"]["M_loop_before"],
            example["gold"]["components"]["M_1"],
            example["gold"]["components"]["M_2"],
            example["gold"]["components"]["M_loop_end"],
            "```",
            "",
        ]
    )

    def fake_run(cmd, shell, text, input, capture_output):
        return subprocess.CompletedProcess(
            args=cmd,
            returncode=0,
            stdout=response_text,
            stderr="",
        )

    monkeypatch.setattr("GenMonads.absprog.synthesize.subprocess.run", fake_run)

    summary = run_synthesis_pipeline(
        input_path="few-shot-examples/absprog/sll_reverse.auto.json",
        output_dir=str(output_dir),
        backend="command",
        command="codex exec",
        run_check=False,
    )

    assert summary["status"] == "assembled"
    assembled = (output_dir / "sll_reverse_rel_lib.v").read_text(encoding="utf-8")
    assert "Definition sll_reverse_M_loop_before" in assembled


def test_run_synthesis_pipeline_retries_after_parse_failure(monkeypatch, tmp_path):
    example = _load_example()
    output_dir = tmp_path / "repair-parse"
    responses = iter(
        [
            "```coq\nDefinition MretTy : Type := list Z.\n```",
            "\n".join(
                [
                    "```coq",
                    f"Definition MretTy : Type := {example['gold']['MretTy']}.",
                    example["gold"]["components"]["M_loop_before"],
                    example["gold"]["components"]["M_1"],
                    example["gold"]["components"]["M_2"],
                    example["gold"]["components"]["M_loop_end"],
                    "```",
                    "",
                ]
            ),
        ]
    )

    def fake_generate(*_args, **_kwargs):
        return next(responses)

    monkeypatch.setattr("GenMonads.absprog.synthesize.generate_candidate_response", fake_generate)

    summary = run_synthesis_pipeline(
        input_path="few-shot-examples/absprog/sll_reverse.auto.json",
        output_dir=str(output_dir),
        backend="command",
        command="codex exec",
        run_check=False,
        max_retries=1,
    )

    assert summary["status"] == "assembled"
    assert summary["attempt_count"] == 2
    assert summary["attempts"][0]["failure_kind"] == "parse"
    assert summary["attempts"][1]["status"] == "assembled"

    repair_prompt = (output_dir / "attempt-1" / "sll_reverse.prompt.txt").read_text(encoding="utf-8")
    assert "## Repair Feedback" in repair_prompt
    assert "Failure kind: parse" in repair_prompt


def test_run_synthesis_pipeline_retries_after_rocq_failure(monkeypatch, tmp_path):
    example = _load_example()
    output_dir = tmp_path / "repair-rocq"
    response_text = "\n".join(
        [
            "```coq",
            f"Definition MretTy : Type := {example['gold']['MretTy']}.",
            example["gold"]["components"]["M_loop_before"],
            example["gold"]["components"]["M_1"],
            example["gold"]["components"]["M_2"],
            example["gold"]["components"]["M_loop_end"],
            "```",
            "",
        ]
    )
    checks = iter(
        [
            {
                "status": "failed",
                "passed": False,
                "reason": "",
                "stdout": "",
                "stderr": "Syntax error on line 12",
                "returncode": 1,
            },
            {
                "status": "passed",
                "passed": True,
                "reason": "",
                "stdout": "",
                "stderr": "",
                "returncode": 0,
            },
        ]
    )

    monkeypatch.setattr(
        "GenMonads.absprog.synthesize.generate_candidate_response",
        lambda *_args, **_kwargs: response_text,
    )
    monkeypatch.setattr(
        "GenMonads.absprog.synthesize.check_rocq_file",
        lambda _path: next(checks),
    )

    summary = run_synthesis_pipeline(
        input_path="few-shot-examples/absprog/sll_reverse.auto.json",
        output_dir=str(output_dir),
        backend="command",
        command="codex exec",
        run_check=True,
        max_retries=1,
    )

    assert summary["status"] == "passed"
    assert summary["attempt_count"] == 2
    assert summary["attempts"][0]["failure_kind"] == "rocq"
    assert summary["attempts"][1]["status"] == "passed"

    repair_prompt = (output_dir / "attempt-1" / "sll_reverse.prompt.txt").read_text(encoding="utf-8")
    assert "Failure kind: rocq" in repair_prompt
    assert "Syntax error on line 12" in repair_prompt
