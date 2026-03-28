import json
import os
import shutil
import subprocess
from typing import Dict, List, Optional, Tuple

from GenMonads.absprog.assemble import write_assembled_rel_lib
from GenMonads.absprog.check_rocq import check_rocq_file
from GenMonads.absprog.context import collect_synthesis_context, write_synthesis_context
from GenMonads.absprog.parse_coq import parse_synthesized_components
from GenMonads.absprog.templates import prompt_payload, render_prompt, render_repair_prompt


def _load_json(path: str) -> Dict:
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)


def _write_text(path: str, content: str) -> str:
    parent = os.path.dirname(path)
    if parent:
        os.makedirs(parent, exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        f.write(content)
    return path


def _write_json(path: str, content: Dict) -> str:
    parent = os.path.dirname(path)
    if parent:
        os.makedirs(parent, exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        json.dump(content, f, indent=2)
        f.write("\n")
    return path


def _replay_gold_response(example: Dict) -> str:
    gold = example.get("gold")
    if not gold:
        raise ValueError("Replay backend requires an example JSON with a gold section")

    components = gold.get("components", {})
    lines = [
        "```coq",
        f"Definition MretTy : Type := {gold['MretTy']}.",
        components["M_loop_before"],
        components["M_1"],
        components["M_2"],
        components["M_loop_end"],
        "```",
        "",
    ]
    return "\n".join(lines)


def _format_command(
    command: str,
    context: Dict,
    prompt_file: str,
    context_file: str,
    output_dir: str,
    response_file: str,
) -> str:
    return command.format(
        prompt_file=prompt_file,
        context_file=context_file,
        output_dir=output_dir,
        response_file=response_file,
        context_id=context["id"],
        func_name=context["summary"]["func_name"],
        c_file=context["source"]["c_file"],
    )


def _run_command_backend(
    command: str,
    prompt_text: str,
    context: Dict,
    prompt_file: str,
    context_file: str,
    output_dir: str,
    response_file: str,
) -> str:
    formatted = _format_command(
        command, context, prompt_file, context_file, output_dir, response_file
    )
    proc = subprocess.run(
        formatted,
        shell=True,
        text=True,
        input=prompt_text,
        capture_output=True,
    )
    if proc.returncode != 0:
        detail = proc.stderr.strip() or proc.stdout.strip() or f"exit code {proc.returncode}"
        raise ValueError(f"Command backend failed: {detail}")
    if os.path.isfile(response_file):
        with open(response_file, "r", encoding="utf-8") as f:
            return f.read()
    return proc.stdout


def generate_candidate_response(
    context: Dict,
    backend: str,
    prompt_text: str,
    prompt_file: str,
    context_file: str,
    output_dir: str,
    backend_response_file: str,
    replay_from: Optional[str] = None,
    response_file: Optional[str] = None,
    command: Optional[str] = None,
) -> str:
    if backend == "gold-example":
        if replay_from:
            example = _load_json(replay_from)
        else:
            example = context
        return _replay_gold_response(example)

    if backend == "response-file":
        if not response_file:
            raise ValueError("response-file backend requires --response-file")
        with open(response_file, "r", encoding="utf-8") as f:
            return f.read()

    if backend == "command":
        if not command:
            raise ValueError("command backend requires --command")
        return _run_command_backend(
            command=command,
            prompt_text=prompt_text,
            context=context,
            prompt_file=prompt_file,
            context_file=context_file,
            output_dir=output_dir,
            response_file=backend_response_file,
        )

    raise ValueError(f"Unsupported backend: {backend}")


def _default_check_result() -> Dict:
    return {
        "status": "skipped",
        "passed": False,
        "reason": "check disabled",
        "stdout": "",
        "stderr": "",
    }


def _validate_opaque_callee_usage(context: Dict, response_text: str) -> None:
    required_programs = context.get("generation_policy", {}).get("opaque_external_programs", [])
    missing = []
    for name in required_programs:
        if name not in response_text:
            missing.append(name)

    if missing:
        obligations = context.get("opaque_call_obligations", [])
        detail_lines = [
            "Missing required opaque callee program(s) in synthesized response:",
            ", ".join(missing),
        ]
        if obligations:
            detail_lines.append("Required opaque call obligations:")
            for obligation in obligations:
                if obligation["callee"] in missing:
                    detail_lines.append(
                        f"- {obligation['call_site']} -> {obligation['callee']}"
                    )
        raise ValueError("\n".join(detail_lines))


def _validate_early_return_scaffold(context: Dict, response_text: str) -> None:
    control_flow = context.get("control_flow") or context.get("target", {}).get("control_flow", {})
    if not control_flow.get("needs_early_result"):
        return

    if "early_result" not in response_text:
        detail_lines = [
            "Missing early-return-aware scaffold in synthesized response.",
            f"Template case: {control_flow.get('template_case', 'unknown')}",
            "Expected the generated definitions to mention `early_result`.",
        ]
        raise ValueError("\n".join(detail_lines))


def _attempt_dir(output_dir: str, attempt_index: int) -> str:
    return os.path.join(output_dir, f"attempt-{attempt_index}")


def _attempt_file(attempt_dir: str, context_id: str, suffix: str) -> str:
    return os.path.join(attempt_dir, f"{context_id}.{suffix}")


def _root_file(output_dir: str, context_id: str, suffix: str) -> str:
    return os.path.join(output_dir, f"{context_id}.{suffix}")


def _default_coq_lib_dir() -> str:
    env = os.environ.get("COQ_LIB_DIR")
    if env:
        return env

    configure = os.path.join(os.path.dirname(__file__), "..", "..", "CONFIGURE")
    configure = os.path.normpath(configure)
    if os.path.isfile(configure):
        with open(configure, "r", encoding="utf-8") as f:
            for line in f:
                line = line.strip()
                if line.startswith("COQ_LIB_DIR="):
                    value = line.split(":-", 1)[-1].rstrip('}"')
                    if value:
                        return value
    return os.path.join("output", "gen", "libs")


def _promote_rel_lib_if_accepted(assembled_file: str, context_id: str, status: str) -> str:
    if status != "passed" or not assembled_file or not os.path.isfile(assembled_file):
        return ""

    target_dir = _default_coq_lib_dir()
    os.makedirs(target_dir, exist_ok=True)
    source_root, _ = os.path.splitext(assembled_file)
    target_root = os.path.join(target_dir, f"{context_id}_rel_lib")
    for ext in [".v", ".vo", ".vok", ".vos", ".glob"]:
        source = f"{source_root}{ext}"
        if os.path.isfile(source):
            shutil.copyfile(source, f"{target_root}{ext}")
    target_path = f"{target_root}.v"
    return target_path


def _final_status_from_attempt(attempt: Dict) -> str:
    if attempt["status"] == "passed":
        return "passed"
    if attempt["status"] == "assembled":
        return "assembled"
    return "failed"


def _build_attempt_summary(
    attempt_index: int,
    files: Dict[str, str],
    status: str,
    failure_kind: str,
    failure_message: str,
    check_result: Dict,
) -> Dict:
    return {
        "attempt": attempt_index,
        "status": status,
        "failure_kind": failure_kind,
        "failure_message": failure_message,
        "files": files,
        "check": check_result,
    }


def _copy_final_attempt_files(final_attempt: Dict, output_dir: str, context_id: str) -> Dict[str, str]:
    final_files = {}
    for label, path in final_attempt["files"].items():
        if not path:
            continue
        if label == "context":
            final_files[label] = path
            continue

        if label == "assembled_rel_lib":
            target = os.path.join(output_dir, f"{context_id}_rel_lib.v")
        elif label == "summary":
            target = os.path.join(output_dir, f"{context_id}.summary.json")
        else:
            suffix = os.path.basename(path).split(f"{context_id}.", 1)[-1]
            target = _root_file(output_dir, context_id, suffix)

        with open(path, "r", encoding="utf-8") as src:
            _write_text(target, src.read())
        final_files[label] = target
    return final_files


def run_synthesis_pipeline(
    input_path: str,
    output_dir: str,
    func_name: Optional[str] = None,
    backend: str = "gold-example",
    replay_from: Optional[str] = None,
    response_file: Optional[str] = None,
    command: Optional[str] = None,
    few_shot_paths: Optional[List[str]] = None,
    run_check: bool = True,
    max_retries: int = 0,
) -> Dict:
    os.makedirs(output_dir, exist_ok=True)

    if input_path.endswith(".json"):
        context = _load_json(input_path)
        context_file = input_path
    else:
        context = collect_synthesis_context(input_path, func_name=func_name)
        context_file = _root_file(output_dir, context["id"], "context.auto.json")
        write_synthesis_context(input_path, context_file, func_name=func_name)

    examples = [_load_json(path) for path in (few_shot_paths or [])]
    base_prompt = render_prompt(context, examples)
    attempts: List[Dict] = []
    previous_response = ""
    previous_failure_kind = ""
    previous_failure_message = ""
    total_attempts = max_retries + 1

    for attempt_index in range(total_attempts):
        attempt_dir = _attempt_dir(output_dir, attempt_index)
        os.makedirs(attempt_dir, exist_ok=True)

        if attempt_index == 0:
            prompt = base_prompt
        else:
            prompt = render_repair_prompt(
                context,
                previous_response=previous_response,
                failure_kind=previous_failure_kind,
                failure_message=previous_failure_message,
                few_shot_examples=examples,
            )

        prompt_file = _attempt_file(attempt_dir, context["id"], "prompt.txt")
        prompt_payload_file = _attempt_file(attempt_dir, context["id"], "prompt.json")
        backend_response_file = _attempt_file(attempt_dir, context["id"], "backend-response.txt")
        response_out_file = _attempt_file(attempt_dir, context["id"], "response.txt")
        parsed_file = _attempt_file(attempt_dir, context["id"], "parsed.json")
        assembled_file = os.path.join(attempt_dir, f"{context['id']}_rel_lib.v")

        _write_text(prompt_file, prompt)
        _write_json(prompt_payload_file, prompt_payload(context, prompt, few_shot_paths))

        files = {
            "context": context_file,
            "prompt": prompt_file,
            "prompt_payload": prompt_payload_file,
            "response": response_out_file,
            "parsed": "",
            "assembled_rel_lib": "",
        }

        check_result = _default_check_result()
        failure_kind = ""
        failure_message = ""
        status = "failed"

        try:
            response_text = generate_candidate_response(
                context,
                backend=backend,
                prompt_text=prompt,
                prompt_file=prompt_file,
                context_file=context_file,
                output_dir=attempt_dir,
                backend_response_file=backend_response_file,
                replay_from=replay_from,
                response_file=response_file,
                command=command,
            )
        except Exception as exc:
            response_text = ""
            failure_kind = "backend"
            failure_message = str(exc)
            _write_text(response_out_file, response_text)
            attempt_summary = _build_attempt_summary(
                attempt_index, files, status, failure_kind, failure_message, check_result
            )
            attempt_summary_file = _attempt_file(attempt_dir, context["id"], "summary.json")
            _write_json(attempt_summary_file, attempt_summary)
            attempt_summary["files"]["summary"] = attempt_summary_file
            attempts.append(attempt_summary)
            previous_response = response_text
            previous_failure_kind = failure_kind
            previous_failure_message = failure_message
            continue

        _write_text(response_out_file, response_text)

        try:
            _validate_opaque_callee_usage(context, response_text)
            _validate_early_return_scaffold(context, response_text)
        except Exception as exc:
            failure_kind = "validation"
            failure_message = str(exc)
            attempt_summary = _build_attempt_summary(
                attempt_index, files, status, failure_kind, failure_message, check_result
            )
            attempt_summary_file = _attempt_file(attempt_dir, context["id"], "summary.json")
            _write_json(attempt_summary_file, attempt_summary)
            attempt_summary["files"]["summary"] = attempt_summary_file
            attempts.append(attempt_summary)
            previous_response = response_text
            previous_failure_kind = failure_kind
            previous_failure_message = failure_message
            continue

        try:
            blocks = parse_synthesized_components(response_text, context["summary"]["func_name"])
            _write_json(parsed_file, blocks)
            files["parsed"] = parsed_file
        except Exception as exc:
            failure_kind = "parse"
            failure_message = str(exc)
            attempt_summary = _build_attempt_summary(
                attempt_index, files, status, failure_kind, failure_message, check_result
            )
            attempt_summary_file = _attempt_file(attempt_dir, context["id"], "summary.json")
            _write_json(attempt_summary_file, attempt_summary)
            attempt_summary["files"]["summary"] = attempt_summary_file
            attempts.append(attempt_summary)
            previous_response = response_text
            previous_failure_kind = failure_kind
            previous_failure_message = failure_message
            continue

        write_assembled_rel_lib(
            context["source"]["c_file"],
            context["summary"]["func_name"],
            blocks,
            assembled_file,
        )
        files["assembled_rel_lib"] = assembled_file

        if run_check:
            check_result = check_rocq_file(assembled_file)

        if not run_check or check_result.get("status") == "passed":
            status = "passed" if run_check else "assembled"
            attempt_summary = _build_attempt_summary(
                attempt_index, files, status, failure_kind, failure_message, check_result
            )
            attempt_summary_file = _attempt_file(attempt_dir, context["id"], "summary.json")
            _write_json(attempt_summary_file, attempt_summary)
            attempt_summary["files"]["summary"] = attempt_summary_file
            attempts.append(attempt_summary)
            final_files = _copy_final_attempt_files(attempt_summary, output_dir, context["id"])
            summary = {
                "input_path": input_path,
                "context_id": context["id"],
                "func_name": context["summary"]["func_name"],
                "backend": backend,
                "max_retries": max_retries,
                "attempt_count": len(attempts),
                "attempts": attempts,
                "files": final_files,
                "check": check_result,
                "status": status,
            }
            promoted_path = _promote_rel_lib_if_accepted(
                attempt_summary["files"].get("assembled_rel_lib", ""), context["id"], status
            )
            if promoted_path:
                summary["files"]["promoted_rel_lib"] = promoted_path
            summary_file = _root_file(output_dir, context["id"], "summary.json")
            _write_json(summary_file, summary)
            summary["files"]["summary"] = summary_file
            return summary

        failure_kind = "rocq"
        failure_message = check_result.get("stderr") or check_result.get("stdout") or "Rocq check failed"
        attempt_summary = _build_attempt_summary(
            attempt_index, files, status, failure_kind, failure_message, check_result
        )
        attempt_summary_file = _attempt_file(attempt_dir, context["id"], "summary.json")
        _write_json(attempt_summary_file, attempt_summary)
        attempt_summary["files"]["summary"] = attempt_summary_file
        attempts.append(attempt_summary)
        previous_response = response_text
        previous_failure_kind = failure_kind
        previous_failure_message = failure_message

    final_attempt = attempts[-1]
    final_files = _copy_final_attempt_files(final_attempt, output_dir, context["id"])
    summary = {
        "input_path": input_path,
        "context_id": context["id"],
        "func_name": context["summary"]["func_name"],
        "backend": backend,
        "max_retries": max_retries,
        "attempt_count": len(attempts),
        "attempts": attempts,
        "files": final_files,
        "check": final_attempt["check"],
        "status": _final_status_from_attempt(final_attempt),
    }
    promoted_path = _promote_rel_lib_if_accepted(
        final_attempt["files"].get("assembled_rel_lib", ""), context["id"], summary["status"]
    )
    if promoted_path:
        summary["files"]["promoted_rel_lib"] = promoted_path
    summary_file = _root_file(output_dir, context["id"], "summary.json")
    _write_json(summary_file, summary)
    summary["files"]["summary"] = summary_file
    return summary
