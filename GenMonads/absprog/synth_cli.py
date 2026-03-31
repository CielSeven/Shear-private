"""CLI for the abstract-program synthesis pipeline."""

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import os
import sys

from GenMonads.absprog.context import collect_all_synthesis_contexts
from GenMonads.absprog.synthesize import run_synthesis_pipeline


def _resolve_io(args, parser):
    input_path = args.input or args.c_dir
    output_dir = args.output_dir or args.output_path
    if not input_path or not output_dir:
        parser.error("Provide either positional input/output_dir or --C_DIR/--OUTPUT_PATH.")
    return input_path, output_dir


def _is_excluded(path: str, excludes) -> bool:
    name = os.path.basename(path)
    stem = os.path.splitext(name)[0]
    return name in excludes or stem in excludes


def _run_batch_for_file(c_file: str, output_dir: str, args):
    stdout_lines = []
    stderr_lines = []
    failures = []

    try:
        contexts = collect_all_synthesis_contexts(c_file)
    except Exception as exc:
        stderr_lines.append(f"Failed: {c_file} ({exc})")
        failures.append(c_file)
        return stdout_lines, stderr_lines, failures

    for context in contexts:
        func_name = context["summary"]["func_name"]
        target_dir = os.path.join(output_dir, context["id"])
        try:
            summary = run_synthesis_pipeline(
                input_path=c_file,
                output_dir=target_dir,
                func_name=func_name,
                backend=args.backend,
                replay_from=args.replay_from,
                response_file=args.response_file,
                command=args.command,
                few_shot_paths=args.few_shot,
                run_check=not args.no_check,
                max_retries=args.max_retries,
            )
        except Exception as exc:
            stderr_lines.append(f"Failed: {context['id']} ({exc})")
            failures.append(context["id"])
            continue

        stdout_lines.append(
            f"{context['id']}: {summary['status']} "
            f"(attempts={summary['attempt_count']}, rocq={summary['check']['status']})"
        )

    return stdout_lines, stderr_lines, failures


def _run_batch(input_dir: str, output_dir: str, args) -> int:
    excludes = set(args.exclude or [])
    failures = []
    c_files = []
    for name in sorted(os.listdir(input_dir)):
        if not name.endswith(".c"):
            continue
        c_file = os.path.join(input_dir, name)
        if _is_excluded(c_file, excludes):
            print(f"Skipped: {c_file}")
            continue
        c_files.append(c_file)

    jobs = max(1, args.jobs)
    if jobs == 1:
        for c_file in c_files:
            stdout_lines, stderr_lines, batch_failures = _run_batch_for_file(c_file, output_dir, args)
            for line in stdout_lines:
                print(line)
            for line in stderr_lines:
                print(line, file=sys.stderr)
            failures.extend(batch_failures)
        return 1 if failures else 0

    with ThreadPoolExecutor(max_workers=jobs) as executor:
        future_map = {
            executor.submit(_run_batch_for_file, c_file, output_dir, args): c_file
            for c_file in c_files
        }
        for future in as_completed(future_map):
            stdout_lines, stderr_lines, batch_failures = future.result()
            if stdout_lines:
                sys.stdout.write("\n".join(stdout_lines) + "\n")
                sys.stdout.flush()
            if stderr_lines:
                sys.stderr.write("\n".join(stderr_lines) + "\n")
                sys.stderr.flush()
            failures.extend(batch_failures)

    return 1 if failures else 0


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Run the abstract-program synthesis pipeline and emit artifacts"
    )
    parser.add_argument("input", nargs="?", help="Input C file, context JSON, or directory")
    parser.add_argument("output_dir", nargs="?", help="Directory for generated artifacts")
    parser.add_argument(
        "--C_DIR",
        dest="c_dir",
        help="Input C file or directory (alias-style convenience flag)",
    )
    parser.add_argument(
        "--OUTPUT_PATH",
        dest="output_path",
        help="Output directory (alias-style convenience flag)",
    )
    parser.add_argument(
        "--func-name",
        help="Function name for multi-function C files",
    )
    parser.add_argument(
        "--backend",
        choices=["gold-example", "response-file", "command"],
        default="gold-example",
        help="Generation backend",
    )
    parser.add_argument(
        "--replay-from",
        help="Auto-example JSON to replay when using the gold-example backend",
    )
    parser.add_argument(
        "--response-file",
        help="Raw LLM response file to parse when using the response-file backend",
    )
    parser.add_argument(
        "--command",
        help=(
            "Shell command for the command backend. The rendered prompt is sent on stdin. "
            "You may also use placeholders like {prompt_file}, {context_file}, {response_file}, "
            "{output_dir}, {context_id}, {func_name}, and {c_file}."
        ),
    )
    parser.add_argument(
        "--few-shot",
        action="append",
        default=[],
        help="Few-shot example JSON to embed into the prompt (repeatable)",
    )
    parser.add_argument(
        "--no-check",
        action="store_true",
        help="Skip the Rocq syntax check step",
    )
    parser.add_argument(
        "--max-retries",
        type=int,
        default=0,
        help="Number of repair attempts after the initial generation attempt",
    )
    parser.add_argument(
        "--exclude",
        action="append",
        default=[],
        help="Exclude a C basename or filename in directory mode (repeatable)",
    )
    parser.add_argument(
        "-j",
        "--jobs",
        type=int,
        default=1,
        help="Number of C-file workers to run in parallel in directory mode",
    )
    args = parser.parse_args()
    input_path, output_dir = _resolve_io(args, parser)

    if os.path.isdir(input_path):
        sys.exit(_run_batch(input_path, output_dir, args))

    try:
        summary = run_synthesis_pipeline(
            input_path=input_path,
            output_dir=output_dir,
            func_name=args.func_name,
            backend=args.backend,
            replay_from=args.replay_from,
            response_file=args.response_file,
            command=args.command,
            few_shot_paths=args.few_shot,
            run_check=not args.no_check,
            max_retries=args.max_retries,
        )
    except Exception as exc:
        print(str(exc), file=sys.stderr)
        sys.exit(1)

    print(f"Status: {summary['status']}")
    for label, path in summary["files"].items():
        print(f"{label}: {path}")
    check = summary["check"]
    print(f"rocq_check: {check['status']}")
    if check.get("reason"):
        print(f"rocq_reason: {check['reason']}")


if __name__ == "__main__":
    main()
