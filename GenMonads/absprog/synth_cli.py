"""CLI for the abstract-program synthesis pipeline."""

import argparse
import sys

from GenMonads.absprog.synthesize import run_synthesis_pipeline


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Run the abstract-program synthesis pipeline and emit artifacts"
    )
    parser.add_argument("input", help="Input C file or context JSON")
    parser.add_argument("output_dir", help="Directory for generated artifacts")
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
    args = parser.parse_args()

    try:
        summary = run_synthesis_pipeline(
            input_path=args.input,
            output_dir=args.output_dir,
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
