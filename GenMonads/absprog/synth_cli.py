"""CLI for the abstract-program synthesis pipeline."""

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import os
import sys

from GenMonads.absprog.assemble import merge_rel_libs_into_file
from GenMonads.absprog.context import collect_all_synthesis_contexts
from GenMonads.absprog.synthesize import (
    _default_coq_lib_dir,
    _eliminate_mretty_in_rel_c,
    _extract_mretty_type,
    run_synthesis_pipeline,
)
from GenMonads.cli_common import (
    add_input_path_arguments,
    add_output_path_argument,
    resolve_cli_value,
)


def _resolve_io(args, parser):
    input_path = resolve_cli_value(
        args,
        parser,
        "input",
        ("file_path", "c_dir"),
        "Provide an input path via positional input, --FILE, or --C_DIR.",
        is_path=True,
    )
    output_dir = resolve_cli_value(
        args,
        parser,
        "output_dir",
        ("output_path",),
        "Provide an output directory via positional output_dir or --OUTPUT_PATH.",
        is_path=True,
    )
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
        contexts = collect_all_synthesis_contexts(
            c_file, sibling_dirs=(args.sibling_dir or None)
        )
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
                command_timeout=(args.command_timeout or None),
                sibling_dirs=(args.sibling_dir or None),
                monad=args.monad,
                coq_lib_dir=args.coq_lib_dir,
                use_block_renderer=args.use_block_renderer,
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
    add_input_path_arguments(parser, "Input C file, context JSON, or directory")
    add_output_path_argument(parser, "output_dir", "Directory for generated artifacts")
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
            "Deprecated.  Workdir-mode owns the codex invocation now; this "
            "flag is ignored.  The codex CLI must be on PATH."
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
    from GenMonads.absprog.synthesize import DEFAULT_COMMAND_TIMEOUT_SECONDS
    parser.add_argument(
        "--command-timeout",
        type=int,
        default=DEFAULT_COMMAND_TIMEOUT_SECONDS,
        help=(
            f"Timeout (in seconds) for each command-backend invocation. "
            f"Default {DEFAULT_COMMAND_TIMEOUT_SECONDS}s.  Pass 0 to disable."
        ),
    )
    parser.add_argument(
        "--sibling-dir",
        action="append",
        default=[],
        help=(
            "Directory to search for sibling callee .c files (repeatable). "
            "Replaces the default of the input file's own directory."
        ),
    )
    parser.add_argument(
        "--coq-lib-dir",
        default=None,
        help=(
            "Directory holding already-synthesized peer _rel_lib.v files. "
            "When set, overrides COQ_LIB_DIR for the workdir pre-spawn check "
            "that verifies every cross-file callee lib is on disk."
        ),
    )
    parser.add_argument(
        "--use-block-renderer", action="store_true", default=False,
        help=(
            "Phase 2 feature flag.  Must match the value used at lib "
            "generation time; otherwise the must_define list and the "
            "skeleton's Parameter/Definition shape will disagree."
        ),
    )
    parser.add_argument(
        "--monad",
        choices=["staterel", "staterr"],
        default="staterel",
        help=(
            "Monad backend for the generated rel_lib: 'staterel' (StateRelMonad, "
            "default) or 'staterr' (error-aware MonadErr)."
        ),
    )
    parser.add_argument(
        "--exclude",
        action="append",
        default=[],
        help="Exclude a C basename or filename in directory mode (repeatable)",
    )
    parser.add_argument(
        "--patch-rel-c",
        action="store_true",
        help=(
            "After synthesis, eliminate the opaque MretTy placeholder in the target "
            "_rel.c file and append residual program signatures. Requires --rel-c-path."
        ),
    )
    parser.add_argument(
        "--rel-c-path",
        help=(
            "Path to the _rel.c file to patch. Required when --patch-rel-c is set. "
            "Not supported in directory mode."
        ),
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

    if args.patch_rel_c and not args.rel_c_path:
        parser.error("--patch-rel-c requires --rel-c-path")
    if args.rel_c_path and not args.patch_rel_c:
        parser.error("--rel-c-path requires --patch-rel-c")

    if os.path.isdir(input_path):
        if args.patch_rel_c:
            parser.error("--patch-rel-c is not supported in directory mode")
        sys.exit(_run_batch(input_path, output_dir, args))

    # Single-file mode: if --func-name is omitted and the file has multiple
    # functions, synthesize each one into its own subdirectory.
    if not args.func_name and input_path.endswith(".c"):
        try:
            contexts = collect_all_synthesis_contexts(
                input_path, sibling_dirs=(args.sibling_dir or None)
            )
        except Exception as exc:
            print(str(exc), file=sys.stderr)
            sys.exit(1)

        # When the file has exactly one synthesizable target but multiple
        # detected functions (e.g. a callee declaration), pick the lone
        # target explicitly so the single-call path doesn't trip the
        # "Function name is required for multi-function files" guard.
        if len(contexts) == 1:
            args.func_name = contexts[0]["summary"]["func_name"]

        if len(contexts) > 1:
            failures = []
            passed_assembled_paths = []
            mretty_by_func = {}
            for context in contexts:
                func_name = context["summary"]["func_name"]
                target_dir = os.path.join(output_dir, context["id"])
                print(f"\n=== {context['id']} ({func_name}) ===")
                try:
                    summary = run_synthesis_pipeline(
                        input_path=input_path,
                        output_dir=target_dir,
                        func_name=func_name,
                        backend=args.backend,
                        replay_from=args.replay_from,
                        response_file=args.response_file,
                        command=args.command,
                        few_shot_paths=args.few_shot,
                        run_check=not args.no_check,
                        max_retries=args.max_retries,
                        command_timeout=(args.command_timeout or None),
                        sibling_dirs=(args.sibling_dir or None),
                        promote_rel_lib=False,
                        monad=args.monad,
                        coq_lib_dir=args.coq_lib_dir,
                        use_block_renderer=args.use_block_renderer,
                    )
                except Exception as exc:
                    print(f"Failed: {context['id']} ({exc})", file=sys.stderr)
                    failures.append(context["id"])
                    continue
                print(
                    f"{context['id']}: {summary['status']} "
                    f"(attempts={summary['attempt_count']}, rocq={summary['check']['status']})"
                )
                assembled = summary["files"].get("assembled_rel_lib")
                if summary["status"] == "passed" and assembled:
                    passed_assembled_paths.append(assembled)
                    mretty_type = _extract_mretty_type(assembled)
                    if mretty_type:
                        mretty_by_func[func_name] = mretty_type

            # Merge per-function passed libs into a single {basename}_rel_lib.v
            if passed_assembled_paths:
                basename = os.path.splitext(os.path.basename(input_path))[0]
                # Honor the per-invocation --coq-lib-dir override (matches the
                # promotion target picked by _promote_rel_lib_if_accepted).
                # Without this, the merged multi-function lib silently lands
                # in the CONFIGURE default while the user's flag is ignored.
                libs_dir = args.coq_lib_dir or _default_coq_lib_dir()
                merged_target = os.path.join(libs_dir, f"{basename}_rel_lib.v")
                try:
                    merge_rel_libs_into_file(
                        input_path, passed_assembled_paths, merged_target,
                        sibling_dirs=(args.sibling_dir or None),
                        monad=args.monad,
                    )
                    print(f"\nMerged rel_lib: {merged_target}")
                except Exception as exc:
                    print(f"Failed to merge rel_lib: {exc}", file=sys.stderr)
                    failures.append(f"merge:{basename}")

                # Remove stale per-function {func}_rel_lib.v files in libs_dir
                # that correspond to functions in this C file (from pre-merge
                # promotion runs).  Keep only the merged {basename}_rel_lib.v.
                func_names = {ctx["summary"]["func_name"] for ctx in contexts}
                for func_name in func_names:
                    if func_name == basename:
                        continue
                    for ext in (".v", ".vo", ".vok", ".vos", ".glob"):
                        stale = os.path.join(libs_dir, f"{func_name}_rel_lib{ext}")
                        if os.path.isfile(stale):
                            try:
                                os.remove(stale)
                                print(f"Removed stale per-function lib: {stale}")
                            except OSError as exc:
                                print(f"Warning: could not remove {stale} ({exc})", file=sys.stderr)

            # Patch the single _rel.c with per-function MretTy substitutions.
            # The codegen for multi-target files emits `{func}_MretTy` per
            # function (matching the merged rel_lib), so apply the mapping.
            if args.patch_rel_c and mretty_by_func:
                _eliminate_mretty_in_rel_c(args.rel_c_path, mretty_by_func)
                print(f"Patched rel.c: {args.rel_c_path}")

            sys.exit(1 if failures else 0)

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
            command_timeout=(args.command_timeout or None),
            sibling_dirs=(args.sibling_dir or None),
            rel_c_path=args.rel_c_path if args.patch_rel_c else None,
            monad=args.monad,
            coq_lib_dir=args.coq_lib_dir,
            use_block_renderer=args.use_block_renderer,
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
