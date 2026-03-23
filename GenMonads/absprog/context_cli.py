"""CLI for generating synthesis-context JSON files."""

import argparse
import json
import os
import sys
from typing import List

from GenMonads.absprog.context import (
    collect_all_synthesis_contexts,
    write_synthesis_context,
)


def _output_path_for_context(output_dir: str, context_id: str) -> str:
    return os.path.join(output_dir, f"{context_id}.auto.json")


def _write_context_json(context: dict, output_path: str) -> None:
    output_dir = os.path.dirname(output_path)
    if output_dir:
        os.makedirs(output_dir, exist_ok=True)
    with open(output_path, "w", encoding="utf-8") as f:
        json.dump(context, f, indent=2)
        f.write("\n")


def _write_contexts_for_file(input_file: str, output_dir: str) -> List[str]:
    contexts = collect_all_synthesis_contexts(input_file)
    written_paths = []
    for context in contexts:
        output_path = _output_path_for_context(output_dir, context["id"])
        _write_context_json(context, output_path)
        written_paths.append(output_path)
    return written_paths


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Generate synthesis-context JSON files for LLM abstract-program generation"
    )
    parser.add_argument("input", help="Input C file or directory")
    parser.add_argument("output", help="Output JSON file or directory")
    args = parser.parse_args()

    if os.path.isdir(args.input):
        os.makedirs(args.output, exist_ok=True)
        written_paths = []
        for filename in sorted(os.listdir(args.input)):
            if not filename.endswith(".c"):
                continue
            input_file = os.path.join(args.input, filename)
            try:
                file_paths = _write_contexts_for_file(input_file, args.output)
            except ValueError as exc:
                print(f"Skipped: {input_file} ({exc})", file=sys.stderr)
                continue
            if not file_paths:
                print(f"Skipped: {input_file} (no loop-invariant contexts)", file=sys.stderr)
                continue
            written_paths.extend(file_paths)

        for path in written_paths:
            print(f"Generated: {path}")
        return

    if args.output.endswith(".json"):
        try:
            context = write_synthesis_context(args.input, args.output)
        except ValueError as exc:
            print(str(exc), file=sys.stderr)
            sys.exit(1)
        print(f"Generated: {args.output} ({context['summary']['func_name']})")
        return

    os.makedirs(args.output, exist_ok=True)
    try:
        written_paths = _write_contexts_for_file(args.input, args.output)
    except ValueError as exc:
        print(str(exc), file=sys.stderr)
        sys.exit(1)
    if not written_paths:
        print(f"Skipped: {args.input} (no loop-invariant contexts)", file=sys.stderr)
        return

    for path in written_paths:
        print(f"Generated: {path}")


if __name__ == "__main__":
    main()
