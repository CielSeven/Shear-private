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
from GenMonads.cli_common import (
    add_input_path_arguments,
    add_output_path_argument,
    resolve_cli_value,
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
    add_input_path_arguments(parser, "Input C file or directory")
    add_output_path_argument(parser, "output", "Output JSON file or directory")
    args = parser.parse_args()

    input_path = resolve_cli_value(
        args,
        parser,
        "input",
        ("file_path", "c_dir"),
        "Provide an input path via positional input, --FILE, or --C_DIR.",
        is_path=True,
    )
    output_path = resolve_cli_value(
        args,
        parser,
        "output",
        ("output_path",),
        "Provide an output path via positional output or --OUTPUT_PATH.",
        is_path=True,
    )

    if os.path.isdir(input_path):
        os.makedirs(output_path, exist_ok=True)
        written_paths = []
        for filename in sorted(os.listdir(input_path)):
            if not filename.endswith(".c"):
                continue
            input_file = os.path.join(input_path, filename)
            try:
                file_paths = _write_contexts_for_file(input_file, output_path)
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

    if output_path.endswith(".json"):
        try:
            context = write_synthesis_context(input_path, output_path)
        except ValueError as exc:
            print(str(exc), file=sys.stderr)
            sys.exit(1)
        print(f"Generated: {output_path} ({context['summary']['func_name']})")
        return

    os.makedirs(output_path, exist_ok=True)
    try:
        written_paths = _write_contexts_for_file(input_path, output_path)
    except ValueError as exc:
        print(str(exc), file=sys.stderr)
        sys.exit(1)
    if not written_paths:
        print(f"Skipped: {input_path} (no loop-invariant contexts)", file=sys.stderr)
        return

    for path in written_paths:
        print(f"Generated: {path}")


if __name__ == "__main__":
    main()
