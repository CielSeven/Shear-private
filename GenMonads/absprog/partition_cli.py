"""CLI debug command for the Phase-1 partitioner.

Usage::

    uv run llm4pv-partition path/to/file.c [--func name]

Dumps the block tree as JSON to stdout.  Useful for eyeballing the
partitioner's output on real files before any renderer is wired.  The
``--func`` flag picks a specific function in a multi-function file; the
default partitions every function present and prints them under a
``{func_name: blocks}`` mapping.
"""

import argparse
import json
import os
import sys
from typing import List, Optional

from GenMonads.absprog.context import _extract_function_source
from GenMonads.absprog.partition import (
    blocks_to_list,
    partition_function_body,
)
from GenMonads.transshape.process_and_translate import (
    process_and_translate_file,
)


def _extract_function_sources(c_file: str) -> List[dict]:
    """Return ``[{"name": str, "source": str}, …]`` — one entry per
    function definition present in *c_file*.

    Uses the existing TransShape preprocessor to enumerate functions (so
    the discovery rules stay in sync with the rest of the pipeline), then
    ``context._extract_function_source`` to pull each function's body
    from the source file.
    """
    result = process_and_translate_file(c_file, generate_guards=False)
    if "error" in result:
        raise ValueError(result["error"])
    funcs: List[dict] = []
    raw_funcs = result.get("functions") or ([result] if "function" in result else [])
    for func_data in raw_funcs:
        name = func_data.get("function")
        if not name:
            continue
        try:
            src = _extract_function_source(c_file, name)
        except (ValueError, OSError):
            continue
        funcs.append({"name": name, "source": src})
    return funcs


def _resolve_targets(
    c_file: str, func_filter: Optional[str],
) -> List[dict]:
    funcs = _extract_function_sources(c_file)
    if func_filter:
        funcs = [f for f in funcs if f["name"] == func_filter]
        if not funcs:
            raise ValueError(
                f"Function '{func_filter}' not found in {c_file}"
            )
    return funcs


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Dump the Phase-1 block-tree partition of a C function as JSON. "
            "Inspection-only — no renderer is invoked."
        )
    )
    parser.add_argument(
        "c_file",
        help="Path to the C source file to partition.",
    )
    parser.add_argument(
        "--func",
        help="Limit output to the named function (default: all functions).",
    )
    parser.add_argument(
        "--indent",
        type=int, default=2,
        help="JSON indent level (default: 2).  Pass 0 for compact output.",
    )
    args = parser.parse_args()

    if not os.path.isfile(args.c_file):
        parser.error(f"file not found: {args.c_file}")

    try:
        funcs = _resolve_targets(args.c_file, args.func)
    except ValueError as exc:
        print(f"error: {exc}", file=sys.stderr)
        sys.exit(1)

    output = {
        func["name"]: blocks_to_list(partition_function_body(func["source"]))
        for func in funcs
    }
    indent = args.indent if args.indent > 0 else None
    print(json.dumps(output, indent=indent))


if __name__ == "__main__":
    main()
