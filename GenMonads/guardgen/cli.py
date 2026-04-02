"""
CLI for generating Coq guards from invariants and loop conditions.
"""

import argparse
import sys

from GenMonads.guardgen import gen_coq_guard
from GenMonads.cli_common import add_named_value_argument, resolve_cli_value


def main():
    parser = argparse.ArgumentParser(
        description="Generate Coq guards from separation logic invariants and loop conditions"
    )
    add_named_value_argument(
        parser,
        "inv",
        "Separation logic invariant (e.g. 'sll(p, l1) * sll(y, l2)')",
        "--INV",
        "--inv",
    )
    add_named_value_argument(
        parser,
        "cond",
        "Loop condition (e.g. 'p != null')",
        "--COND",
        "--cond",
    )

    args = parser.parse_args()
    inv = resolve_cli_value(
        args,
        parser,
        "inv",
        ("inv_flag",),
        "Provide the invariant via positional inv or --INV.",
    )
    cond = resolve_cli_value(
        args,
        parser,
        "cond",
        ("cond_flag",),
        "Provide the loop condition via positional cond or --COND.",
    )

    try:
        result = gen_coq_guard(inv, cond)
        print(result)
    except ValueError as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
