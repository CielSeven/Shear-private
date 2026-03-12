"""
CLI for generating Coq guards from invariants and loop conditions.
"""

import argparse
import sys

from GenMonads.guardgen import gen_coq_guard


def main():
    parser = argparse.ArgumentParser(
        description="Generate Coq guards from separation logic invariants and loop conditions"
    )
    parser.add_argument("inv", help="Separation logic invariant (e.g. 'sll(p, l1) * sll(y, l2)')")
    parser.add_argument("cond", help="Loop condition (e.g. 'p != null')")

    args = parser.parse_args()

    try:
        result = gen_coq_guard(args.inv, args.cond)
        print(result)
    except ValueError as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
