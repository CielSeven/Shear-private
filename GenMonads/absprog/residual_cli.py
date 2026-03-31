"""CLI for appending residual abstract-program definitions to a Coq file."""

import argparse

from GenMonads.absprog.gen_func_residual import append_func_residual_definitions


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Append residual abstract-program definitions for callee calls"
    )
    parser.add_argument("--FILE", dest="file_path", required=True, help="Target Rocq/Coq file path")
    parser.add_argument("--CALLEE", dest="callee", required=True, help="Opaque callee name, e.g. sll_merge_M")
    parser.add_argument("--CALLER", dest="caller", required=True, help="Caller definition name, e.g. sll_multi_merge_M")
    parser.add_argument(
        "--POLISH",
        dest="polish",
        action="store_true",
        help="Polish generated residual definitions before appending",
    )
    parser.add_argument(
        "--NO-POLISH",
        dest="polish",
        action="store_false",
        help="Append raw residual definitions without polishing",
    )
    parser.set_defaults(polish=True)
    args = parser.parse_args()

    appended = append_func_residual_definitions(
        args.file_path,
        args.callee,
        args.caller,
        polish=args.polish,
    )
    print(f"Appended {len(appended)} residual definition(s) to {args.file_path}")


if __name__ == "__main__":
    main()
