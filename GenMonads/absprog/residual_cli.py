"""CLI for appending residual abstract-program definitions to a Coq file."""

import argparse

from GenMonads.absprog.gen_func_residual import append_func_residual_definitions
from GenMonads.cli_common import add_named_value_argument, resolve_cli_value


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Append residual abstract-program definitions for callee calls"
    )
    add_named_value_argument(
        parser,
        "file_path",
        "Target Rocq/Coq file path",
        "--FILE",
        "--file",
        positional_metavar="FILE",
        flag_metavar="FILE",
    )
    add_named_value_argument(
        parser,
        "callee",
        "Opaque callee name, e.g. sll_merge_M",
        "--CALLEE",
        "--callee",
        positional_metavar="CALLEE",
        flag_metavar="CALLEE",
    )
    add_named_value_argument(
        parser,
        "caller",
        "Caller definition name, e.g. sll_multi_merge_M",
        "--CALLER",
        "--caller",
        positional_metavar="CALLER",
        flag_metavar="CALLER",
    )
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

    file_path = resolve_cli_value(
        args,
        parser,
        "file_path",
        ("file_path_flag",),
        "Provide the target file via positional FILE or --FILE.",
        is_path=True,
    )
    callee = resolve_cli_value(
        args,
        parser,
        "callee",
        ("callee_flag",),
        "Provide the callee via positional CALLEE or --CALLEE.",
    )
    caller = resolve_cli_value(
        args,
        parser,
        "caller",
        ("caller_flag",),
        "Provide the caller via positional CALLER or --CALLER.",
    )

    appended = append_func_residual_definitions(
        file_path,
        callee,
        caller,
        polish=args.polish,
    )
    print(f"Appended {len(appended)} residual definition(s) to {file_path}")


if __name__ == "__main__":
    main()
