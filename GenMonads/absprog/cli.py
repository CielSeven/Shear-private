"""CLI for generating _rel_lib.v skeleton files."""

import argparse
import os
import sys

from GenMonads.absprog.gen_rel_lib import generate_rel_lib_for_file
from GenMonads.cli_common import (
    add_input_path_arguments,
    add_output_path_argument,
    read_configure_value,
    resolve_cli_value,
)


def _default_output_dir():
    """Read COQ_LIB_DIR from environment or CONFIGURE file."""
    return read_configure_value("COQ_LIB_DIR")


def main():
    default_dir = _default_output_dir()
    output_arg_attrs = ("output_dir", "output_dir_flag")

    parser = argparse.ArgumentParser(
        description="Generate _rel_lib.v skeleton files with Parameter declarations"
    )
    add_input_path_arguments(parser, "Input C file or directory")
    add_output_path_argument(
        parser,
        "output_dir",
        f"Output directory for .v files (default: {default_dir or 'none, must specify'})",
        "-o",
        "--output-dir",
        dest="output_dir_flag",
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
        "--monad",
        choices=["staterel", "staterr"],
        default="staterel",
        help=(
            "Monad backend for the generated rel_lib: 'staterel' (StateRelMonad, "
            "default) or 'staterr' (error-aware MonadErr)."
        ),
    )
    args = parser.parse_args()

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
        ("output_dir_flag",),
        "No output directory specified. Set COQ_LIB_DIR or use positional output_dir, --OUTPUT_PATH, or -o/--output-dir.",
        is_path=True,
    ) if any(
        getattr(args, attr, None) is not None
        for attr in output_arg_attrs
    ) else (os.path.normpath(default_dir) if default_dir is not None else None)

    if not output_dir:
        parser.error(
            "No output directory specified. Set COQ_LIB_DIR or use positional output_dir, --OUTPUT_PATH, or -o/--output-dir."
        )

    sibling_dirs = args.sibling_dir or None
    if os.path.isdir(input_path):
        for f in sorted(os.listdir(input_path)):
            if f.endswith(".c"):
                path = generate_rel_lib_for_file(
                    os.path.join(input_path, f), output_dir,
                    sibling_dirs=sibling_dirs,
                    monad=args.monad,
                )
                if path:
                    print(f"  Generated: {os.path.basename(path)}")
                else:
                    print(f"  Skipped:   {f}")
    else:
        path = generate_rel_lib_for_file(
            input_path, output_dir, sibling_dirs=sibling_dirs, monad=args.monad
        )
        if path:
            print(f"Generated: {path}")
        else:
            print("Failed.", file=sys.stderr)
            sys.exit(1)


if __name__ == "__main__":
    main()
