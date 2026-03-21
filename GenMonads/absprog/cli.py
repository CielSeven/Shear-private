"""CLI for generating _rel_lib.v skeleton files."""

import argparse
import os
import sys

from GenMonads.absprog.gen_rel_lib import generate_rel_lib_for_file


def _default_output_dir():
    """Read COQ_LIB_DIR from environment or CONFIGURE file."""
    env = os.environ.get("COQ_LIB_DIR")
    if env:
        return env

    # Try reading from CONFIGURE at repo root
    configure = os.path.join(os.path.dirname(__file__), "..", "..", "CONFIGURE")
    configure = os.path.normpath(configure)
    if os.path.isfile(configure):
        with open(configure) as f:
            for line in f:
                line = line.strip()
                if line.startswith("COQ_LIB_DIR="):
                    # Parse: COQ_LIB_DIR="${COQ_LIB_DIR:-/default/path}"
                    val = line.split(":-", 1)[-1].rstrip('}"')
                    if val:
                        return val
    return None


def main():
    default_dir = _default_output_dir()

    parser = argparse.ArgumentParser(
        description="Generate _rel_lib.v skeleton files with Parameter declarations"
    )
    parser.add_argument("input", help="Input C file or directory")
    parser.add_argument(
        "-o", "--output-dir",
        default=default_dir,
        help=f"Output directory for .v files (default: {default_dir or 'none, must specify'})",
    )
    args = parser.parse_args()

    if not args.output_dir:
        parser.error("No output directory specified. Set COQ_LIB_DIR or use -o.")

    if os.path.isdir(args.input):
        for f in sorted(os.listdir(args.input)):
            if f.endswith(".c"):
                path = generate_rel_lib_for_file(
                    os.path.join(args.input, f), args.output_dir
                )
                if path:
                    print(f"  Generated: {os.path.basename(path)}")
                else:
                    print(f"  Skipped:   {f}")
    else:
        path = generate_rel_lib_for_file(args.input, args.output_dir)
        if path:
            print(f"Generated: {path}")
        else:
            print("Failed.", file=sys.stderr)
            sys.exit(1)


if __name__ == "__main__":
    main()
