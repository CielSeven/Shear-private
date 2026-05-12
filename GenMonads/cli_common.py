"""Shared helpers for CLI argument aliases.

Path-like arguments follow a single contract across the CLI entry points:
- positional and alias-style flags may both be provided;
- matching duplicates are accepted;
- conflicting duplicates raise a parser error;
- resolved path values are normalized before being returned.
"""

import os
from typing import Optional


_CONFIGURE_REL_PATH = os.path.normpath(
    os.path.join(os.path.dirname(__file__), "..", "CONFIGURE")
)


def read_configure_value(key: str) -> Optional[str]:
    """Return the default for *key* from ``$key`` env var or the ``CONFIGURE`` file.

    Environment variables take precedence.  The CONFIGURE file uses shell
    syntax like ``KEY="${KEY:-/default/path}"``; the default after ``:-`` is
    extracted.  Returns ``None`` if neither source provides a value.
    """
    env = os.environ.get(key)
    if env:
        return env

    if not os.path.isfile(_CONFIGURE_REL_PATH):
        return None

    with open(_CONFIGURE_REL_PATH) as f:
        for line in f:
            stripped = line.strip()
            if not stripped.startswith(f"{key}="):
                continue
            if ":-" in stripped:
                value = stripped.split(":-", 1)[-1].rstrip('}"')
            else:
                value = stripped.split("=", 1)[-1].strip().strip('"')
            if value:
                return value
    return None


def add_input_path_arguments(parser, help_text: str) -> None:
    parser.add_argument("input", nargs="?", help=help_text)
    parser.add_argument(
        "--FILE",
        "--file",
        dest="file_path",
        help="Input file path (alias-style convenience flag)",
    )
    parser.add_argument(
        "--C_DIR",
        "--c-dir",
        dest="c_dir",
        help="Input directory path (alias-style convenience flag)",
    )


def add_output_path_argument(
    parser,
    positional_name: str,
    help_text: str,
    *extra_flags: str,
    dest: str = "output_path",
) -> None:
    parser.add_argument(positional_name, nargs="?", help=help_text)
    parser.add_argument(
        "--OUTPUT_PATH",
        "--output-path",
        *extra_flags,
        dest=dest,
        help="Output file or directory path (alias-style convenience flag)",
    )


def add_named_value_argument(
    parser,
    positional_name: str,
    help_text: str,
    *flags: str,
    positional_metavar: Optional[str] = None,
    flag_metavar: Optional[str] = None,
) -> None:
    parser.add_argument(positional_name, nargs="?", help=help_text, metavar=positional_metavar)
    parser.add_argument(
        *flags,
        dest=f"{positional_name}_flag",
        help=help_text,
        metavar=flag_metavar,
    )


def _normalize_path(value: str) -> str:
    return os.path.normpath(value)


def resolve_cli_value(args, parser, positional_attr: str, alias_attrs, missing_message: str, *, is_path: bool = False):
    values = []
    for attr in (positional_attr, *alias_attrs):
        value = getattr(args, attr, None)
        if value is None:
            continue
        normalized = _normalize_path(value) if is_path else value
        values.append((attr, value, normalized))

    if not values:
        parser.error(missing_message)

    _, chosen_value, chosen_normalized = values[0]
    conflicts = [
        f"{attr}={value}"
        for attr, value, normalized in values[1:]
        if normalized != chosen_normalized
    ]
    if conflicts:
        parser.error(
            f"Conflicting values provided for {positional_attr}: "
            f"{positional_attr}={chosen_value}, " + ", ".join(conflicts)
        )

    return chosen_normalized if is_path else chosen_value
