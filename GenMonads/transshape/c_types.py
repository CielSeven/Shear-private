"""Regex-level C struct + type utilities used to resolve the C type of a
``EXPR -> FIELD`` field access referenced in an annotation.

Only what the shape-annotation translator needs is supported: parsing
``struct NAME { ... };`` blocks from a C source / header text, classifying a
type token as scalar vs pointer, and mapping scalar C types to their Coq
counterpart for the abstract-program carrier (typically ``Z``).
"""

from __future__ import annotations

import os
import re
from typing import Dict, List, Optional, Tuple


_STRUCT_DECL_RE = re.compile(
    r"struct\s+(\w+)\s*\{(.*?)\}\s*;",
    re.DOTALL,
)

_FIELD_RE = re.compile(r"^\s*(.*?)(\b\w+)\s*(?:\[[^\]]*\])?\s*$")


def parse_struct_decls(text: str) -> Dict[str, Dict[str, str]]:
    """Return ``{struct_name: {field_name: c_type}}`` parsed from *text*.

    *c_type* is the textual type (e.g. ``"int"``, ``"struct list *"``,
    ``"unsigned long"``).  Whitespace is normalised to single spaces;
    trailing ``*`` markers on the field name are folded into the type.
    """
    out: Dict[str, Dict[str, str]] = {}
    for m in _STRUCT_DECL_RE.finditer(text):
        name = m.group(1)
        body = m.group(2)
        fields: Dict[str, str] = {}
        for raw_field in body.split(";"):
            stripped = raw_field.strip()
            if not stripped:
                continue
            stripped = re.sub(r"\s+", " ", stripped)
            stars_before_name = re.match(r"(.*?)(\*+)\s*(\w+)\s*(?:\[[^\]]*\])?\s*$",
                                         stripped)
            if stars_before_name:
                type_text = (stars_before_name.group(1).strip() + " "
                             + stars_before_name.group(2)).strip()
                field_name = stars_before_name.group(3)
            else:
                fm = _FIELD_RE.match(stripped)
                if not fm:
                    continue
                type_text = fm.group(1).strip()
                field_name = fm.group(2)
            if not type_text or not field_name:
                continue
            fields[field_name] = type_text
        if fields:
            out[name] = fields
    return out


_INCLUDE_RE = re.compile(r'^\s*#\s*include\s*"([^"]+)"', re.MULTILINE)


def collect_struct_decls(
    c_file: str,
    include_search_dirs: Optional[List[str]] = None,
) -> Dict[str, Dict[str, str]]:
    """Parse struct decls from *c_file* and any ``#include "..."`` headers
    resolvable inside *include_search_dirs* (defaults to the directory of
    *c_file*).  Local-only: ``#include <...>`` system headers are ignored."""
    if not os.path.exists(c_file):
        return {}
    dirs = list(include_search_dirs or [])
    dirs.insert(0, os.path.dirname(os.path.abspath(c_file)))
    seen_files: set = set()
    merged: Dict[str, Dict[str, str]] = {}

    def _ingest(path: str) -> None:
        abs_path = os.path.abspath(path)
        if abs_path in seen_files or not os.path.exists(abs_path):
            return
        seen_files.add(abs_path)
        try:
            with open(abs_path, "r", encoding="utf-8") as f:
                text = f.read()
        except OSError:
            return
        for name, fields in parse_struct_decls(text).items():
            merged.setdefault(name, {}).update(fields)
        for inc in _INCLUDE_RE.findall(text):
            for d in dirs:
                candidate = os.path.join(d, inc)
                if os.path.exists(candidate):
                    _ingest(candidate)
                    break

    _ingest(c_file)
    return merged


_SCALAR_TOKENS = {
    "int", "long", "short", "char", "signed", "unsigned",
    "size_t", "ssize_t", "ptrdiff_t",
    "int8_t", "int16_t", "int32_t", "int64_t",
    "uint8_t", "uint16_t", "uint32_t", "uint64_t",
    "intptr_t", "uintptr_t",
}


def is_pointer_type(c_type: str) -> bool:
    return c_type.rstrip().endswith("*")


def is_bool_type(c_type: str) -> bool:
    return c_type.strip() in ("_Bool", "bool")


def is_scalar_type(c_type: str) -> bool:
    """True for integer/scalar types that map to Coq ``Z``."""
    if is_pointer_type(c_type):
        return False
    if is_bool_type(c_type):
        return False
    tokens = [t for t in c_type.strip().split() if t != "const"]
    if not tokens:
        return False
    return all(t in _SCALAR_TOKENS for t in tokens)


def coq_type_of(c_type: str) -> Optional[str]:
    """Map a C type to its Coq counterpart for the abstract-program carrier.
    Returns ``None`` for pointer types (no carrier contribution)."""
    if is_pointer_type(c_type):
        return None
    if is_bool_type(c_type):
        return "bool"
    if is_scalar_type(c_type):
        return "Z"
    return None


# --- per-function variable environment -------------------------------------

def _skip_ws_and_block_comments(text: str, pos: int) -> int:
    while pos < len(text):
        if text[pos].isspace():
            pos += 1
            continue
        if text.startswith("/*", pos):
            end = text.find("*/", pos + 2)
            if end == -1:
                return len(text)
            pos = end + 2
            continue
        break
    return pos


def _find_function_definition(text: str, func_name: str) -> Optional[Tuple[int, str, str]]:
    """Locate ``func_name`` as a definition (followed by ``{``).

    Returns ``(body_start_index, return_type_text, params_text)`` or ``None``
    if no definition (or only declarations) is found.
    """
    name_re = re.compile(rf"\b{re.escape(func_name)}\s*\(")
    for m in name_re.finditer(text):
        # Find matching ``)``.
        depth = 1
        i = m.end()
        while i < len(text) and depth > 0:
            ch = text[i]
            if ch == '(':
                depth += 1
            elif ch == ')':
                depth -= 1
            i += 1
        if depth != 0:
            continue
        params_text = text[m.end():i - 1]
        after = _skip_ws_and_block_comments(text, i)
        # Definition: next non-comment token is ``{``.  A declaration ends
        # with ``;`` (possibly after another comment block, which we already
        # skipped).
        if after >= len(text) or text[after] != '{':
            continue
        # Walk backwards from m.start() to capture the return-type prefix,
        # stopping at ``;``, ``}``, ``{``, ``#`` (preprocessor directive), or
        # start-of-file.
        ret_end = m.start()
        ret_start = ret_end
        while ret_start > 0:
            ch = text[ret_start - 1]
            if ch in ';}{':
                break
            if ch == '\n' and ret_start - 1 > 0:
                # Cut at the line break preceding a ``#include`` /
                # ``#define`` line so directives don't leak into the
                # return-type capture.
                line_start = text.rfind('\n', 0, ret_start - 1) + 1
                if text[line_start:ret_start - 1].lstrip().startswith('#'):
                    break
            ret_start -= 1
        ret_text = text[ret_start:ret_end].strip()
        # Trim any trailing annotation block from a previous declaration.
        if "*/" in ret_text:
            ret_text = ret_text[ret_text.rfind("*/") + 2:].strip()
        # Drop any leading preprocessor lines that survived.
        ret_lines = [
            line for line in ret_text.splitlines()
            if not line.lstrip().startswith('#')
        ]
        ret_text = " ".join(line.strip() for line in ret_lines).strip()
        return after, ret_text, params_text
    return None


def _split_type_and_name(decl: str) -> Optional[Tuple[str, str]]:
    decl = re.sub(r"\s+", " ", decl).strip()
    if not decl:
        return None
    m = re.match(r"^(.*?)(\*+)\s*(\w+)\s*(?:\[[^\]]*\])?\s*$", decl)
    if m:
        type_text = (m.group(1).strip() + " " + m.group(2)).strip()
        return type_text, m.group(3)
    fm = _FIELD_RE.match(decl)
    if not fm:
        return None
    return fm.group(1).strip(), fm.group(2)


def build_type_env(c_source: str, func_name: str) -> Dict[str, str]:
    """Best-effort env mapping ``var_name -> c_type`` for *func_name* in
    *c_source*: includes function params, ``__return``, and any
    ``struct X *p;`` (and similar) declarations at the top of the body.
    """
    env: Dict[str, str] = {}
    located = _find_function_definition(c_source, func_name)
    if not located:
        return env
    body_open, ret_text, params_text = located
    if ret_text:
        env["__return"] = re.sub(r"\s+", " ", ret_text).strip()
    if params_text.strip() and params_text.strip() != "void":
        for raw in params_text.split(","):
            split = _split_type_and_name(raw)
            if split:
                env[split[1]] = split[0]
    # Walk the body to its matching ``}``.
    start = body_open + 1
    depth = 1
    i = start
    while i < len(c_source) and depth > 0:
        ch = c_source[i]
        if ch == '{':
            depth += 1
        elif ch == '}':
            depth -= 1
        i += 1
    body = c_source[start:i - 1] if i > start else ""
    _STMT_KEYWORDS = {"return", "if", "while", "for", "switch", "do",
                      "break", "continue", "goto", "case", "default"}
    for decl_match in re.finditer(
        r"(struct\s+\w+|\w+(?:\s+\w+)*)\s+([\*\s]*\w[\w,\s\*]*);",
        body,
    ):
        type_prefix = decl_match.group(1).strip()
        if type_prefix.split()[0] in _STMT_KEYWORDS:
            continue
        names_part = decl_match.group(2)
        for piece in names_part.split(","):
            piece = piece.strip()
            stars = ""
            while piece.startswith("*"):
                stars += "*"
                piece = piece[1:].strip()
            name_match = re.match(r"^(\w+)", piece)
            if not name_match:
                continue
            name = name_match.group(1)
            if name in env:
                continue
            full_type = (type_prefix + " " + stars).strip() if stars else type_prefix
            env[name] = full_type
    return env


def resolve_field_type(
    expr_text: str,
    field: str,
    type_env: Dict[str, str],
    struct_decls: Dict[str, Dict[str, str]],
) -> Optional[str]:
    """Resolve the C type of ``EXPR -> FIELD``.

    *expr_text* must be a simple identifier (e.g. ``__return``, ``t``);
    parenthesised expressions are unwrapped.  Returns ``None`` if the
    expression can't be associated with a known struct.
    """
    expr = expr_text.strip()
    while expr.startswith("(") and expr.endswith(")"):
        expr = expr[1:-1].strip()
    base_type = type_env.get(expr)
    if not base_type:
        return None
    m = re.search(r"struct\s+(\w+)\s*\*+\s*$", base_type)
    if not m:
        return None
    struct_name = m.group(1)
    fields = struct_decls.get(struct_name)
    if not fields:
        return None
    return fields.get(field)
