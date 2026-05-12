"""Helpers for detecting early return points around a function's first top-level loop."""

from __future__ import annotations

import re
from typing import Dict, Optional


_COMMENT_RE = re.compile(r"/\*.*?\*/|//.*?$", re.DOTALL | re.MULTILINE)


def strip_c_comments(text: str) -> str:
    return _COMMENT_RE.sub("", text)


def extract_function_body(c_source: str) -> str:
    brace_start = c_source.find("{")
    brace_end = c_source.rfind("}")
    if brace_start == -1 or brace_end == -1 or brace_end <= brace_start:
        return ""
    return c_source[brace_start + 1:brace_end]


def _skip_ws(text: str, idx: int) -> int:
    while idx < len(text) and text[idx].isspace():
        idx += 1
    return idx


def _find_matching(text: str, start: int, open_ch: str, close_ch: str) -> Optional[int]:
    depth = 0
    for idx in range(start, len(text)):
        ch = text[idx]
        if ch == open_ch:
            depth += 1
        elif ch == close_ch:
            depth -= 1
            if depth == 0:
                return idx
    return None


def _loop_statement_end(text: str, idx: int) -> int:
    brace_depth = 0
    paren_depth = 0
    while idx < len(text):
        ch = text[idx]
        if ch == "{":
            brace_depth += 1
        elif ch == "}":
            if brace_depth == 0:
                return idx
            brace_depth -= 1
            if brace_depth == 0 and paren_depth == 0:
                return idx + 1
        elif ch == "(":
            paren_depth += 1
        elif ch == ")":
            if paren_depth > 0:
                paren_depth -= 1
        elif ch == ";" and brace_depth == 0 and paren_depth == 0:
            return idx + 1
        idx += 1
    return len(text)


def find_first_top_level_loop(body: str) -> Optional[Dict[str, int | str]]:
    """Find the first while/for loop in the function body.

    Scans at any brace depth so that loops inside if/else blocks are found.
    Returns on the first match, so nested inner loops are not picked up.
    """
    clean = strip_c_comments(body)
    idx = 0
    while idx < len(clean):
        for keyword in ("while", "for"):
            prefix_ok = idx == 0 or not (clean[idx - 1].isalnum() or clean[idx - 1] == "_")
            if prefix_ok and clean.startswith(keyword, idx):
                after_kw = idx + len(keyword)
                suffix_ok = after_kw >= len(clean) or not (
                    clean[after_kw].isalnum() or clean[after_kw] == "_"
                )
                if not suffix_ok:
                    continue
                paren_start = _skip_ws(clean, after_kw)
                if paren_start >= len(clean) or clean[paren_start] != "(":
                    continue
                paren_end = _find_matching(clean, paren_start, "(", ")")
                if paren_end is None:
                    return None
                stmt_start = _skip_ws(clean, paren_end + 1)
                stmt_end = _loop_statement_end(clean, stmt_start)
                if stmt_start < len(clean) and clean[stmt_start] == "{":
                    loop_body_start = stmt_start + 1
                    loop_body_end = stmt_end - 1
                else:
                    loop_body_start = stmt_start
                    loop_body_end = stmt_end
                return {
                    "keyword": keyword,
                    "start": idx,
                    "paren_start": paren_start,
                    "paren_end": paren_end,
                    "stmt_start": stmt_start,
                    "stmt_end": stmt_end,
                    "body_start": loop_body_start,
                    "body_end": loop_body_end,
                }
        idx += 1
    return None


def detect_early_return_shape(c_source: str) -> Dict[str, bool]:
    body = extract_function_body(c_source)
    clean = strip_c_comments(body)
    loop_info = find_first_top_level_loop(body)
    has_loop = loop_info is not None

    if not has_loop:
        # No loop: an "early return" is any branching exit — detected as two
        # or more `return` statements (one in a conditional branch plus the
        # final one, or multiple conditional branches).
        return_count = len(re.findall(r"\breturn\b", clean))
        has_no_loop_early_return = return_count >= 2
        return {
            "has_top_level_loop": False,
            "has_pre_loop_early_return": False,
            "has_loop_body_early_return": False,
            "has_no_loop_early_return": has_no_loop_early_return,
            "needs_early_result": has_no_loop_early_return,
        }

    pre_region = clean[: int(loop_info["start"])]
    loop_region = clean[int(loop_info["body_start"]) : int(loop_info["body_end"])]

    has_pre_loop_early_return = bool(re.search(r"\breturn\b", pre_region))
    has_loop_body_early_return = bool(re.search(r"\breturn\b", loop_region))
    return {
        "has_top_level_loop": True,
        "has_pre_loop_early_return": has_pre_loop_early_return,
        "has_loop_body_early_return": has_loop_body_early_return,
        "has_no_loop_early_return": False,
        "needs_early_result": has_pre_loop_early_return or has_loop_body_early_return,
    }
