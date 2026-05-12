import re
from typing import Dict, List, Optional

_IDENT_CHAR = re.compile(r"[A-Za-z0-9_']")


def _is_keyword(text: str, pos: int, kw: str) -> bool:
    end = pos + len(kw)
    if text[pos:end] != kw:
        return False
    before_ok = pos == 0 or not _IDENT_CHAR.match(text[pos - 1])
    after_ok = end >= len(text) or not _IDENT_CHAR.match(text[end])
    return before_ok and after_ok


def _extract_definition_block(coq_source: str, name: str) -> str:
    lines = coq_source.splitlines()
    start = None
    for idx, line in enumerate(lines):
        if re.match(rf"^Definition {re.escape(name)}\b", line):
            start = idx
            break

    if start is None:
        raise ValueError(f"Could not find Definition '{name}' in response")

    text = "\n".join(lines[start:])
    paren_depth = 0
    match_depth = 0
    comment_depth = 0
    in_string = False
    i = 0

    while i < len(text):
        # Inside string literal — only watch for closing quote
        if in_string:
            if text[i] == '"':
                in_string = False
            i += 1
            continue

        # Inside nested comment — watch for (* and *)
        if comment_depth > 0:
            if text[i:i + 2] == "(*":
                comment_depth += 1
                i += 2
            elif text[i:i + 2] == "*)":
                comment_depth -= 1
                i += 2
            else:
                i += 1
            continue

        # Opening comment
        if text[i:i + 2] == "(*":
            comment_depth += 1
            i += 2
            continue

        # Opening string
        if text[i] == '"':
            in_string = True
            i += 1
            continue

        ch = text[i]

        if ch in "([{":
            paren_depth += 1
            i += 1
            continue
        if ch in ")]}":
            paren_depth = max(0, paren_depth - 1)
            i += 1
            continue

        if _is_keyword(text, i, "match"):
            match_depth += 1
            i += len("match")
            continue
        if match_depth > 0 and _is_keyword(text, i, "end"):
            match_depth -= 1
            i += len("end")
            continue

        # Terminating '.' — only at top level, followed by whitespace or EOF
        # (distinguishes statement terminator from qualified names like Module.foo)
        if ch == "." and paren_depth == 0 and match_depth == 0:
            after = text[i + 1] if i + 1 < len(text) else ""
            if not after or after in " \t\n\r":
                return text[:i + 1].strip()

        i += 1

    raise ValueError(f"Definition '{name}' does not terminate with '.'")


_COMPONENT_PARAMETER_SUFFIX = {
    "MretTy": "MretTy",                 # Special: not "{fn}_MretTy" form here.
    "M_loop_before": "M_loop_before",
    "M_1": "M_loop_M1",
    "M_2": "M_loop_M2",
    "M_loop_end": "M_loop_end",
    "M_before": "M_before",
    "M_normal": "M_normal",
    "M": "M",
}


def _component_parameter_name(component: str, func_name: str) -> str:
    suffix = _COMPONENT_PARAMETER_SUFFIX.get(component, component)
    if component == "MretTy":
        return "MretTy"
    return f"{func_name}_{suffix}"


def parse_synthesized_components(
    response_text: str,
    func_name: str,
    required: Optional[list] = None,
) -> Dict[str, str]:
    """Extract Coq Definition blocks from an LLM response.

    By default, extracts the loop-bearing component set
    (``MretTy``, ``M_loop_before``, ``M_1``, ``M_2``, ``M_loop_end``).  When
    *required* is given, extracts exactly those components.
    """
    if required is None:
        required = ["MretTy", "M_loop_before", "M_1", "M_2", "M_loop_end"]
    return {
        component: _extract_definition_block(
            response_text, _component_parameter_name(component, func_name)
        )
        for component in required
    }
