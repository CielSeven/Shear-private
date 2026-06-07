"""Loop-forest analysis: scan a C function body, identify each ``while``/
``for`` loop with its body span, and assemble a forest by source-position
containment.  The resulting nodes describe the *nesting structure* (parent /
children / sibling order) that the abstract-program codegen consumes when it
emits one scaffold per loop with mechanical nesting.

This module is purely a structural analyser — it doesn't read invariants or
emit Coq.  The only intersection with the rest of the pipeline is
:func:`assign_invariants_to_loops`, which maps each ``/*@ Inv ... */``
annotation (by its source position) to the loop it annotates.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from typing import Dict, List, Optional


@dataclass
class LoopNode:
    """One ``while`` / ``for`` loop discovered in a function body.

    Attributes
    ----------
    index : int
        0-based position in source order; stable identifier used by codegen.
    keyword : str
        Either ``"while"`` or ``"for"``.
    while_pos : int
        Byte offset of the keyword in the source string.
    body_start : int
        Offset of the first character inside the loop's ``{ ... }`` body
        (i.e. one past the opening brace).
    body_end : int
        Offset of the matching closing brace.
    parent : Optional[int]
        Index of the immediate enclosing loop, or ``None`` for top-level.
    children : list[int]
        Indices of directly-nested loops, in source order.
    inv_index : Optional[int]
        Index into the caller-supplied ``inv_positions`` list, after
        :func:`assign_invariants_to_loops` runs.
    """

    index: int
    keyword: str
    while_pos: int
    body_start: int
    body_end: int
    parent: Optional[int] = None
    children: List[int] = field(default_factory=list)
    inv_index: Optional[int] = None


# ---------------------------------------------------------------------------
# Tokenisation helpers — respect comments, strings and char literals so loop
# keywords inside them are not mistaken for real loops.


def _skip_ws_comments(text: str, pos: int) -> int:
    while pos < len(text):
        ch = text[pos]
        if ch.isspace():
            pos += 1
            continue
        if text.startswith("//", pos):
            nl = text.find("\n", pos)
            pos = len(text) if nl == -1 else nl + 1
            continue
        if text.startswith("/*", pos):
            end = text.find("*/", pos + 2)
            pos = len(text) if end == -1 else end + 2
            continue
        break
    return pos


def _skip_string(text: str, pos: int, quote: str) -> int:
    """Skip a C string or char literal starting at ``pos`` (the opening quote)."""
    pos += 1
    n = len(text)
    while pos < n and text[pos] != quote:
        if text[pos] == "\\" and pos + 1 < n:
            pos += 2
            continue
        pos += 1
    return pos + 1 if pos < n else n


def _match_brace(text: str, open_pos: int) -> int:
    """Return the index of the ``}`` matching the ``{`` at *open_pos*, or -1."""
    assert text[open_pos] == "{"
    depth = 1
    i = open_pos + 1
    n = len(text)
    while i < n:
        ch = text[i]
        if ch == '"' or ch == "'":
            i = _skip_string(text, i, ch)
            continue
        if text.startswith("//", i):
            nl = text.find("\n", i)
            i = n if nl == -1 else nl + 1
            continue
        if text.startswith("/*", i):
            end = text.find("*/", i + 2)
            i = n if end == -1 else end + 2
            continue
        if ch == "{":
            depth += 1
        elif ch == "}":
            depth -= 1
            if depth == 0:
                return i
        i += 1
    return -1


_LOOP_KW_RE = re.compile(r"\b(while|for)\b")


def _find_loop_keywords(text: str) -> List[tuple]:
    """Yield ``(position, keyword)`` for every ``while``/``for`` token outside
    comments and string literals."""
    out: List[tuple] = []
    i = 0
    n = len(text)
    while i < n:
        ch = text[i]
        if ch == '"' or ch == "'":
            i = _skip_string(text, i, ch)
            continue
        if text.startswith("//", i):
            nl = text.find("\n", i)
            i = n if nl == -1 else nl + 1
            continue
        if text.startswith("/*", i):
            end = text.find("*/", i + 2)
            i = n if end == -1 else end + 2
            continue
        m = _LOOP_KW_RE.match(text, i)
        if m and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] == "_")):
            out.append((m.start(), m.group(1)))
            i = m.end()
            continue
        i += 1
    return out


# ---------------------------------------------------------------------------
# Public API


def build_loop_forest(c_source: str) -> List[LoopNode]:
    """Find every ``while`` / ``for`` loop in *c_source* and assemble the
    nesting forest.

    Loops without an opening brace (single-statement body) and ``do-while``
    constructs are ignored — the abstract-program scaffolds we generate are
    only meaningful for braced loop bodies, which is what every fixture and
    real C source in this project uses.

    Returns
    -------
    list[LoopNode]
        In source order.  ``parent``/``children`` describe the forest.
    """
    loops: List[LoopNode] = []
    for kw_pos, keyword in _find_loop_keywords(c_source):
        p = _skip_ws_comments(c_source, kw_pos + len(keyword))
        if p >= len(c_source) or c_source[p] != "(":
            continue
        # Match the closing ``)``.
        depth = 1
        i = p + 1
        n = len(c_source)
        while i < n and depth > 0:
            ch = c_source[i]
            if ch == '"' or ch == "'":
                i = _skip_string(c_source, i, ch)
                continue
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
            i += 1
        if depth != 0:
            continue
        body_open = _skip_ws_comments(c_source, i)
        if body_open >= n or c_source[body_open] != "{":
            continue
        body_end = _match_brace(c_source, body_open)
        if body_end == -1:
            continue
        loops.append(LoopNode(
            index=len(loops),
            keyword=keyword,
            while_pos=kw_pos,
            body_start=body_open + 1,
            body_end=body_end,
        ))

    # Resolve parent/children by source-position containment.  The "immediate"
    # parent is the deepest enclosing loop — i.e. the smallest body span that
    # still contains the child's ``while`` position.
    for child in loops:
        containing = [
            cand for cand in loops
            if cand.index != child.index
            and cand.body_start <= child.while_pos < cand.body_end
        ]
        if not containing:
            continue
        parent = min(containing, key=lambda c: c.body_end - c.body_start)
        child.parent = parent.index
        parent.children.append(child.index)

    return loops


def top_level_loops(loops: List[LoopNode]) -> List[LoopNode]:
    """Return loops with no parent, in source order."""
    return [loop for loop in loops if loop.parent is None]


def _tuple_type(types: List[str]) -> str:
    if not types:
        return "unit"
    if len(types) == 1:
        return types[0]
    return "(" + " * ".join(types) + ")"


def _body_has_top_level_return(body: str) -> bool:
    """True when *body* contains a top-level ``return`` statement (one not
    inside a nested ``while``/``for``).  Used to flag per-loop early return.

    A nested loop's own ``return`` counts as the inner loop's early-return,
    not the outer's — so we recurse-skip nested loop body spans.
    """
    stripped = body
    # Find nested while/for spans inside this body and mask them out.
    nested = build_loop_forest(stripped)
    masked = list(stripped)
    for n in nested:
        for i in range(n.while_pos, n.body_end + 1):
            if i < len(masked):
                masked[i] = " "
    masked_text = "".join(masked)
    # Strip strings and comments before searching.
    cleaned: List[str] = []
    i = 0
    n = len(masked_text)
    while i < n:
        ch = masked_text[i]
        if ch == '"' or ch == "'":
            i = _skip_string(masked_text, i, ch)
            continue
        if masked_text.startswith("//", i):
            nl = masked_text.find("\n", i)
            i = n if nl == -1 else nl + 1
            continue
        if masked_text.startswith("/*", i):
            end = masked_text.find("*/", i + 2)
            i = n if end == -1 else end + 2
            continue
        cleaned.append(ch)
        i += 1
    return re.search(r"\breturn\b", "".join(cleaned)) is not None


def build_loop_templates(
    func_name: str,
    c_source: Optional[str],
    inv_assertions: List[Dict],
) -> List[Dict]:
    """Canonical per-loop descriptor builder used by every stage of the
    pipeline (translate_c_file, gen_rel_lib, absprog.context).

    Each entry combines the loop forest's structural info with that loop's
    own ``Inv`` data — variable types, condition, guard.  ``has_early_return``
    flags top-level ``return`` statements in the loop's body (a ``break``
    exits only its own loop and is already modeled by ``M1``).

    Returns ``[]`` when *c_source* is missing or no ``Inv`` annotations are
    available — callers fall back to legacy single-loop behaviour.
    """
    if not c_source or not inv_assertions:
        return []
    invs = [a for a in inv_assertions if a.get("type") == "Inv" and "variables" in a]
    if not invs:
        return []
    loops = build_loop_forest(c_source)
    if not loops:
        return []
    assign_invariants_in_source_order(loops, len(invs))

    templates: List[Dict] = []
    for loop in loops:
        if loop.inv_index is None:
            continue
        inv = invs[loop.inv_index]
        inv_vars = list(inv.get("variables", []))
        raw_types = inv.get("variable_types")
        if raw_types is None:
            inv_var_types: List[str] = ["list Z"] * len(inv_vars)
        else:
            inv_var_types = list(raw_types)
            if len(inv_var_types) != len(inv_vars):
                inv_var_types = inv_var_types[: len(inv_vars)] + ["list Z"] * (
                    len(inv_vars) - len(inv_var_types)
                )
        body_span = c_source[loop.body_start: loop.body_end]
        coq_guard = inv.get("coq_guard")
        templates.append({
            "func_name": func_name,
            "loop_index": loop.index,
            "parent": loop.parent,
            "children": list(loop.children),
            "keyword": loop.keyword,
            "inv_index": loop.inv_index,
            "inv_variables": inv_vars,
            "inv_var_types": inv_var_types,
            "state_type": _tuple_type(inv_var_types),
            "loop_condition": inv.get("command_guard", ""),
            "coq_guard": coq_guard or "",
            "guard_available": bool(coq_guard),
            "loop_invariant_translated": inv.get("translated", ""),
            "data_witnesses": list(inv.get("data_witnesses", []) or []),
            "has_inner_loops": bool(loop.children),
            "has_early_return": _body_has_top_level_return(body_span),
        })
    return templates


def assign_invariants_in_source_order(
    loops: List[LoopNode],
    num_invariants: int,
) -> None:
    """Pair invariants with loops by source order: the i-th ``Inv`` annotation
    annotates the i-th loop in source order.

    This is the robust mapping used by the rest of the pipeline — the
    transshape preprocessor extracts invariants and the forest builder
    extracts loops both in source order, and the project convention is that
    every loop carries exactly one ``Inv``.  Excess invariants are silently
    ignored (the next stage handles missing/extra cases).
    """
    if not loops:
        return
    by_pos = sorted(loops, key=lambda lo: lo.while_pos)
    for i in range(min(num_invariants, len(by_pos))):
        by_pos[i].inv_index = i


def assign_invariants_to_loops(
    loops: List[LoopNode],
    inv_positions: List[int],
) -> None:
    """For each Inv position (in caller order), set ``loop.inv_index`` on the
    loop whose ``while`` keyword first follows that position.

    Modifies *loops* in place.  An Inv annotation positioned past every loop is
    silently ignored.  The mapping reflects the project convention that a
    ``/*@ Inv ... */`` comment annotates the loop immediately following it.
    """
    if not loops:
        return
    by_pos = sorted(loops, key=lambda lo: lo.while_pos)
    for inv_idx, inv_pos in enumerate(inv_positions):
        for loop in by_pos:
            if loop.while_pos > inv_pos:
                loop.inv_index = inv_idx
                break
