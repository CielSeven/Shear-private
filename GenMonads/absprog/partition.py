"""C-source partitioner: function body → tree of typed blocks.

Phase 1 of the block-partition refactor (see
``TODO/block_partition_refactor_plan.md``).  This module provides the
partitioner only — the renderer arrives in Phase 2.  No existing pipeline
code calls into this module yet; it's introduced as pure groundwork
so the block tree can be inspected via ``llm4pv-partition`` before any
behavior changes.

The grammar is five disjoint, complete block types:

1. :class:`Others`            — straight-line statements (no control flow).
2. :class:`IfNoReturn`        — ``if/else`` with no ``return`` in any branch.
3. :class:`IfWithReturn`      — ``if/else`` with ``return`` at any depth in
                                any branch.
4. :class:`WhileNoReturn`     — ``while/for`` whose body has no ``return``.
5. :class:`WhileWithReturn`   — ``while/for`` whose body has a ``return``
                                at any depth (transitive through nested
                                blocks).

The partitioner is a pure function from C source to block tree.  Branch
bodies (then/else) and loop bodies are themselves partitioned recursively
into ``List[Block]``.

Known limitations (do-while, switch, goto, etc.) are tracked separately
in ``TODO/partition_known_limitations.md`` together with the fix sketch
and the test pin that locks the current behavior.  Add a new entry there
when surfacing a new limitation.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from typing import List, Optional, Tuple

from GenMonads.early_return import (
    extract_function_body,
    strip_c_comments,
    _skip_ws,
    _find_matching,
    _loop_statement_end,
)


# ---------------------------------------------------------------------------
# Block dataclasses


@dataclass
class Block:
    """Common to every block.  ``raw_c_text`` is the original C source span
    the block represents (for prompt rendering + debug visibility)."""
    raw_c_text: str


@dataclass
class Others(Block):
    """Straight-line statements.  Renders to a monadic bind chain.

    *contains_terminal_return* is True iff this block holds the function's
    trailing ``return X;`` (P3).  Useful for renderers that need to know
    the outbound type matches the function's declared return type.
    """
    contains_terminal_return: bool = False


@dataclass
class IfNoReturn(Block):
    """``if (cond) { then } [else { else }]`` where neither branch contains
    a ``return`` at any nesting depth.  Renders to ``choice + assume!!``."""
    cond: str
    then_body: List[Block] = field(default_factory=list)
    else_body: List[Block] = field(default_factory=list)


@dataclass
class IfWithReturn(Block):
    """``if (cond) { then } [else { else }]`` where AT LEAST one branch
    contains a ``return`` at any nesting depth.  Covers:

    * the asymmetric early-return case (one branch returns, one continues);
    * the both-branches-return case (renderer collapses the outer match
      because there's no ``Continue`` path).

    ``then_terminates`` / ``else_terminates`` record whether each branch
    transitively returns from the function — derived at partition time so
    the renderer can dispatch without re-scanning C source.
    """
    cond: str
    then_body: List[Block] = field(default_factory=list)
    else_body: List[Block] = field(default_factory=list)
    then_terminates: bool = False
    else_terminates: bool = False


@dataclass
class WhileNoReturn(Block):
    """``while/for (cond) { body }`` where the body has no ``return`` at
    any nesting depth."""
    cond: str
    body: List[Block] = field(default_factory=list)
    keyword: str = "while"   # "while" or "for"


@dataclass
class WhileWithReturn(Block):
    """``while/for (cond) { body }`` where the body has a ``return`` at
    any depth (including through nested loops or inner ``if/else``s — the
    classification is transitive, per the design plan)."""
    cond: str
    body: List[Block] = field(default_factory=list)
    keyword: str = "while"


# ---------------------------------------------------------------------------
# Public API


def partition_function_body(c_source: str) -> List[Block]:
    """Top-level partitioner: take a C function source (with braces), return
    the block-tree representation of its body."""
    body = extract_function_body(c_source)
    return _partition_text(body)


# ---------------------------------------------------------------------------
# Core partitioner


_CONTROL_KEYWORDS = frozenset({
    "return", "break", "continue", "goto",
    "if", "else", "while", "for", "do", "switch", "case", "default",
})


_DECL_PATTERN = re.compile(
    r"""
    ^\s*                            # leading whitespace
    (?:static\s+|extern\s+|const\s+|volatile\s+)*    # storage / qualifier
    (?:                             # type:
        struct\s+\w+                #   struct Name
      | union\s+\w+                 #   union Name
      | enum\s+\w+                  #   enum Name
      | (?:un)?signed\s+\w+         #   signed/unsigned X
      | \w+                         #   bare type name (int, long, size_t, alias)
    )
    \s*\**\s*                       # optional pointer stars, with or without surrounding ws
    \w+                             # variable name
    (?:\s*,\s*\**\s*\w+)*           # additional names (comma-separated)
    \s*;\s*$                        # terminator
    """,
    re.VERBOSE,
)


def _strip_declarations(text: str) -> str:
    """Remove bare top-level variable declarations (P2 in the design plan).

    Declarations introduce no monadic state change; the abstract state is
    determined by the function's invariants, not by C-level locals.  Only
    *initializerless* declarations are dropped — ``int x = foo();`` is real
    work (calls a function) and must stay.

    Only top-level lines (semicolon-terminated, not inside braces or
    parentheses) are inspected; declarations inside nested blocks are left
    alone — the recursive partitioner will see them when it processes that
    block.

    Statements whose first token is a control-flow keyword (``return``,
    ``break``, ``continue``, ``goto``, …) are never treated as
    declarations even if they superficially match the type+var shape
    (``return foo;`` looks like ``<type> <var>;`` to a naive matcher).
    """
    out_chunks: List[str] = []
    brace_depth = 0
    paren_depth = 0
    buf: List[str] = []
    for ch in text:
        if ch == "{":
            brace_depth += 1
        elif ch == "}":
            brace_depth -= 1
        elif ch == "(":
            paren_depth += 1
        elif ch == ")":
            paren_depth -= 1
        buf.append(ch)
        if ch == ";" and brace_depth == 0 and paren_depth == 0:
            stmt = "".join(buf)
            # Guard against control-flow keywords that match the decl
            # regex superficially (`return X;`, `goto label;`, …).
            stripped = stmt.lstrip()
            first_token_match = re.match(r"(\w+)", stripped)
            first_token = first_token_match.group(1) if first_token_match else ""
            if first_token not in _CONTROL_KEYWORDS and _DECL_PATTERN.match(stmt.rstrip()):
                # It's a declaration — drop.
                buf = []
                continue
            # Drop bare empty statements (a lone ``;``); they're no-ops
            # and would surface as ``Others(";")`` blocks that confuse
            # the renderer.
            if stmt.strip() == ";":
                buf = []
                continue
            out_chunks.append(stmt)
            buf = []
    # Trailing run that never hit a ; at depth 0 — preserve verbatim.
    tail = "".join(buf)
    if tail.strip():
        out_chunks.append(tail)
    return "".join(out_chunks)


def _partition_text(text: str) -> List[Block]:
    """Partition arbitrary C body text into a List[Block].

    Algorithm:
        - strip block-comments (so indices used for matching = indices used
          for slicing — without this, comment removal would offset
          positions and the partitioner would miss specials following a
          comment)
        - strip top-level declarations
        - find earliest special (if / while / for) at depth 0
        - everything before it becomes an ``Others`` (if non-empty)
        - emit the special block (recursively partition its sub-bodies)
        - advance the cursor past the special and continue
    """
    text = strip_c_comments(text)
    text = _strip_declarations(text)
    blocks: List[Block] = []
    cursor = 0
    end = len(text)
    while cursor < end:
        cursor = _skip_ws(text, cursor)
        if cursor >= end:
            break
        special = _find_earliest_special(text, cursor)
        if special is None:
            tail = text[cursor:end].strip()
            if tail:
                blocks.append(_others_block(tail))
            break

        gap = text[cursor:special["start"]].strip()
        if gap:
            blocks.append(_others_block(gap))

        blocks.append(_build_special_block(text, special))
        cursor = special["end"]

    # Mark the trailing Others (if any) as containing the function's
    # terminal return.  Even if the C function returns void / has no
    # explicit return, we still flag the last Others — the renderer
    # knows how to handle empty terminal blocks.
    for block in reversed(blocks):
        if isinstance(block, Others):
            block.contains_terminal_return = _contains_top_level_return(block.raw_c_text)
            break

    return blocks


def _others_block(raw: str) -> Others:
    return Others(raw_c_text=raw)


# ---------------------------------------------------------------------------
# Special-block detection


_IF_KW_RE = re.compile(r"\bif\b")
_LOOP_KW_RE = re.compile(r"\b(while|for)\b")
_RETURN_KW_RE = re.compile(r"\breturn\b")


def _find_earliest_special(text: str, start: int) -> Optional[dict]:
    """Scan from *start* for the earliest top-level ``if`` / ``while`` /
    ``for`` keyword.  Returns a dict describing the block extent, or None
    when no special remains in the slice.

    "Top-level" means at brace depth 0 *within the slice we're scanning*
    (i.e. not nested inside a child block we already plan to recurse into).

    *text* is expected to be comment-stripped already (handled by the
    caller in :func:`_partition_text`).  All indices returned are into the
    same *text* the caller passed in.
    """
    clean = text
    idx = start
    brace_depth = 0
    paren_depth = 0
    while idx < len(clean):
        ch = clean[idx]
        if ch == "{":
            brace_depth += 1
            idx += 1
            continue
        if ch == "}":
            brace_depth -= 1
            idx += 1
            continue
        if ch == "(":
            paren_depth += 1
            idx += 1
            continue
        if ch == ")":
            paren_depth -= 1
            idx += 1
            continue
        if brace_depth != 0 or paren_depth != 0:
            idx += 1
            continue
        # Try to match a keyword starting at idx.
        match = _match_keyword_at(clean, idx)
        if match is None:
            idx += 1
            continue
        keyword, kw_end = match
        # Found a top-level if / while / for.
        # Skip whitespace, expect '('.
        paren_start = _skip_ws(text, kw_end)
        if paren_start >= len(text) or text[paren_start] != "(":
            # Malformed — skip past the keyword and keep scanning.
            idx = kw_end
            continue
        paren_end = _find_matching(text, paren_start, "(", ")")
        if paren_end is None:
            return None  # unbalanced — give up on this slice
        stmt_start = _skip_ws(text, paren_end + 1)
        if stmt_start >= len(text):
            return None

        if text[stmt_start] == "{":
            body_brace_end = _find_matching(text, stmt_start, "{", "}")
            if body_brace_end is None:
                return None
            then_body_text = text[stmt_start + 1:body_brace_end]
            stmt_end = body_brace_end + 1
        else:
            # Single-statement form: `if (cond) stmt;`
            stmt_end = _loop_statement_end(text, stmt_start)
            then_body_text = text[stmt_start:stmt_end]

        info = {
            "kind": keyword,
            "start": idx,
            "kw_end": kw_end,
            "cond": text[paren_start + 1:paren_end],
            "then_body_text": then_body_text,
            "end": stmt_end,
        }

        if keyword == "if":
            # Look for optional else (possibly `else if`).
            else_info = _parse_optional_else(text, stmt_end)
            if else_info is not None:
                info["else_body_text"] = else_info["body"]
                info["end"] = else_info["end"]
            else:
                info["else_body_text"] = None

        return info

    return None


def _match_keyword_at(text: str, idx: int) -> Optional[Tuple[str, int]]:
    """If *text* contains ``if`` / ``while`` / ``for`` at *idx* as a whole
    word, return (keyword, idx_after_keyword); else None."""
    for kw in ("while", "for", "if"):
        if not text.startswith(kw, idx):
            continue
        # Whole-word: char before idx is not alnum/_; char after kw isn't either.
        if idx > 0 and (text[idx - 1].isalnum() or text[idx - 1] == "_"):
            continue
        end = idx + len(kw)
        if end < len(text) and (text[end].isalnum() or text[end] == "_"):
            continue
        return (kw, end)
    return None


def _parse_optional_else(text: str, after_then: int) -> Optional[dict]:
    """Look for ``else`` immediately after the then-block.  Returns the
    body text (whether braced or single-statement) plus the cursor after
    the else.

    When the else body is itself an ``if`` (the ``else if`` chain case),
    we consume the FULL composite if-else chain — including the inner
    if's own else clauses — so a chain like::

        if (X) { ... } else if (Y) { ... } else { ... }

    parses as outer-if-with-else-body, where the else body is the entire
    ``if (Y) { ... } else { ... }``.  The recursive partitioner then
    descends into that else body and emits a nested If block carrying
    the chain's tail.

    Without this, ``_loop_statement_end`` stops at the inner if's first
    ``}`` and the final ``else { ... }`` clause gets orphaned in the
    following ``Others`` gap — a real bug surfaced by
    ``glibc_slist_clean_multi_merge``.
    """
    cursor = _skip_ws(text, after_then)
    if not _is_keyword_at(text, cursor, "else"):
        return None
    end_of_else_kw = cursor + 4
    stmt_start = _skip_ws(text, end_of_else_kw)
    if stmt_start >= len(text):
        return None
    if text[stmt_start] == "{":
        body_end = _find_matching(text, stmt_start, "{", "}")
        if body_end is None:
            return None
        return {
            "body": text[stmt_start + 1:body_end],
            "end": body_end + 1,
        }
    # Single-statement else body.  Could be a bare statement OR an
    # ``if`` that may itself carry an ``else`` chain — use the
    # if-aware statement consumer.
    stmt_end = _consume_statement_with_else_chain(text, stmt_start)
    return {
        "body": text[stmt_start:stmt_end],
        "end": stmt_end,
    }


def _is_keyword_at(text: str, idx: int, kw: str) -> bool:
    """Whole-word keyword match at *idx*."""
    if not text.startswith(kw, idx):
        return False
    if idx > 0 and (text[idx - 1].isalnum() or text[idx - 1] == "_"):
        return False
    end = idx + len(kw)
    if end < len(text) and (text[end].isalnum() or text[end] == "_"):
        return False
    return True


def _consume_statement_with_else_chain(text: str, start: int) -> int:
    """Return the position just after a single C statement at *start*,
    chaining ``else`` clauses when the statement is an ``if``.

    Difference from :func:`_loop_statement_end`:

    * ``_loop_statement_end`` stops at the end of the first braced block
      it sees at depth 0 — fine for plain statements, wrong for ``if``
      whose body is braced because it misses any ``else`` that follows.
    * This function recognises that ``if (cond) { ... }`` may extend
      past the closing brace via ``else <stmt>``, and recurses to
      consume the entire composite construct.
    """
    cursor = _skip_ws(text, start)
    if cursor >= len(text):
        return start

    # Braced block: just find the matching brace.
    if text[cursor] == "{":
        end = _find_matching(text, cursor, "{", "}")
        return (end + 1) if end is not None else len(text)

    # `if (cond) <body> [else <body>]` — recurse into body, then optional
    # else, which itself may be another `if`.
    if _is_keyword_at(text, cursor, "if"):
        paren_start = _skip_ws(text, cursor + 2)
        if paren_start >= len(text) or text[paren_start] != "(":
            return _loop_statement_end(text, cursor)
        paren_end = _find_matching(text, paren_start, "(", ")")
        if paren_end is None:
            return len(text)
        body_start = _skip_ws(text, paren_end + 1)
        body_end = _consume_statement_with_else_chain(text, body_start)
        # Tail-recurse into ``else <stmt>`` if present.
        else_pos = _skip_ws(text, body_end)
        if _is_keyword_at(text, else_pos, "else"):
            return _consume_statement_with_else_chain(text, else_pos + 4)
        return body_end

    # Any other single statement — semicolon-terminated or brace-block.
    return _loop_statement_end(text, cursor)


def _build_special_block(full_text: str, info: dict) -> Block:
    """Construct the right block dataclass for *info* and recurse into its
    sub-bodies."""
    raw = full_text[info["start"]:info["end"]]
    cond = info["cond"].strip()

    if info["kind"] in ("while", "for"):
        body_blocks = _partition_text(info["then_body_text"])
        body_has_return = _contains_return(info["then_body_text"])
        cls = WhileWithReturn if body_has_return else WhileNoReturn
        return cls(
            raw_c_text=raw, cond=cond,
            body=body_blocks, keyword=info["kind"],
        )

    # if
    then_text = info["then_body_text"]
    else_text = info["else_body_text"] or ""
    then_body = _partition_text(then_text)
    else_body = _partition_text(else_text) if else_text else []
    then_has_return = _contains_return(then_text)
    else_has_return = _contains_return(else_text) if else_text else False

    if then_has_return or else_has_return:
        return IfWithReturn(
            raw_c_text=raw, cond=cond,
            then_body=then_body, else_body=else_body,
            then_terminates=then_has_return,
            else_terminates=else_has_return,
        )
    return IfNoReturn(
        raw_c_text=raw, cond=cond,
        then_body=then_body, else_body=else_body,
    )


# ---------------------------------------------------------------------------
# Helpers


def _contains_return(text: str) -> bool:
    """Whether *text* syntactically contains a ``return`` keyword at any
    nesting depth.  Used to classify ``If*`` and ``While*`` block variants
    (the classification is transitive — a ``return`` inside a nested
    inner loop still propagates to the outer loop).

    Comments are stripped before the search so a literal ``return`` inside
    a ``/* ... */`` doesn't false-positive.
    """
    return bool(_RETURN_KW_RE.search(strip_c_comments(text)))


def _contains_top_level_return(text: str) -> bool:
    """Whether *text* contains a top-level (not inside braces) ``return``.

    Used to flag the trailing ``Others`` block as carrying the function's
    final return — distinguishes it from intermediate ``Others`` blocks
    that are just side-effecting work without a terminal return.

    *text* arrives already comment-stripped from :func:`_partition_text`,
    so we walk it directly.
    """
    depth = 0
    idx = 0
    while idx < len(text):
        ch = text[idx]
        if ch == "{":
            depth += 1
        elif ch == "}":
            depth -= 1
        elif depth == 0:
            m = _RETURN_KW_RE.match(text, idx)
            if m and (idx == 0 or not (text[idx - 1].isalnum() or text[idx - 1] == "_")):
                return True
        idx += 1
    return False


# ---------------------------------------------------------------------------
# JSON serialisation (for the CLI debug dump)


def block_to_dict(block: Block) -> dict:
    """Convert a block (and its sub-blocks) to a JSON-friendly dict."""
    base = {
        "type": type(block).__name__,
        "raw_c_text": block.raw_c_text,
    }
    if isinstance(block, Others):
        base["contains_terminal_return"] = block.contains_terminal_return
    elif isinstance(block, IfNoReturn):
        base["cond"] = block.cond
        base["then_body"] = [block_to_dict(b) for b in block.then_body]
        base["else_body"] = [block_to_dict(b) for b in block.else_body]
    elif isinstance(block, IfWithReturn):
        base["cond"] = block.cond
        base["then_body"] = [block_to_dict(b) for b in block.then_body]
        base["else_body"] = [block_to_dict(b) for b in block.else_body]
        base["then_terminates"] = block.then_terminates
        base["else_terminates"] = block.else_terminates
    elif isinstance(block, (WhileNoReturn, WhileWithReturn)):
        base["cond"] = block.cond
        base["keyword"] = block.keyword
        base["body"] = [block_to_dict(b) for b in block.body]
    return base


def blocks_to_list(blocks: List[Block]) -> List[dict]:
    return [block_to_dict(b) for b in blocks]


# ---------------------------------------------------------------------------
# Phase 2a: scaffold annotation helpers


@dataclass
class _LoopInfo:
    """Internal bookkeeping for ``split_for_loop_forest``."""
    index: int                          # 1-based source-order loop index
    parent_index: Optional[int]         # parent loop's index, None at top level
    direct_children: List[int]          # direct child loop indices
    block: Block                        # the While* block itself
    siblings_before: List[Block]        # blocks at the same scope before this loop
    siblings_after: List[Block]         # blocks at the same scope after this loop


def split_for_loop_forest(blocks: List[Block]) -> Optional[Dict[str, str]]:
    """Return per-loop C segments for a multi-loop (forest) function.

    Walks the block tree, assigns each ``While*`` block a 1-based source-
    order index (mirroring the legacy ``loop_forest`` numbering), and
    computes the C segments corresponding to the holes the forest scaffold
    emits.  Keys returned:

    * ``M_loop{k}_before`` — top-level loops only: the function-level
      pre-loop preparation.
    * ``M_loop{k}_M2`` — leaf loops only: the loop body (one iteration).
    * ``M_loop{k}_end`` — top-level loops only: the post-loop
      transformation (function-level work after the loop).
    * ``M_loop{k}_to_inner_{j}`` — parent loops: the work inside loop
      ``k``'s body BEFORE entering its direct child ``j``.
    * ``M_loop{k}_after_inner_{j}`` — parent loops: the work inside loop
      ``k``'s body AFTER returning from its direct child ``j``.

    Returns ``None`` when the block sequence contains no ``While*`` block
    (caller falls back to the no-loop helpers).
    """
    all_loops: List[_LoopInfo] = []
    counter = [0]
    _index_loops_at_level(blocks, parent=None, all_loops=all_loops, counter=counter)
    if not all_loops:
        return None
    by_index = {li.index: li for li in all_loops}

    # Walk the loops in execution-narrative order so the dict (and hence
    # the prompt) reads top-to-bottom:
    #   loop1_before
    #   loop1_to_inner_2  →  loop2 (recursively)  →  loop1_after_inner_2
    #   loop1_end
    # then any subsequent top-level loops.
    segments: Dict[str, str] = {}
    top_level = [li for li in all_loops if li.parent_index is None]
    for li in top_level:
        _emit_loop_segments_in_order(li, by_index, segments)
    return segments


def _emit_loop_segments_in_order(
    li: "_LoopInfo",
    by_index: Dict[int, "_LoopInfo"],
    segments: Dict[str, str],
) -> None:
    """Insert *li*'s segments into *segments* in execution-narrative order
    and recurse into its direct children at the right point in the body."""
    prefix = f"M_loop{li.index}"

    # Pre-loop work appears only for top-level loops (function-level
    # _before / _end).  Inner loops' "pre-loop" work is captured by the
    # parent's _to_inner_{this} segment, not by an own _before.
    if li.parent_index is None:
        segments[f"{prefix}_before"] = render_blocks_as_c_snippet(li.siblings_before)

    if not li.direct_children:
        # Leaf loop: emit one iteration as M_loop{k}_M2.
        segments[f"{prefix}_M2"] = render_blocks_as_c_snippet(li.block.body)
    else:
        body = li.block.body
        # Find positions of direct children in the body, preserving
        # source order.
        child_positions: List[Tuple[int, int]] = []
        for child_idx in li.direct_children:
            child_block = by_index[child_idx].block
            for bi, b in enumerate(body):
                if b is child_block:
                    child_positions.append((bi, child_idx))
                    break
        child_positions.sort()
        for seq_idx, (body_idx, child_idx) in enumerate(child_positions):
            # Work before this inner child.
            if seq_idx == 0:
                pre_blocks = body[:body_idx]
            else:
                prev_body_idx = child_positions[seq_idx - 1][0]
                pre_blocks = body[prev_body_idx + 1:body_idx]
            segments[f"{prefix}_to_inner_{child_idx}"] = (
                render_blocks_as_c_snippet(pre_blocks)
            )
            # Recurse into the child — its segments land between
            # to_inner_{child_idx} and after_inner_{child_idx}.
            _emit_loop_segments_in_order(by_index[child_idx], by_index, segments)
            # Work after this inner child returns.
            if seq_idx == len(child_positions) - 1:
                post_blocks = body[body_idx + 1:]
            else:
                next_body_idx = child_positions[seq_idx + 1][0]
                post_blocks = body[body_idx + 1:next_body_idx]
            segments[f"{prefix}_after_inner_{child_idx}"] = (
                render_blocks_as_c_snippet(post_blocks)
            )

    # Post-loop work appears only at top level.
    if li.parent_index is None:
        segments[f"{prefix}_end"] = render_blocks_as_c_snippet(li.siblings_after)


def _index_loops_at_level(
    blocks: List[Block],
    parent: Optional[int],
    all_loops: List[_LoopInfo],
    counter: List[int],
) -> None:
    """Assign loop indices in source order, walking depth-first.

    ``counter`` is a single-element list used as a mutable integer (each
    discovered loop increments it).  ``all_loops`` accumulates the
    ``_LoopInfo`` records across the entire walk.
    """
    while_positions: List[int] = [
        i for i, b in enumerate(blocks)
        if isinstance(b, (WhileNoReturn, WhileWithReturn))
    ]
    if not while_positions:
        return

    for seq_idx, block_idx in enumerate(while_positions):
        counter[0] += 1
        loop_index = counter[0]
        block = blocks[block_idx]

        prev_end = while_positions[seq_idx - 1] + 1 if seq_idx > 0 else 0
        siblings_before = blocks[prev_end:block_idx]
        next_start = (
            while_positions[seq_idx + 1] if seq_idx + 1 < len(while_positions)
            else len(blocks)
        )
        siblings_after = blocks[block_idx + 1:next_start]

        info = _LoopInfo(
            index=loop_index,
            parent_index=parent,
            direct_children=[],
            block=block,
            siblings_before=siblings_before,
            siblings_after=siblings_after,
        )
        all_loops.append(info)

        # Recurse into this loop's body.  The recursion appends new
        # _LoopInfo records to ``all_loops`` — anything whose
        # ``parent_index`` is ``loop_index`` is a direct child.
        _index_loops_at_level(block.body, parent=loop_index, all_loops=all_loops, counter=counter)
        info.direct_children = [
            li.index for li in all_loops if li.parent_index == loop_index
        ]


def split_for_interleaved_early_return(blocks: List[Block]) -> Optional[dict]:
    """Detect the "interleaved early-return" shape: a function whose
    body is a sequence of ``IfWithReturn`` decisions separated by
    ``Others``/``IfNoReturn`` work, with no top-level loops.

    Two or more decisions are required — a single decision is the
    existing no-loop-early-return scaffold, handled by
    :func:`split_for_no_loop_early_return`.  Loop-bearing functions
    are out of scope (those go through the loop scaffolds).

    Returns ``None`` when *blocks* doesn't fit the shape.  When it does:

    .. code-block:: python

        {
            "decisions": [IfWithReturn_block, …],    # length N (>= 2)
            "phases":    [List[Block], …],           # length N: the work AFTER each decision's Continue path
        }

    ``phases[k]`` is the work between decisions ``k`` and ``k+1``; the
    last entry is the work after the final decision (the terminal phase
    producing the function's return value).  Any work BEFORE the first
    decision lives in the first decision's M_decision_1 input scope (the
    agent encodes it into M_decision_1's body) — we don't surface it as
    a separate hole because the existing scaffold convention puts
    pre-decision work into the decision's caller.
    """
    if any(
        isinstance(b, (WhileNoReturn, WhileWithReturn)) for b in blocks
    ):
        return None
    decision_positions = [
        i for i, b in enumerate(blocks) if isinstance(b, IfWithReturn)
    ]
    if len(decision_positions) < 2:
        return None
    decisions: List[Block] = []
    phases: List[List[Block]] = []
    for k, dec_idx in enumerate(decision_positions):
        decisions.append(blocks[dec_idx])
        if k + 1 < len(decision_positions):
            next_idx = decision_positions[k + 1]
            phases.append(blocks[dec_idx + 1:next_idx])
        else:
            phases.append(blocks[dec_idx + 1:])
    return {"decisions": decisions, "phases": phases}


def split_for_loop_scaffold(blocks: List[Block]) -> Optional[dict]:
    """Map a single-loop function's block tree onto the existing
    ``M_loop_before`` / ``M_loop_M2`` / ``M_loop_end`` scaffold.

    The split:

    * ``M_loop_before``: every block before the first ``While*`` block.
      This includes any pre-loop preparation statements *and* any early-
      return guards that occur before the loop — the existing scaffold
      models this via the ``pre_loop_early_return`` variant.
    * ``M_loop_M2``: the loop body (the ``While*`` block's recursive
      partition).  One iteration of the loop.
    * ``M_loop_end``: every block after the loop, typically the trailing
      ``return X;`` statement.

    Phase 3B addition: when the loop is a :class:`WhileWithReturn` AND
    its body contains an ``IfWithReturn`` block, also returns
    ``"M_loop_M2_split": {"pre_decision": [...], "decision": IfBlock,
    "post_decision": [...]}`` so the renderer can show the agent the
    body's internal structure (pre-early-return work → decision →
    post-decision continuation).  Only the first body-level
    ``IfWithReturn`` is split; deeper or sequenced cases stay in the
    ``M_loop_M2`` snippet for the agent to navigate.

    ``M_loop_M1`` (the loop's break-branch hole) is omitted: it has no
    direct C-source counterpart — it's the mechanical "extract MretTy
    from the loop state at exit," and the agent fills it based on the
    state's type rather than a C statement.

    Returns ``{"M_loop_before": [...], "M_loop_M2": [...],
    "M_loop_end": [...]}`` (with optional ``"M_loop_M2_split"``) or
    ``None`` when *blocks* doesn't contain exactly one ``While*`` block.
    Multi-loop bodies are handled by :func:`split_for_loop_forest`.
    """
    loop_positions = [
        i for i, b in enumerate(blocks)
        if isinstance(b, (WhileNoReturn, WhileWithReturn))
    ]
    if len(loop_positions) != 1:
        return None
    loop_idx = loop_positions[0]
    loop_block = blocks[loop_idx]
    result: dict = {
        "M_loop_before": blocks[:loop_idx],
        "M_loop_M2": loop_block.body,
        "M_loop_end": blocks[loop_idx + 1:],
    }

    # Phase 3B — when the loop has an internal early-return at the top
    # level of its body, surface the sub-structure so the agent knows to
    # use ``early_result`` wrapping.
    if isinstance(loop_block, WhileWithReturn):
        body = loop_block.body
        inner_if_idx = next(
            (i for i, b in enumerate(body) if isinstance(b, IfWithReturn)),
            None,
        )
        if inner_if_idx is not None:
            inner_if = body[inner_if_idx]
            result["M_loop_M2_split"] = {
                "pre_decision": body[:inner_if_idx],
                "decision": inner_if,
                "post_decision": body[inner_if_idx + 1:],
            }
    return result


def split_for_no_loop_early_return(blocks: List[Block]) -> Optional[dict]:
    """Map a no-loop-early-return function's block tree onto the existing
    ``M_before`` / ``M_normal`` scaffold.

    The split: everything from function start through the first
    :class:`IfWithReturn` is the ``M_before`` segment (the early-return
    decision, possibly preceded by prep work the agent must still execute
    before the decision); everything after that is the ``M_normal``
    segment (the post-decision body).

    Returns ``{"m_before": List[Block], "m_normal": List[Block]}`` or
    ``None`` when the block sequence doesn't have a leading
    ``IfWithReturn`` (i.e. the function doesn't fit the simple no-loop
    early-return shape the existing scaffold supports).

    This helper is *for annotation only* — it doesn't change the
    scaffold's hole names or types; it tells the renderer which C
    statements correspond to each hole so the agent's prompt can carry
    the binding.
    """
    if not blocks:
        return None
    split_index = next(
        (i for i, b in enumerate(blocks) if isinstance(b, IfWithReturn)),
        None,
    )
    if split_index is None:
        return None
    return {
        "m_before": blocks[: split_index + 1],
        "m_normal": blocks[split_index + 1:],
    }


def render_blocks_as_c_snippet(blocks: List[Block]) -> str:
    """Concatenate a block sub-list's ``raw_c_text`` into a single C
    snippet suitable for embedding in a Coq comment.  Blocks are joined
    by blank lines to preserve readability."""
    return "\n\n".join(
        b.raw_c_text.strip() for b in blocks if b.raw_c_text.strip()
    )


def format_c_segment_comment(
    hole_name: str,
    role: str,
    c_snippet: str,
    indent: str = "       ",
) -> str:
    """Render a Coq ``(* ... *)`` block describing which C statements a
    given LLM hole models.

    Args:
        hole_name: e.g. ``"sll_reverse_M_before"``.
        role: short tagline like ``"the early-return decision"`` or
            ``"the post-decision body"``.
        c_snippet: the C source segment the hole models (rendered
            verbatim, indented under the comment).
        indent: leading whitespace placed before each line of the C
            snippet to set it off visually.
    """
    body_lines = c_snippet.splitlines() if c_snippet else ["(empty)"]
    indented = "\n".join(indent + line for line in body_lines)
    return (
        f"(* {hole_name} models {role}:\n"
        f"{indented}\n"
        f" *)"
    )
