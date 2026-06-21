"""Block-tree-driven Coq renderer (Phase 2 — see
``TODO/block_partition_refactor_plan.md``).

This module attempts to translate a function's block tree into a fully
concrete ``Definition {fn}_M := …`` Coq body, eliminating the legacy
opaque ``Parameter {fn}_M`` (and therefore one LLM hole) for functions
the renderer can handle mechanically.

Current scope (Phase 2.0):

* Shape 1 straight-line functions only.
* The function body is a single ``Others`` block.
* Every statement matches one of three patterns:

    1. ``var = callee(args);``     → ``var <- callee_M args ;;``
    2. ``return callee(args);``    → ``callee_M args``
    3. ``return var;``             → ``return var``

* Each argument is a bare identifier (a function parameter or a
  previously-assigned local).
* Each callee name is registered as an ``available_callee`` (so we know
  to emit its ``_M`` suffix and trust it exists in the imported rel-lib).

When all statements translate, :func:`try_render_concrete_definition`
returns the body text.  Anything else returns ``None`` and the caller
falls back to the legacy ``Parameter`` emission — the existing strict-
diff validator continues to operate against that scaffold.

Future phases will extend the rules (initializations, branching, loops);
this module is the place to add them.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple

from GenMonads.absprog.partition import Others


# ---------------------------------------------------------------------------
# Statement parsing


_ASSIGN_CALL_RE = re.compile(
    r"^\s*(?P<lhs>[A-Za-z_]\w*)\s*=\s*"
    r"(?P<callee>[A-Za-z_]\w*)\s*\((?P<args>[^()]*)\)\s*;?\s*$"
)
_RETURN_CALL_RE = re.compile(
    r"^\s*return\s+(?P<callee>[A-Za-z_]\w*)\s*\((?P<args>[^()]*)\)\s*;?\s*$"
)
_RETURN_VAR_RE = re.compile(
    r"^\s*return\s+(?P<var>[A-Za-z_]\w*)\s*;?\s*$"
)
_BARE_IDENT_RE = re.compile(r"^[A-Za-z_]\w*$")


@dataclass
class _AssignCall:
    """``lhs = callee(args);``"""
    lhs: str
    callee: str
    args: List[str]


@dataclass
class _ReturnCall:
    """``return callee(args);``"""
    callee: str
    args: List[str]


@dataclass
class _ReturnVar:
    """``return var;``"""
    var: str


_Statement = "_AssignCall | _ReturnCall | _ReturnVar"


def _split_args(text: str) -> Optional[List[str]]:
    """Return the comma-separated argument list when each entry is a bare
    identifier, else ``None``.  We refuse anything more complex so callers
    fall back to the legacy renderer; future Phase 2.x work can handle
    constants, member accesses, etc."""
    pieces = [p.strip() for p in text.split(",")]
    if pieces == [""]:
        return []
    if not all(_BARE_IDENT_RE.match(p) for p in pieces):
        return None
    return pieces


def _parse_statement(stmt: str) -> Optional[_Statement]:
    """Recognise one of the three supported statement shapes; return
    ``None`` for anything else."""
    stripped = stmt.strip()
    if not stripped:
        return None
    if (m := _ASSIGN_CALL_RE.match(stripped)) is not None:
        args = _split_args(m.group("args"))
        if args is None:
            return None
        return _AssignCall(lhs=m.group("lhs"), callee=m.group("callee"), args=args)
    if (m := _RETURN_CALL_RE.match(stripped)) is not None:
        args = _split_args(m.group("args"))
        if args is None:
            return None
        return _ReturnCall(callee=m.group("callee"), args=args)
    if (m := _RETURN_VAR_RE.match(stripped)) is not None:
        return _ReturnVar(var=m.group("var"))
    return None


def _split_statements(body_text: str) -> List[str]:
    """Split an Others-block body into top-level statements at ``;``."""
    out: List[str] = []
    depth_brace = 0
    depth_paren = 0
    buf: List[str] = []
    for ch in body_text:
        if ch == "{":
            depth_brace += 1
        elif ch == "}":
            depth_brace -= 1
        elif ch == "(":
            depth_paren += 1
        elif ch == ")":
            depth_paren -= 1
        buf.append(ch)
        if ch == ";" and depth_brace == 0 and depth_paren == 0:
            stmt = "".join(buf).strip()
            if stmt:
                out.append(stmt)
            buf = []
    tail = "".join(buf).strip()
    if tail:
        out.append(tail)
    return out


# ---------------------------------------------------------------------------
# Renderer


def try_render_concrete_definition(
    fn_name: str,
    blocks: List,
    require_var_names: List[str],
    available_callees: Dict[str, str],
) -> Optional[str]:
    """Attempt to emit a concrete ``Definition {fn}_M := …`` body for the
    function whose block tree is *blocks*.

    Args:
        fn_name: function name (e.g. ``"glibc_slist_clean_app"``).
        blocks: the function's block-tree (output of
            :func:`partition_function_body`).
        require_var_names: parameter names from the C signature, in
            declaration order — used as the binders for the generated
            ``fun arg1 arg2 => …`` form.
        available_callees: ``{callee_name: callee_signature_str}`` —
            callees the renderer is allowed to invoke via their ``_M``
            counterpart.  Anything outside this set causes a None return.

    Returns:
        The body text to follow ``Definition {fn}_M : <type> :=``, or
        ``None`` when the function isn't (yet) translatable.  Callers
        fall back to the legacy ``Parameter`` emission on None.
    """
    if len(blocks) != 1 or not isinstance(blocks[0], Others):
        return None

    statements = _split_statements(blocks[0].raw_c_text)
    parsed: List[_Statement] = []
    for stmt in statements:
        node = _parse_statement(stmt)
        if node is None:
            return None
        parsed.append(node)
    if not parsed:
        return None
    if not isinstance(parsed[-1], (_ReturnCall, _ReturnVar)):
        return None

    # Validate: every callee mentioned is in available_callees; every
    # variable read is either a require-var or a prior lhs.
    in_scope = set(require_var_names)
    for node in parsed:
        if isinstance(node, _AssignCall):
            if node.callee not in available_callees:
                return None
            for arg in node.args:
                if arg not in in_scope:
                    return None
            in_scope.add(node.lhs)
        elif isinstance(node, _ReturnCall):
            if node.callee not in available_callees:
                return None
            for arg in node.args:
                if arg not in in_scope:
                    return None
        elif isinstance(node, _ReturnVar):
            if node.var not in in_scope:
                return None

    # Render the monadic bind chain.
    lines: List[str] = []
    # Zero-param functions are monadic values, not functions from
    # ``unit``.  Emitting ``fun tt => …`` here would give the Definition
    # a different type (``unit -> MONAD T``) than the declared signature
    # (``MONAD T``) — Coq rejects it.  So we only emit the ``fun`` binder
    # when there's at least one parameter.
    if require_var_names:
        binder = " ".join(require_var_names)
        lines.append(f"  fun {binder} =>")
        body_indent = "    "
    else:
        body_indent = "  "

    def _call_text(callee: str, args: List[str]) -> str:
        """Render a monadic call.  Skip the trailing space when there are
        no args so we don't produce ``f_M ;;`` / ``f_M .`` glitches."""
        if args:
            return f"{callee}_M " + " ".join(args)
        return f"{callee}_M"

    for node in parsed[:-1]:
        # Only _AssignCall reaches here — _ReturnVar and _ReturnCall are
        # the terminal; only an _AssignCall is allowed mid-sequence (the
        # parser already rejects non-terminal returns).
        assert isinstance(node, _AssignCall), (
            "non-terminal statement must be an assignment"
        )
        lines.append(
            f"{body_indent}{node.lhs} <- {_call_text(node.callee, node.args)};;"
        )
    final = parsed[-1]
    if isinstance(final, _ReturnCall):
        lines.append(f"{body_indent}{_call_text(final.callee, final.args)}.")
    else:  # _ReturnVar
        lines.append(f"{body_indent}return {final.var}.")
    return "\n".join(lines)
