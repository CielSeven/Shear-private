"""Translate a proof-block SEP *frame* into a C ``/*@ exists …, … */`` assertion.

A ``funccall_wit`` block's ``Frame:`` lists the separation-logic conjuncts the
callee leaves untouched, spelled in symexec's internal variable language
(``node_423_value``, ``x_427_free``, ``signed int``, ``store(addr, value, type)``).
The *faithful* residual names the frame's unfolded pieces (``x, l0, l1``) as
parameters, so the ``_rel.c`` must (re)introduce them at the call site with a
matching SEP assertion.  This module produces that assertion:

    Frame:
      store(&(node_423_value->data), x_427_free, signed int);
      sll(y_428_free, l0_429_free);
      store(&(node_423_value->next), y_428_free, struct list*);
      store(src_383_addr, src_382_pre, struct list*);          (dropped: local cell)
      ...
      sllseg(src_382_pre, node_423_value, l1_424)
    ->
    /*@ exists x y l0 l1,
        store(&(node->data), int, x) *
        sll(y, l0) *
        store(&(node->next), struct list*, y) *
        sllseg(src@pre, node, l1) */

Rules (see the module README's residual section):

* **keep** heap predicates (``sll``/``sllseg``/…) and *field* stores
  (``store(&(ptr->field), …)``); **drop** local-variable cells
  (``store(<var>_addr, …)``), ``has_permission``, ``undef_data_at``;
* **rename** symexec vars: ``_value`` → the C var (in scope), ``_pre`` → ``var@pre``
  (in scope), ``_free`` / bare ``_<id>`` → the logical var (existential);
* **field store** ``store(addr, value, type)`` → ``store(addr, type, value)`` and a
  leading ``signed`` is stripped from the type (``signed int`` → ``int``);
* **exists** binds the existential vars of the kept conjuncts, first-appearance
  ordered.
"""

from __future__ import annotations

import re
from typing import Iterable, List, Optional, Tuple

__all__ = ["translate_frame_sep"]

# heap predicates kept verbatim (args var-renamed, operand order preserved)
_HEAP_PREDS = ("sllseg", "sllbseg", "dllseg", "listrep", "sll", "lseg", "dll")

# conjunct heads dropped outright (permission / uninitialised local cells)
_DROP_HEADS = ("has_permission", "undef_data_at")

# a symexec variable: `<base>_<id>` with an optional role suffix.
_VAR_RE = re.compile(r"\b([A-Za-z_]\w*?)_(\d+)(_value|_pre|_free|_addr)?\b")


def _rename(text: str) -> str:
    """Rewrite every symexec variable in ``text`` to its C/logical spelling."""
    def repl(m: "re.Match") -> str:
        base, suffix = m.group(1), m.group(3)
        if suffix == "_value":
            return base                        # current C var value — in scope
        if suffix == "_pre":
            return base + "@pre"               # pre-state C var value — in scope
        return base                            # _free / _addr / bare — logical name
    return _VAR_RE.sub(repl, text)


def _existential_bases(conj: str, with_vars: set) -> List[str]:
    """The *logical* (existentially-bound) variable bases in ``conj``, in order.

    Not bound (already in scope): a ``_value``/``_pre`` program value, and a
    **precondition** var — spelled ``_free`` *and* with a base name in
    ``with_vars`` (the same test the residual's ``Given`` rule uses, so a
    ``With`` var like ``l2_381_free`` is not re-bound).  Everything else — an
    unfold piece (``x_427_free``) or a bare ``_<id>`` loop-``Inv`` carrier
    (``l1_424``, bound even though base ``l1`` may also name a ``With`` var) —
    is an existential."""
    out: List[str] = []
    for m in _VAR_RE.finditer(conj):
        base, suffix = m.group(1), m.group(3)
        if suffix in ("_value", "_pre"):
            continue
        if suffix == "_free" and base in with_vars:
            continue
        out.append(base)
    return out


def _split_top_args(s: str) -> List[str]:
    """Split ``a, b, c`` on top-level commas (commas inside ``()``/``[]`` are kept)."""
    args: List[str] = []
    depth = 0
    cur: List[str] = []
    for ch in s:
        if ch in "([":
            depth += 1
            cur.append(ch)
        elif ch in ")]":
            depth -= 1
            cur.append(ch)
        elif ch == "," and depth == 0:
            args.append("".join(cur).strip())
            cur = []
        else:
            cur.append(ch)
    if "".join(cur).strip():
        args.append("".join(cur).strip())
    return args


def _head_args(conj: str) -> Optional[Tuple[str, str]]:
    """``sll(a, b)`` -> ``('sll', 'a, b')``; ``None`` if not a ``head(...)`` form."""
    m = re.match(r"^\s*([A-Za-z_]\w*)\s*\((.*)\)\s*$", conj, re.DOTALL)
    return (m.group(1), m.group(2)) if m else None


def _strip_signed(ty: str) -> str:
    return re.sub(r"^\s*signed\s+", "", ty.strip())


def _render_conjunct(conj: str) -> Optional[str]:
    """Render one kept frame conjunct, or ``None`` if it should be dropped."""
    ha = _head_args(conj)
    if ha is None:
        return None
    head, argstr = ha
    if head in _DROP_HEADS:
        return None
    args = _split_top_args(argstr)
    if head == "store":
        # keep only *field* stores (`store(&(ptr->field), value, type)`); a local
        # variable cell (`store(<var>_addr, value, type)`) is dropped.
        if len(args) != 3 or "->" not in args[0]:
            return None
        addr, value, ty = args
        return f"store({_rename(addr)}, {_strip_signed(ty)}, {_rename(value)})"
    if head in _HEAP_PREDS:
        return f"{head}({', '.join(_rename(a) for a in args)})"
    return None                                # unknown head — drop conservatively


def translate_frame_sep(frame: List[str], with_vars: Iterable[str] = ()) -> str:
    """Translate a parsed ``funccall_wit`` frame into a ``/*@ exists …, … */``
    C assertion, or ``""`` when no conjunct survives.

    ``frame`` is the list of conjunct strings from ``VCBlock.frame`` (e.g.
    ``["store(&(node_423_value->data), x_427_free, signed int)", "sll(...)", …]``).
    ``with_vars`` are the caller's ``With``/``Require`` precondition var base names;
    a frame var that is one of them (``_free`` + base in ``with_vars``) is already
    in scope and is **not** existentially re-bound."""
    with_set = set(with_vars)
    kept: List[Tuple[str, str]] = []           # (rendered, original) for surviving conjuncts
    for conj in frame:
        rendered = _render_conjunct(conj)
        if rendered is not None:
            kept.append((rendered, conj))
    if not kept:
        return ""

    exists: List[str] = []
    for _rendered, original in kept:
        for base in _existential_bases(original, with_set):
            if base not in exists:
                exists.append(base)

    body = " *\n    ".join(r for r, _ in kept)
    header = f"exists {' '.join(exists)},\n    " if exists else ""
    return f"/*@ {header}{body} */"
