"""Logical-list term language used inside autovc proof blocks.

The term syntax is a small first-order language whose operators are described
*externally* by ``GenMonads/data/list_op_signatures.json`` — the generator
itself knows nothing about ``cons``/``app``/``nil`` specifically.  Each operator
declares:

* whether its first textual argument is the element *type* (``cons(Z, h, t)``);
* the *role* of each remaining operand (``elem`` -> ``T``, ``list`` -> ``list T``),
  which is what lets us infer the type of a fresh variable from the term it
  appears in;
* how to render it as Coq surface syntax.

So `cons(Z, x_427_free, l0_429_free)` parses to an `Op`, from which we can read
off "`x_427_free : Z`, `l0_429_free : list Z`" and render "`x :: l2'`".
"""

from __future__ import annotations

import json
import os
from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple, Union


# ---- operator signature registry (external data) ---------------------------

_DATA_DIR = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(__file__))), "data")
_SIG_FILE = os.path.join(_DATA_DIR, "list_op_signatures.json")


@dataclass(frozen=True)
class OpSig:
    name: str
    type_arg: bool
    arg_roles: Tuple[str, ...]      # per-operand role: "elem" | "list" | "scalar"
    render_kind: str                # "nullary" | "infix"
    symbol: str                     # render symbol
    result: str = "list"            # value kind produced: "list" | "scalar"
    parse_kind: str = "call"        # proof-block syntax: "call" (head(args)) | "infix"
    parse_symbol: str = ""          # infix symbol in proof blocks (e.g. "+")
    elem_type: Optional[str] = None  # fixed element type when there's no type_arg


def _load_signatures(path: str = _SIG_FILE) -> Dict[str, OpSig]:
    with open(path) as f:
        raw = json.load(f)
    sigs: Dict[str, OpSig] = {}
    for name, spec in raw["operators"].items():
        r = spec["render"]
        p = spec.get("parse", {"kind": "call"})
        sigs[name] = OpSig(
            name=name,
            type_arg=bool(spec.get("type_arg", False)),
            arg_roles=tuple(spec.get("args", [])),
            render_kind=r["kind"],
            symbol=r["symbol"],
            result=spec.get("result", "list"),
            parse_kind=p.get("kind", "call"),
            parse_symbol=p.get("symbol", ""),
            elem_type=spec.get("elem_type"),
        )
    return sigs


SIGNATURES: Dict[str, OpSig] = _load_signatures()


# ---- AST -------------------------------------------------------------------

@dataclass(frozen=True)
class Var:
    name: str


@dataclass(frozen=True)
class Op:
    op: str                     # operator name, e.g. "cons"
    type_arg: Optional[str]     # element type T parsed from the term, e.g. "Z"
    operands: Tuple["Term", ...]


Term = Union[Var, Op]


def role_type(role: str, type_arg: Optional[str]) -> str:
    """Type of an operand given its role and the operator's element type T."""
    if role in ("elem", "scalar"):
        return type_arg or "_"
    if role == "list":
        return f"list {type_arg}" if type_arg else "list _"
    return type_arg or "_"


# ---- parsing ---------------------------------------------------------------

def _split_args(s: str) -> List[str]:
    args: List[str] = []
    depth, cur = 0, ""
    for ch in s:
        if ch == "(":
            depth += 1
            cur += ch
        elif ch == ")":
            depth -= 1
            cur += ch
        elif ch == "," and depth == 0:
            args.append(cur.strip())
            cur = ""
        else:
            cur += ch
    if cur.strip():
        args.append(cur.strip())
    return args


def _strip_outer_parens(s: str) -> str:
    s = s.strip()
    while s.startswith("(") and s.endswith(")"):
        depth = 0
        enclosing = True
        for i, c in enumerate(s):
            if c == "(":
                depth += 1
            elif c == ")":
                depth -= 1
                if depth == 0 and i != len(s) - 1:
                    enclosing = False
                    break
        if enclosing:
            s = s[1:-1].strip()
        else:
            break
    return s


def _split_top(s: str, sep: str) -> List[str]:
    out, depth, cur = [], 0, ""
    for c in s:
        if c == "(":
            depth += 1
            cur += c
        elif c == ")":
            depth -= 1
            cur += c
        elif c == sep and depth == 0:
            out.append(cur)
            cur = ""
        else:
            cur += c
    out.append(cur)
    return out


def parse_term(s: str) -> Term:
    s = s.strip()
    # call form: head(args)  — cons(Z, h, t), app(Z, a, b), nil(Z)
    if s.endswith(")") and "(" in s:
        head = s[: s.index("(")].strip()
        if head in SIGNATURES and SIGNATURES[head].parse_kind == "call":
            sig = SIGNATURES[head]
            args = _split_args(s[s.index("(") + 1 : -1])
            type_arg: Optional[str] = None
            if sig.type_arg and args:
                type_arg, args = args[0], args[1:]
            return Op(op=head, type_arg=type_arg, operands=tuple(parse_term(a) for a in args))
    # infix form: a SYM b  — (s + x); registered, not hardcoded
    inner = _strip_outer_parens(s)
    for name, sig in SIGNATURES.items():
        if sig.parse_kind != "infix":
            continue
        parts = _split_top(inner, sig.parse_symbol)
        if len(parts) == 2 and parts[0].strip() and parts[1].strip():
            return Op(op=name, type_arg=sig.elem_type,
                      operands=(parse_term(parts[0]), parse_term(parts[1])))
    return Var(s)


# ---- queries / rendering ---------------------------------------------------

def free_vars(t: Term) -> List[str]:
    out: List[str] = []

    def go(x: Term) -> None:
        if isinstance(x, Var):
            if x.name not in out:
                out.append(x.name)
        elif isinstance(x, Op):
            for o in x.operands:
                go(o)

    go(t)
    return out


def substitute(t: Term, subst: Dict[str, "Term"]) -> "Term":
    """Replace every ``Var`` whose name is a key of *subst* with the mapped
    term, recursively.  Used to inline solver-emitted definitions of
    intermediate ``_free`` variables (``l0 -> l3``, ``l3 -> l2_2 ++ l2_3``) so
    the output term is expressed purely over the segment's inputs."""
    if isinstance(t, Var):
        return subst.get(t.name, t)
    if isinstance(t, Op):
        return Op(op=t.op, type_arg=t.type_arg,
                  operands=tuple(substitute(o, subst) for o in t.operands))
    return t


def collect_var_types(t: Term) -> List[Tuple[str, str]]:
    """Infer the type of each variable from its position inside operators.

    Returns ordered (var_name, coq_type) pairs.  A bare variable at top level
    has no inferable type and is omitted.
    """
    out: List[Tuple[str, str]] = []
    seen: set[str] = set()

    def go(x: Term) -> None:
        if isinstance(x, Op):
            sig = SIGNATURES[x.op]
            for role, operand in zip(sig.arg_roles, x.operands):
                if isinstance(operand, Var):
                    if operand.name not in seen:
                        seen.add(operand.name)
                        out.append((operand.name, role_type(role, x.type_arg)))
                else:
                    go(operand)

    go(t)
    return out


def render(t: Term, names: Dict[str, str], *, top: bool = True) -> str:
    """Render `t` as Coq, mapping variable names through `names`."""
    if isinstance(t, Var):
        return names.get(t.name, t.name)
    sig = SIGNATURES[t.op]
    if sig.render_kind == "nullary":
        return sig.symbol
    if sig.render_kind == "infix":
        parts = [render(o, names, top=False) for o in t.operands]
        s = f" {sig.symbol} ".join(parts)
        return s if top else f"({s})"
    # prefix fallback
    parts = [render(o, names, top=False) for o in t.operands]
    s = " ".join([sig.symbol] + parts)
    return s if top else f"({s})"
