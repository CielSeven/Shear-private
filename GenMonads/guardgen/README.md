# guardgen: Invariant + Cond → Abstract Guard (Rocq) Generator

A tiny, modular toolkit for turning *heap invariants* (with separation-logic predicates like `sll`, `store_tree`, `sllseg`) and *pointer conditions* (e.g. `p==null`, `x==y`, `! (a==b) || c!=null`) into **abstract guards** over your chosen abstract values (lists, trees, etc.) expressed as Coq formulas.

The key design is a **predicate registry**: each heap predicate is registered once with its parsing rules and Coq rendering callbacks. Adding a new predicate is a one-file drop-in—no scattered `if/elif` edits.

---

## ✨ Features

- **Modular predicate registry**: add predicates by registering a `PredicateSpec`.
- **Clean package structure** split into `registry`, `parsing`, `cond`, `predicates`, `translate`.
- **Boolean condition parser**: supports `!`, `&&`, `||`, `==`, `!=`, `<>`, `null/nullptr/0`.
- **Segment matching** for `x==y` via segment predicates (e.g., `sllseg(x,y,ℓ)`).
- **Coq output** with a lambda binding that destructs abstract values in invariant order.

---

## 🗂️ Repository layout

```
guardgen/
  __init__.py                 # auto-register built-in predicates on import
  registry.py                 # PredicateSpec + registry
  translate.py                # gen_coq_guard, gen_coq_from_bool
  parsing/
    __init__.py
    invariant.py              # normalize_inv, parse_invariant, ShAtom
  cond/
    __init__.py
    lexer.py                  # tokenization for conditions
    ast.py                    # AtomKind, AtomCond, BoolNode
    parser.py                 # condition parser -> BoolNode
  predicates/
    __init__.py               # imports that register built-ins
    sll.py                    # sll(p,l) and sllseg(x,y,ℓ)
    tree.py             # store_tree(q,t)
```

---

## 📦 Requirements & Install

- Python 3.10+ (uses `typing.Literal`, `|` unions)
- No third-party deps.

import in your project:

```python
from guardgen import gen_coq_guard

inv  = "x=3 && sll(p1,l1) * sll(p2,l2) * store_tree(q,t)"
cond = "p2 == null && q <> null"
print(gen_coq_guard(inv, cond))
```

---

## 🚀 Quick Start

Given:

- **Invariant**
  ```
  x=3 && y=5 && sll(p1, l1) * sll(p2, l2) * store_tree(q, t)
  ```
- **Condition**
  ```
  p2 == null && q <> null
  ```

**Output**:

```coq
fun a =>
  let '(l1, l2, t) := a in
  (l2 = [] /\ t <> empty)
```

Another:

- **Invariant**
  ```
  sll(cur, lh) * sllseg(head, cur, lseg) * store_tree(r, tr)
  ```
- **Condition**
  ```
  head == cur
  ```

**Output**:

```coq
fun a =>
  let '(lh, lseg, tr) := a in
  (lseg = [])
```

If a pointer in the condition has **no matching root predicate** in the invariant:

```
INV: sll(h, xs)
COND: t == null
```

You’ll get a clear error:
```
ValueError: Pointer 't' has no root predicate in invariant
```

---

## 🧠 Core Concepts

### 1) Predicates: **root** vs **segment**

- **Root predicates** model a structure from a pointer root, e.g. `sll(p, l)`, `store_tree(q, t)`.
  - They must provide a `ptr` and an abstract value (e.g. `l`, `t`).
  - When conditions compare `ptr` with null (`ptr==null` or `ptr!=null`), the registry’s root handler converts this into constraints over the abstract value (e.g., `l = []`, `t <> empty`).

- **Segment predicates** relate two pointers, e.g. `sllseg(x, y, lseg)`.
  - They must provide `start`, `end`, and a segment abstract value.
  - When conditions compare two pointers (`x==y` or `x!=y`), the segment handler turns it into constraints like `lseg = []` or `lseg <> []`. Reverse matching `(y,x)` is supported.

### 2) Abstract binding order

The lambda’s pattern `(l1, l2, t, ...)` follows the **invariant order**. Each predicate contributes names via its `abs_names(payload)` callback.

---

## 🧩 API Overview

### `gen_coq_guard(inv: str, cond: str) -> str`
- Normalizes and parses `inv`, parses `cond`, resolves via registry handlers, and emits a Coq guard as a `fun a => ...` expression with `let '(...):= a`.

### `PredicateSpec`
Defined in `guardgen/registry.py`:

```python
@dataclass
class PredicateSpec:
    name: str                       # "sll", "store_tree", ...
    kind: Literal["root","segment"]
    arity: int
    parse_args: Callable[[list[str]], dict]
    to_coq_root_null: Optional[Callable[[dict, bool], str]] = None
    to_coq_segment_eq: Optional[Callable[[dict, bool, bool], str]] = None
    abs_names: Callable[[dict], list[str]] = lambda payload: []
```

**Contract expectations:**
- Root predicates must include `"ptr"` and one or more abstract names (`abs_names`).
- Segment predicates must include `"start"`, `"end"`, and typically one abstract name (e.g., `"seg_abs"`).
- Provide the appropriate handler(s) for the predicate kind.

---

## ➕ Adding a New Predicate

Suppose you want a **doubly-linked list segment** `dllseg(x, y, dl)` where `x==y ↔ dl = []`.

Create `guardgen/predicates/dllseg.py`:

```python
from ..registry import PredicateSpec, register_predicate

def _parse(args: list[str]) -> dict:
    if len(args) != 3:
        raise ValueError(f"dllseg(...) expects 3 args, got {args}")
    return {"start": args[0], "end": args[1], "seg_abs": args[2]}

def _eq(payload: dict, is_eq: bool, reversed_match: bool) -> str:
    dl = payload["seg_abs"]
    return f"{dl} = []" if is_eq else f"{dl} <> []"

def _abs(payload: dict) -> list[str]:
    return [payload["seg_abs"]]

register_predicate(PredicateSpec(
    name="dllseg",
    kind="segment",
    arity=3,
    parse_args=_parse,
    to_coq_segment_eq=_eq,
    abs_names=_abs,
))
```

Then include it by importing inside `guardgen/predicates/__init__.py`:

```python
from .dllseg import *  # noqa: F401,F403
```

That’s it—`dllseg` is live across the whole pipeline.

---

## 🔍 Supported Condition Syntax

- Unary: `! φ`
- Binary: `φ && ψ`, `φ || ψ`
- Atomic pointer comparisons:
  - `p == null`, `p != null`, `p == 0`, `p != 0`, `p == nullptr`, `p != nullptr`
  - `x == y`, `x != y`

> If you need `<, <=, >, >=`, or pure arithmetic, you can extend the condition parser in `guardgen/cond/` similarly to how predicates are registered—reach out in issues if you want a template.

---

## ⚠️ Errors & Diagnostics

- Unknown predicate in the invariant:
  ```
  ValueError: Unknown predicate 'foo' (not registered)
  ```
- Pointer without a root predicate:
  ```
  ValueError: Pointer 'r' has no root predicate in invariant
  ```
- Missing segment for `x==y` / `x!=y`:
  ```
  ValueError: No segment predicate for (x,y) found in invariant
  ```
- Arity mismatches are reported with the predicate name and provided args.

These errors are intentional and precise, so users can immediately fix their invariants or add the necessary predicate registrations.

---

## 🛠️ Internals at a Glance

- `parsing/invariant.py`  
  Splits `INV` by `&&` and `*`, matches `NAME(args)`, consults the registry to parse into `ShAtom(spec, payload)`.

- `cond/parser.py`  
  Turns the condition string into a `BoolNode` AST.

- `translate.py`  
  Resolves pointer atoms using:
  - Root lookups (`payload["ptr"]`) for `p ==/!= null` via `spec.to_coq_root_null`,
    falling back to the `_composition_rules.root_null` engine (e.g. the peeled-tail
    `sllseg(p,q) * sll(q)` concat).
  - Segment emptiness for `x ==/!= y` via the `_composition_rules.segment_eq`
    engine: it matches the queried endpoints to a segment **and requires a
    trailing root `sll(end, _)`** — the acyclicity witness that makes
    `x = y  <=>  seg = []` sound (a bare segment could be a lasso). There is no
    per-predicate `segment_eq` primitive; the gate lives entirely in the JSON.
  Builds the Coq formula and constructs the lambda pattern using `spec.abs_names`.

---

## 🤝 Contributing

- Open a PR with a new predicate in `guardgen/predicates/` plus a minimal example in `examples/`.
- Keep predicate payloads small and explicit (`ptr`, `abs`, `start`, `end`, `seg_abs`, …).
- Add clear error messages; they’re part of the user experience.
- Tests: add cases covering success + expected failures (unknown pointer, missing segment, arity mismatch).

---

## ❓FAQ

**Q: Can the lambda pattern reorder abstract values?**  
A: No. It intentionally follows invariant order to keep the mental model simple. If you want another order, change the invariant or customize `abs_names`.

**Q: Can I map `p==null` using a segment predicate instead of a root?**  
A: By design, **no**—root-vs-null is resolved only against root predicates (e.g., `sll(p, l)`, `store_tree(q, t)`), which encode emptiness at the abstraction boundary.

**Q: What if I need multiple abstract names from one predicate?**  
A: Return multiple names from `abs_names(payload)`; they’ll be included in the pattern in that order.

---
