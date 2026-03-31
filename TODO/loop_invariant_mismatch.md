# Loop Invariant / Abstract State Mismatch

## High-level issue

There is a generator-level mismatch between:

- the loop invariant emitted into `_rel.c` / auto context files, and
- the abstract loop program state emitted into `_rel_lib.v`.

Today, the loop abstract state is derived mainly from the generated data variables that come from translated predicates, such as `l1`, `l2`, `l3`. This works when the refinement relation is fully represented by those translated predicate variables.

However, some loop invariants also contain extra existential witnesses that come from pure match relations, for example:

- `t -> data == w`
- `p -> key == k`
- other similar "current concrete field matches abstract value" clauses

These witnesses are kept in the printed invariant, but they are not threaded into the monadic loop state. As a result, the generated invariant may mention a witness like `w`, while the abstract program only uses a state such as:

```coq
M_loop(l1, l2, l3)
```

instead of something like:

```coq
M_loop(l1, l2, l3, w)
```

This makes the loop invariant and the abstract program talk about different states.

## Why this is a problem

For refinement proofs, the loop invariant is supposed to describe the same abstract state that the loop program manipulates. If the invariant contains a meaningful match witness that is not represented in the abstract loop state, then:

- the `safeExec` clause is attached to an incomplete state,
- the generated `_rel_lib.v` signatures have the wrong arity,
- the synthesized abstract loop transitions are forced to ignore part of the invariant,
- and the downstream verification conditions can become false rather than merely hard to prove.

In short, the current pipeline can generate an invariant that is stronger than the state tracked by `M_loop`.

## Example: `sll_append`

Source file:

- `/Users/cielseven/Projects/LLM4PV/shape_invdataset/sll/sll_append.c`

The original C loop invariant is:

```c
/*@ Inv  exists w, t != 0 &&
    t -> next == u && t -> data == w &&
    listrep(y) *
    listrep(u) *
    lseg(x, t)
 */
```

This invariant does two things at once:

1. It tracks the list-shaped abstract pieces:
   - `listrep(y)`
   - `listrep(u)`
   - `lseg(x, t)`
2. It also tracks the current concrete node `t` through pure facts:
   - `t != 0`
   - `t -> next == u`
   - `t -> data == w`

The generated relational invariant becomes:

```c
/*@ Inv exists w l1 l2 l3,
    safeExec(ATrue, bind(sll_append_M_loop(l1,l2,l3), sll_append_M_loop_end), X) &&
    t != 0 && t -> next == u && t -> data == w &&
    sll(y, l1) * sll(u, l2) * sllseg(x, t, l3)
 */
```

The problem is that `w` is still present in the invariant, but it is not present in the abstract loop state:

```coq
sll_append_M_loop(l1, l2, l3)
```

So the emitted invariant suggests that the refinement state includes `w`, while the abstract program interface says it does not.

The generated `_rel_lib.v` follows the incomplete 3-component state:

```coq
Definition sll_append_M_loop :
  list Z -> list Z -> list Z -> program unit MretTy := ...
```

But the invariant shape suggests that the intended loop state should be closer to:

```coq
Definition sll_append_M_loop :
  list Z -> list Z -> list Z -> Z -> program unit MretTy := ...
```

or equivalently a 4-tuple state containing `w`.

## Root cause

The pipeline currently treats "generated predicate variables" as the loop abstract state, but does not extend that state with existential witnesses that arise from pure match relations.

So there are effectively two notions of loop state:

- the state visible in the translated invariant text,
- the state visible in `M_loop` / `_rel_lib.v` signatures.

Those two notions should be unified.

## Likely fix direction

The generator should derive the loop abstract state from the full refinement-relevant invariant, not only from the translated predicate variables.

In practice, that likely means:

- keep the translated predicate variables such as `l1`, `l2`, `l3`,
- also detect existential witnesses that are semantically part of the match relation, such as `w` in `t -> data == w`,
- include them in the loop state used by:
  - `safeExec(... M_loop(...), ...)`,
  - auto context signatures,
  - `_rel_lib.v` signatures,
  - and any synthesized loop transition components.

For `sll_append`, that would mean consistently using a state like:

```coq
sll_append_M_loop(l1, l2, l3, w)
```

throughout the generated artifacts.

## Impact

This does not appear to be a one-file issue. Other generated examples with invariants of the form `exists w, ... t -> data == w ...` may be affected in the same way.

So this should be treated as a generator design bug, not just a bad proof obligation in one verification file.

---

## Fix Plan

### Key insight

Not all pre-existing existential variables are data variables. For example, `exists nxt, x -> next == nxt` — `nxt` is a pointer, not data. Only variables that appear in **data field match clauses** like `? -> data == w` should be promoted into the abstract loop state. Which struct fields count as "data" must be configurable.

### Step 1: Configurable data field registry

Create `GenMonads/data/data_fields.json`:

```json
{
  "data_fields": ["data", "key", "val"]
}
```

Extensible — when new struct types are added (trees with `val`, etc.), update this file.

### Step 2: Data witness extraction utility

Create a function (e.g., `extract_data_witnesses`) that, given:
- the translated invariant text,
- the list of pre-existing existential variable names,
- the data field registry,

scans pure clauses for patterns `<expr> -> <data_field> == <var>` where `<data_field>` is in the registry and `<var>` is a pre-existing existential. Returns the matched variable names.

Example: `exists w nxt, t -> next == nxt && t -> data == w && ...`
- `t -> next == nxt` — `next` not a data field → skip
- `t -> data == w` — `data` is a data field, `w` is existential → collect `w`

Result: `['w']`

### Step 3: Integration in process_and_translate.py

In `translate_inner_assertions`, after calling `translate_assertion_with_exists`:
- Extract pre-existing existential vars from the translated text (the vars before the generated ones)
- Run `extract_data_witnesses` against those vars
- Append the data witnesses to `variables` (after the generated predicate vars)
- Append their types (`Z`) to `variable_types`

### Step 4: No downstream changes needed

`add_safeexec_predicate`, `collect_func_extern_info`, and `_rel_lib.v` generation all read from `variables` and `variable_types` — they propagate automatically.

### Expected output for sll_append

```
variables: ['l1', 'l2', 'l3', 'w']
variable_types: ['list Z', 'list Z', 'list Z', 'Z']
```

```coq
sll_append_M_loop(l1, l2, l3, w)
-- signature: list Z -> list Z -> list Z -> Z -> program unit MretTy
```

### Affected files

| File | Change |
|---|---|
| `data/data_fields.json` | New — configurable list of data field names |
| `transshape/process_and_translate.py` | After `translate_assertion_with_exists`, extract data witnesses, append to `variables` and `variable_types` |
| New utility (e.g., `transshape/data_witness.py`) | `extract_data_witnesses()` function + loader for `data_fields.json` |
