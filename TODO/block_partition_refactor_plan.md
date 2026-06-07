# Block-Partition Refactor Plan

## Motivation

`generate_rel_lib` (in `GenMonads/absprog/gen_rel_lib.py`) currently dispatches
on a small set of pre-computed flags to pick one of three hard-coded
scaffolds: loop, no-loop-early-return, or opaque-Parameter.  The scaffolds do
not compose.  Functions whose shape is "early return + work + call + early
return + work" can't be expressed by stitching scaffolds together, and the
ad-hoc post-synth `_sync_residual_artifacts` step (which re-extracts
continuations after each cross-file call from the LLM-synthesized
`M_before` / `M_normal`) produces malformed Coq whenever the call placement
differs from the scaffold's hidden assumption.

Symptom: `list_append_raw` synthesis fails because the LLM places the
`list_tail_M` call in `M_before` (semantically fine, syntactically what the
C source looks like), but the residual extractor is built around the
convention "call lives in `M_normal`."  No prompt tells the agent which C
statements each abstract program should model — the convention is implicit
in the flag-dispatched scaffold.

The reorganization replaces the three hard-coded scaffolds with a small
compositional grammar: a function body parses into a tree of typed blocks,
each block has a fixed monadic template, and trees compose by sequencing.
The mapping from C statements to abstract-program structure becomes explicit
in the partitioner's output, eliminating the implicit-convention failure
mode.

## The Five Block Types

Disjoint, complete: any C function body partitions into a sequence of
these.

1. **`Others`** — straight-line statements (assignments, calls, declarations,
   inner `if/else` chains that don't return).  No control flow boundaries
   at this level.

2. **`IfNoReturn`** — `if (cond) { then } [else { else }]` where **neither**
   branch contains a `return`.

3. **`IfWithReturn`** — `if (cond) { then } [else { else }]` where **at
   least one** branch contains a `return` at any depth.  Covers the
   asymmetric early-return case AND the both-branches-return case.

4. **`WhileNoReturn`** — `while/for (cond) { body }` where `body` contains
   no `return` at any depth.

5. **`WhileWithReturn`** — `while/for (cond) { body }` where `body` contains
   a `return` at any depth (including through inner loops or inner
   `if/else`s — the propagation is transitive, not depth-bounded).

The classification predicate is uniform: `*_with_return` ⟺ the block's body
syntactically contains `\breturn\b` at any nesting depth.

## Monadic Templates

The QCP monad's branching primitive is `choice` + `assume!!`, not Coq
`match` on the C-level boolean.  This is a non-negotiable convention.

### `Others`

```coq
⟦stmt_1⟧ ;; ⟦stmt_2⟧ ;; … ;; ⟦stmt_n⟧
```

Each statement renders to its monadic counterpart: calls become
`r <- callee_M args ;;`, pure assignments become state updates,
declarations are dropped (no monad semantics).  The final `return X;`
becomes the trailing `return ⟦X⟧` of the bind chain.

### `IfNoReturn`

```coq
choice
  (assume!! ⟦cond⟧  ;; ⟦then_body⟧)
  (assume!! ⟦¬cond⟧ ;; ⟦else_body⟧)
```

When the else branch is absent in C, the renderer fills `⟦else_body⟧` with
`return s` (continue with the current state).  Both branches must produce
the same outbound state type.

### `IfWithReturn`

```coq
e <-
  choice
    (assume!! ⟦cond⟧  ;; ⟦then_body⟧ ;;
       (* if then terminates with `return X`: *) return (ReturnNow ⟦X⟧)
       (* if then continues:                  *) return (Continue s))
    (assume!! ⟦¬cond⟧ ;; ⟦else_body⟧ ;;
       (* symmetric *)) ;;
match e with
| ReturnNow r => return r
| Continue s  => …downstream blocks…
end
```

Three sub-cases distinguished by the renderer:

- **Both branches return** → the outer `match` collapses; the block IS the
  function tail and there are no downstream blocks (dead code after both
  branches returning is treated as user error).
- **Then returns, else continues** → `Continue` flows into the next sibling
  block.
- **Else returns, then continues** → symmetric.

### `WhileNoReturn` / `WhileWithReturn`

Existing `repeat_break` scaffold with `M_loop_before` / `M_loop_M1` /
`M_loop_M2` / `M_loop_end` holes, driven by the block tree rather than the
flag-dispatched scaffold.  `WhileWithReturn` wraps its iteration with
`early_result` so an inner `return` produces `ReturnNow r` which propagates
up through the outer loop's `repeat_break`.

### Composition between siblings

For a sequence `[B_1, B_2, …, B_n]`:

- If any `B_i` is `IfWithReturn` or `WhileWithReturn`, downstream siblings
  `B_{i+1} … B_n` are wrapped in `match e with | Continue s => … |
  ReturnNow r => return r end` mechanically.
- `early_result` wrapping is propagated outward through every enclosing
  loop, so a `WhileWithReturn` whose body contains a `WhileWithReturn`
  whose body contains an `IfWithReturn` produces three nested
  `repeat_break`-on-`early_result` layers.

## Partitioning Algorithm

```python
partition_body(c_body) → List[Block]:
    body = strip_declarations(c_body)   # locals like `struct list *tail;`

    blocks = []
    cursor = 0
    while cursor < end:
        next_special = find_earliest_special(c_body, after=cursor)
        if next_special is None:
            tail = c_body[cursor:end]
            if non_empty(tail):
                blocks.append(Others(stmts=tail))
            break

        gap = c_body[cursor : next_special.start]
        if non_empty(gap):
            blocks.append(Others(stmts=gap))

        blocks.append(build_special_block(next_special))
        cursor = next_special.end

    for block in blocks:
        if isinstance(block, (WhileNoReturn, WhileWithReturn)):
            block.body = partition_body(block.body)
        elif isinstance(block, (IfNoReturn, IfWithReturn)):
            block.then_body = partition_body(block.then_body)
            block.else_body = partition_body(block.else_body) if block.else_body else []

    return blocks
```

`find_earliest_special` scans for the earliest `if (...)` or `while/for
(...)` and classifies the resulting block by inspecting whether `\breturn\b`
appears in its body (any branch, any depth).  By construction, gaps between
specials are contiguous runs of non-control-flow code that collapse into
exactly one `Others`.  Adjacency of two `Others` blocks is impossible.

### Edge cases

- **Function body is a single `return X;`** → one `Others` block with that
  statement.
- **No specials at all** → one `Others` block holding the whole body.
- **Special at very start / very end** → fine; the surrounding gap is just
  empty.
- **`if (cond) { return X; } else { work; }`** → emit `IfWithReturn` with
  `then_body=[Others("return X;")]` and `else_body=[Others("work;")]`.  No
  hoisting of else-body — the block owns both branches structurally.
- **`if (cond) return X; else return Y;`** → emit `IfWithReturn` with both
  branches terminating.  Renderer skips the outer `match` because there's no
  `Continue` path.
- **`goto`** → out of scope for this codebase; surfaces as unsupported.

## Renderer Architecture

The block-tree renderer is a small recursive function per block type:

```python
def render(block: Block, ctx: RenderContext) -> Tuple[str, OutboundType]:
    ...
```

Each renderer returns its monadic text and the outbound type it produces
(plain `MONAD T` for non-returning blocks, `MONAD (early_result S Ret)`
for `_with_return` blocks).  `render` on a sibling list (`List[Block]`)
composes them with the bind-and-`match`-wrap discipline described above.

The renderer reuses existing primitives:

- `assume!!`, `choice` from the QCP monad imports.
- `early_result` Inductive (unchanged).
- `repeat_break` (unchanged).
- The `_M_loop_*` hole-name conventions (unchanged) — just emitted from the
  block tree rather than the flag-dispatched scaffold.

## LLM Holes

The pipeline owns the structural code generation (binds, matches, choices,
assume!!, return).  The LLM owns the **semantic** content:

- **Predicate interpretations** for `if_*` conditions.  Today these are
  partially handled by GuardGen; in the new architecture, GuardGen feeds the
  block tree's `IfNoReturn` / `IfWithReturn` renderers with the abstract
  predicate.
- **Abstract assignment semantics** for `Others` blocks containing
  spatial-predicate mutations (e.g. `tail->next = y` becomes
  "append `y` onto the abstract list at `tail`").
- **Loop scaffold holes** `M_loop_before`, `M_loop_M1`, `M_loop_M2`,
  `M_loop_end` for `While*` blocks — same as today, but the block tree
  tells the LLM which C statements each hole models.

The strict-diff validator's `must_define` list is derived from the block
tree's hole-name walk, so adding a new block type with new holes
automatically extends the contract; no manual list maintenance.

## Migration Phases

### Phase 1 — partitioner module + JSON dump (no behavior change)

- New `GenMonads/absprog/partition.py`:
  - `dataclass` definitions for the five block types.
  - `partition_function_body(c_source) → List[Block]`.
  - Recursive body decomposition for `If*` branches and `While*` bodies.
- New CLI `uv run llm4pv-partition input.c [--func name]` — dumps the
  block tree as JSON for inspection.
- Tests:
  - `list_append_raw` — `[IfWithReturn, Others]`.
  - `glibc_slist_iter_back` — same shape.
  - `list_tail` — `[WhileNoReturn, Others]` (or `[Others, WhileNoReturn,
    Others]` depending on layout).
  - Synthetic interleaved early-return.
  - Nested loop with inner early return — outer is `WhileWithReturn` due
    to transitive `return` detection.
  - Both-branches-return — `[IfWithReturn]` only, no trailing block.

**No renderer touched.**  The legacy `generate_rel_lib` runs unchanged.
Phase 1 is pure groundwork.

### Phase 2 — implement renderers for `Others`, `IfNoReturn`, `IfWithReturn`

- Renderer registry keyed on block type.
- Feature flag `--rel-lib-renderer=blocks` (default stays `legacy`).
- The block renderer covers all no-loop functions in the dataset; the
  legacy renderer continues to handle anything containing a `While*`.
- Parity tests: for every no-loop function in `shape_invdataset/`,
  legacy and block renderers must produce semantically equivalent libs
  (textually different is fine; `coqc`-equivalent is the bar).
- Flip default for no-loop functions to `blocks`.

This is when today's `list_append_raw` failure stops surfacing: there is no
`M_before` to put a call wrongly into; the call lives in the `Others` block
that follows the `IfWithReturn`, exactly where the C source puts it.  The
ad-hoc `_sync_residual_artifacts` post-synth step is no longer needed for
no-loop functions — the residual program structure is in the block tree
itself.

### Phase 3 — implement renderers for `WhileNoReturn`, `WhileWithReturn`

- Reuse the existing `M_loop_before / M_loop_M1 / M_loop_M2 / M_loop_end`
  hole conventions, driven from the block tree.
- Nested loop composition emerges from recursive block-body partitioning.
- The existing `loop_forest` infrastructure either folds into the block
  renderer (preferred) or stays as a pass that runs before block-tree
  construction (fallback).
- Flip default for loop functions to `blocks`.
- Delete the legacy `generate_rel_lib` dispatcher.

### Phase 4 (optional, after parity is established)

- Migrate `_sync_residual_artifacts` to be block-tree-driven, OR remove it
  entirely if the new renderer covers all of its responsibilities.
- Validator becomes fully block-tree-aware (today's strict-diff still works
  block-by-block, but the validator's introspection of expected holes can be
  derived from the block tree).

## Risk & Rollback

The migration is **incremental** and **flag-gated**.  Each phase is
shippable independently:

- Phase 1 changes no behavior; it can ship with confidence as long as the
  tests pass.
- Phase 2 introduces a runtime flag.  Default stays legacy until parity is
  proven; rolling back is a default-flag flip.
- Phase 3 is the last "flip"; the legacy code path stays in tree until
  Phase 3 ships green.

Rollback at any phase = revert the commit and the default flag.  The
block-tree primitives are additive until Phase 3 deletes the legacy code.

## What Stays the Same

- TransShape (C-with-shape-predicates → C-with-data-predicates).
- GuardGen (loop conditions → guardP).
- Workdir / strict-diff validator / synthesis loop.
- `_CoqProject`-aware qualified `Require Import` resolution.
- `early_result` Inductive, `repeat_break`, `safeExec`, monad primitives.

## What Changes

- `generate_rel_lib` becomes a block-tree builder + renderer dispatch.
- Three hard-coded scaffolds (loop, no-loop-early-return, opaque) collapse
  into emergent composition of the five block types.
- `_collect_func_info_with_guard` + `_enrich_func_info_with_early_return_shape`
  + a dozen flag fields converge into a single `BlockTree` value.
- `_sync_residual_artifacts` either retires or moves onto the block tree.
- Strict-diff `must_define` derivation is automated from the block tree.

## Open Questions

- **Q1.** Does the `Others` block renderer need an LLM hole for its body, or
  can the renderer mechanically compose statement-by-statement?  Calls and
  pure scalar assignments are mechanical; spatial mutations (`p->next = q`)
  need an abstract-domain interpretation.  Working assumption: one LLM hole
  per `Others` block whose body contains spatial mutations; otherwise the
  block renders fully mechanically.
- **Q2.** How should the prompt visualize the block tree to the agent — as a
  labelled diagram, or only as the named LLM holes?  Working assumption:
  show the tree, with each leaf labelled by its hole name and the C segment
  it models.
- **Q3.** Should the partitioner emit a warning when it sees a shape it
  conservatively classifies as `Others` but suspects might benefit from
  finer structure (e.g. a complex `if/else` chain inside `Others`)?  Working
  assumption: yes, with a `--strict` flag that turns warnings into errors.

These are deferred to Phase 2 design discussions; they don't affect Phase 1.
