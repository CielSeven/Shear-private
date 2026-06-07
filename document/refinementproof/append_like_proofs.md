# Append-like Proofs for Generated Refinement VCs

This note collects proof patterns that are common in append-like singly linked list refinements. These patterns are useful when the generated VC grows a list one node at a time and the abstract state carries an accumulator segment.

## A compact `sll` / `sllseg` toolbox

The general refinement tutorial already records the individual lemmas. What matters here is the append-like combination:

1. turn one concrete node into a one-element segment with `sllseg_len1`
2. append segments with `sllseg_sllseg`
3. if the tail is null, use `sll_zero` to identify it with `nil`
4. finish a segment-plus-list shape with `sllseg_sll`

When a proof feels "one node away" from the target list shape, one of these lemmas is usually the missing step.

## Common proof shapes in append-like refinement VCs

The tactics from the general refinement tutorial are local moves. In append-like VCs, they are usually combined in a small number of recurring proof shapes.

### 1. Mixed goals: solve the heap shape and the `safeExec` shape separately

Use the general workflow from [refinement_proof_tutorial.md](./refinement_proof_tutorial.md): solve the spatial side first, then normalize and discharge the remaining `safeExec` side. In append-like proofs, this pattern is especially visible because one loop step usually changes both the heap shape and the abstract accumulator state.

### 2. Loop-step witness pattern

In append-like loop proofs, one iteration usually moves one concrete node from the current cursor into the accumulated segment. A common proof skeleton is:

```coq
entailer!.
sep_apply (sllseg_len1 t w u).
sep_apply (sllseg_sllseg x t u l_acc (w :: nil)).
```

At this point the heap side says that the accumulator segment has grown by one element. The remaining obligation is typically a `safeExec` goal for the next loop state, where the abstract state must be rewritten to use the updated accumulator list.

Typical next steps are:

```coq
unfold <loop_definition> in H.
unfold_loop in H.
prog_nf in H.
```

or the corresponding normalization in the goal.

If the updated list expression is written with `+::`, use the general list-shape rewrite guidance from [refinement_proof_tutorial.md](./refinement_proof_tutorial.md).

### 3. Return-witness pattern

Return obligations often have the shape:

```coq
|- EX l_ret, [| safeExec ATrue (return l_ret) X |] && sll x l_ret
```

A common strategy is:

1. choose the intended returned logical list with `Exists ...`
2. solve the heap side using `sll_zero` or `sllseg_sll`
3. finish the execution side from the current `safeExec` hypothesis after mild normalization

Two common subcases are:

- null tail:
  ```coq
  sep_apply (sll_zero u).
  ```
  This extracts the pure fact that the tail list is `nil`.

- segment plus tail list:
  ```coq
  sep_apply (sllseg_sll x y l1 l2).
  ```
  This turns the assembled segment and tail into one complete list.

### 4. Common failure diagnoses

Some proof failures have very standard causes:

- `rewrite app_assoc` fails on a goal with `+::`
  - usually the missing lemma is `app_cons_assoc`

- `apply H` fails for a `safeExec` hypothesis that "looks the same"
  - the programs are often only extensionally the same; first normalize them with `unfold`, `unfold_loop`, or `prog_nf`

- the heap part is solved but the execution part still does not match
  - check whether one loop state has already absorbed one node, so the list arguments differ by one `+::`

When these patterns occur, the proof usually needs one missing normalization or one missing list-shape rewrite, not a fundamentally different argument.
