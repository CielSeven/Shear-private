# Improving qcp-mcp Annotation Precision

## Problem

When qcp-mcp generates annotations (e.g. in `output/gen/rel/sll/sll_multi_merge_rel.c`), existential variables often appear with no constraints even though the `check` tool can recover those facts.

Example from the `z == 0` branch of `sll_multi_merge`:

```c
/*@ exists v1 v2 l1 l2 l4,
    z == 0 && v2 == t->data && t != 0 && x@pre != 0 && u != 0 &&
    safeExec(ATrue, bind(sll_merge_M(l1, l2),
                         residual_prog_in_sll_multi_merge_M_call_3(l4, v1, v2)), X) &&
    sll(u, l1) * sll(y, l2) */
```

`v1` is introduced but never pinned. `check` at this program point would report
`v1 == u->data` (since `u != 0` and `v1` is the head of the `sll(u, ...)` list),
but the LLM did not include it. The annotation is weaker than what is actually
provable, which makes downstream refinement proofs harder or unsound.

## Root cause

The LLM is writing annotations one-shot from surface context, without
consulting `check` for ground-truth facts at the annotation point. It tends to
leave existentials naked whenever the fact isn't syntactically obvious from
nearby C code.

## Proposed fix — three layered changes to the prompting pipeline

### 1. Pre-seed the prompt with `check` output (highest leverage)

Before asking the LLM to write an assertion at a given program point, run
`check` at that point first and paste the returned facts into the prompt as
ground truth. The LLM then refines from a known-strong fact set instead of
guessing which existentials to constrain.

Concretely: the annotation task becomes
"here is the set of facts `check` reports hold at this point; write an
`exists` clause that exposes every fact relevant to the subsequent `safeExec`
obligation, using these names."

### 2. Iterative refine loop (guarantees strength)

One-shot is not enough — even with `check` facts in context, the LLM will drop
some. Wrap generation in a loop:

1. LLM emits a draft annotation.
2. Run `check` at the same program point.
3. Diff `check`'s facts against what the draft annotation exposes.
4. If any fact about a bound existential is missing, feed it back:
   *"`check` reports `v1 == u->data`; your exists clause omits this — revise."*
5. Repeat until the annotation entails every fact `check` knows about the
   variables it binds.

This is the one change that actually *guarantees* the annotation is as strong
as `check` can prove. Without the loop, (1) and (3) still let the model skip
facts silently.

### 3. Explicit rule + few-shot examples in the system prompt

Add to the system prompt:

> For every existential variable introduced in an annotation, if `check`
> yields an equality or shape fact about it, the annotation **must** include
> that fact. Naked existentials are only acceptable when `check` has nothing
> to say about the variable.

Pair with 1–2 before/after examples, e.g.:

- Before: `exists v1 v2 l1 l2 l4, ... safeExec(..., ..._call_3(l4, v1, v2)) && sll(u, l1) * sll(y, l2)`
- After:  `exists v1 v2 l1 l2 l4, ... && v1 == u->data && v2 == t->data && ... && sll(u, l1) * sll(y, l2)`

Alone this is soft guidance and the model will still miss facts; it earns its
keep as a reinforcement on top of (1)+(2).

## Recommended ordering

(1) + (2) move the needle. (3) is cheap reinforcement. Implement in that
order — do not skip (2), because the loop is what makes precision a
post-condition of generation rather than a hope.

## Open questions

- What is the exact API surface of qcp-mcp's `check` tool — does it return a
  machine-parseable fact list, or free-form text? The diff step in (2)
  requires the former; if only the latter is available, add a structured
  output format to `check` first.
- Should the loop have a max iteration bound, and what to do on non-convergence
  (e.g. `check` depends on a fact the LLM refuses to emit)? Suggest bound = 3
  and fall back to emitting the annotation with a `TODO: missing fact X` marker
  so humans can audit.
- Are there annotation points where exposing every `check` fact would bloat
  the assertion unhelpfully? If so, filter by "facts about variables bound in
  this `exists`" rather than "all facts in scope".

---

## Abstract-program / concrete-heap reconciliation for mid-body annotations

### Problem observed (2026-04-14 session)

At annotation points inside a loop body, the LLM copies the separation
conjuncts of the loop invariant verbatim — even when pointer-mutating
statements between the invariant and the annotation point have already
changed the heap.

Concrete example from `sll_multi_merge`:

The loop invariant says, among other things,
`safeExec(ATrue, bind(sll_multi_merge_M_loop(ly, lz, lu, lprefix, v), ...), X) && ... * sllseg(x@pre, t, lprefix)`.

Inside the loop body, the `if (y)` branch executes:

```c
t->next = y;
t = y;
y = y->next;
```

At the subsequent `z == 0` branch the LLM wrote
`sllseg(x@pre, t, lprefix)` but the correct spatial conjunct is
`sllseg(x@pre, t, app(lprefix, cons(v, nil)))` — the segment has grown by
one element.

### The real failure mode: abstract program pins the old names, heap has moved on

This is not fundamentally a "the LLM forgot to track spatial state" bug.
The deeper structural fact is:

- The **abstract program argument** inside `safeExec(..., bind(M_loop(<args>), ...), X)`
  at a mid-body annotation **must continue to use the loop invariant's
  logical variables verbatim** (`ly`, `lz`, `lu`, `lprefix`, `v` in the
  example). The abstract program logically fires at the start of the
  iteration; its arguments are frozen to the invariant's snapshot.

- The **concrete heap** at P has been mutated since the invariant was
  last established, so the separation conjuncts at P describe a
  *different* heap from the invariant's.

The annotation at P must therefore express the current concrete heap
**as a term built from the invariant's logical variables** — because
those variables are exactly the ones the abstract program still refers
to, and the annotation has to be self-consistent between its abstract
and spatial halves.

The spatial transition (how pointer mutations reshape the heap) is the
bridge that lets us describe the new heap in old-variable terms. That
is what the LLM skipped: it treated the invariant's spatial conjuncts
as a static label and copied them, instead of recomputing the
current-heap-in-old-variables expression.

### Why `check` alone does not catch this

`check` reports facts at a given program point, but its output uses
QCP-internal names (`l0_214`, `l1_215`, ...) that do not transparently
map back to the LLM's chosen binder names (`lprefix`, `ly`, ...). The
LLM can see shape predicates in `check`'s output, but to connect them
to its own `lprefix` it must understand how `lprefix` has evolved — and
that is precisely the step it skipped.

### Proposed solution

Before writing any annotation at a mid-body point P, the LLM must
reconcile the abstract program half and the spatial half:

1. **Freeze abstract-program arguments.** The `M_loop(...)` (or analogous
   residual) call at P must use the loop invariant's logical variables
   unchanged. Do not introduce fresh existentials for the arguments
   when invariant variables are already in scope.

2. **Rebuild spatial conjuncts in those same variables.** Walk the
   pointer-mutating statements between the invariant and P along the
   specific branch leading to P, in execution order. For each mutation,
   update each separation predicate according to the appropriate
   folding/unfolding rule for the predicate family in use (list, list
   segment, tree, doubly-linked list, etc.) — the predicate's own
   definition and lemmas are the authority, not any single schema.

3. **Express the final heap as a term in the invariant's variables.**
   Typical transforms: a traversal step converts `pred(p, l)` into
   `pred(p', l')` where `l = combine(head_elements, l')`; a re-link
   step grows a segment predicate by the elements that were spliced in;
   a detach step removes a cell from one predicate and either rewires
   it into another or leaves it as a standalone cell until rewired.

4. **Red flag.** If P's spatial conjuncts are textually identical to
   the invariant's despite pointer mutations having occurred, the
   annotation is almost certainly wrong. Either no mutations happened
   (fine) or you copied instead of transformed (fix before shipping).

#### When this applies

- Always, when the annotation point P is inside a loop body and at
  least one pointer-mutating statement (assignment to a struct field,
  or reassignment of a pointer variable) lies between the loop
  invariant and P along the branch reaching P.
- Not required when P is immediately after the loop (the invariant
  plus the negated loop condition is the correct state).
- Not required at the top of the loop body before any mutations.

#### How to integrate into the existing skill loop

Insert as **Step 1.5** between Step 1 (pre-check) and Step 2 (draft).
Keep the working as working notes, not emitted into the file.

> **Step 1.5 — Abstract/concrete reconciliation (loop-body annotations only)**
>
> The abstract program argument at P takes the loop invariant's logical
> variables as-is. The separation conjuncts at P describe the *current*
> heap, expressed as terms built from those same invariant variables.
> If pointer mutations lie between the invariant and P:
>
> 1. Identify the invariant's abstract-program arguments and list
>    existentials — these are frozen names for both halves of the
>    annotation.
> 2. Walk the pointer-mutating statements between the invariant and P
>    along the branch reaching P.
> 3. For each mutation, apply the appropriate fold/unfold rule for the
>    predicate family involved to obtain the current heap as an
>    expression in the invariant's variables.
> 4. Write the annotation: abstract program uses the invariant's
>    variables directly; spatial conjuncts use the expressions derived
>    in step 3.
>
> Red flag: textually-identical spatial parts across the invariant and P
> when mutations have occurred almost always means step 3 was skipped.

#### Open questions

- Should the reconciliation working be emitted as a `// Trace:` comment
  for human review, or kept in the agent's working notes only? Leaning
  toward working notes, but during skill development a visible trace
  would help debugging.
- How to handle branches that rejoin — follow the specific branch to P,
  not both sides of an `if/else`.
- Can `step` (or an analogous qcp-mcp tool) return per-statement heap
  state that already uses the invariant's variable names? If so, the
  LLM reads rather than derives the reconciliation, making this the (B)
  driver-script analogue for the problem.
- Is there a lightweight entailment check (e.g. a qcp-mcp tool or Coq
  lemma set) that verifies "the annotation's spatial part entails the
  predicates `check` reports at P"? That would be a mechanical audit
  of step 3's correctness, independent of which predicate family is
  involved.
