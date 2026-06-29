# segcodegen

Fills the LLM-parameter holes of a `*_rel_lib.v` template by reading the
matching annotated data-VC file (`*_data_autovc.c`). One proof block per
verification condition tells us how each abstract-program segment transforms
its input logical lists into its output logical lists; this module turns that
into Coq.

## Usage

```bash
python -m GenMonads.absprog.segcodegen.cli \
    bench-gen/glibc_slist/libs/glibc_slist_copy_rel_lib.v \
    bench-gen/glibc_slist/datac/autovc/glibc_slist_copy_data_autovc.c \
    -o filled.v
```

Library:

```python
from GenMonads.absprog.segcodegen import fill_template, fill_from_paths
filled = fill_from_paths("template.v", "autovc.c", "out.v")
```

### `--check`: type-check the result with Rocq

`--check` compiles the filled lib with `coqc` (building its sibling `*_rel_lib`
dependencies first, using the library-tree flags from a discoverable
`_CoqProject`, falling back to `COQ_LIB_DIR`'s project). It reports
`PASS`/`FAIL`/`SKIP` and exits non-zero on failure.

```bash
python -m GenMonads.absprog.segcodegen.cli TEMPLATE.v AUTOVC.c --check
```

This proves the synthesized `Definition`s are **well-typed Coq** (arities, tuple
shapes, notations, callee references, the `repeat_break`/`choice` scaffolding).
It does **not** prove the abstract program refines the data-VC — that is the
separate entailment-proof obligation. `check.py` holds the logic.

## Convention (loop-carrier `MretTy`)

`MretTy` is set to the **loop-carrier tuple type**. The holes map to VCs:

| hole              | source                              | meaning                                  |
|-------------------|-------------------------------------|------------------------------------------|
| `MretTy`          | template carrier type               | the loop carrier tuple                   |
| `M_loop_before`   | loop-entry `entail_wit`             | precondition list → initial carrier      |
| `M_loop_M2`       | inductive-step `entail_wit`         | one loop-body iteration                  |
| `M_loop_M1`       | (fixed) `fun r => return r`         | break branch                             |
| `M_loop_end`      | `return_wit`                        | carrier → result tuple                   |

**Picking `M_loop_end` when a function has several `return`s.** A `return` VC's
*region* is read from its context: precondition `With` existentials are emitted
as `*_free` (the **before** region — e.g. an early return before the loop),
while loop-carrier instances are not (the **loop** region). Among loop-region
returns, the loop guard (from the template's `guard-struct`) separates the
**normal loop exit** (guard false, e.g. `l3 == nil`) — which is `M_loop_end` —
from **in-loop early returns** (guard true). `regions.py` holds this; it makes
`end` selection correct for multi-return functions (a plain `_return_vc` would
wrongly grab the first `return`, which may be a before-loop early return). The
in-loop / before-loop early returns feed the `early_result` synthesis (below).

### `early_result` holes (`Continue` / `ReturnNow`)

When a function returns early from inside (or before) its loop, the template
gives `M_loop_before` and `M_loop_M2` the type `… -> MONAD (early_result S R)`:
the segment either falls through (`Continue s`, keep the carrier `s`) or returns
right now (`ReturnNow r`, the function result `r`). Such a hole is **just a
branched segment** (`synth_branched`) whose arms carry two extra things:

| arm        | source VC at that point | output group | wrap        |
|------------|-------------------------|--------------|-------------|
| `Continue` | the `entail_wit`        | carrier vars | `Continue`  |
| `ReturnNow`| a `return_wit`          | ensure vars  | `ReturnNow` |

The dispatch is exactly the region classification: `M_loop_before`'s ReturnNow
arms are the **before-region** returns (`regions.before_return_vcs`);
`M_loop_M2`'s are the **in-loop early** returns (`regions.inloop_early_return_vcs`
= loop-region returns that are *not* a normal exit — the selected `M_loop_end`
nor any guard-false return). The guard may be a **disjunction**
(`(or (atom l3 ne) (atom l4 ne))`, `merge`/`multi_merge`): the exit fires only
when *every* atom is false (`l3 = nil` and `l4 = nil`), and a normal exit reached
by several proof paths (each a guard-false return) is excluded wholesale, so no
duplicate exit leaks into `M_loop_M2`. The arms are wrapped at
construction (`synth_parts(..., wrap="Continue"|"ReturnNow")`) and composed with
the same common-prefix + `choice` as any branch. A point with no early return
(but an `early_result` type because the loop returns early elsewhere) just yields
a lone `Continue`-wrapped body, no `choice`.

What makes the `choice` sound is the SEP fact augmentation (below): the entail
(Continue) arm and the paired return (ReturnNow) arm get **complementary**
guards — e.g. `l1 <> nil` vs `l1 = nil` — so the arms are mutually exclusive and
exhaustive. This holds for null-pointer-driven early returns (every glibc_slist
case); an early return driven by a *data* comparison would need a matching rule
in `facts.py`. `glibc_slist_merge` exercises both an entry-time `ReturnNow`
(`if (x==0) return y`) and an in-loop one.

For a **no-loop** function the template has a single hole — the whole function
`_M` (e.g. `glibc_slist_clean_app_M : list Z -> list Z -> MONAD (list Z)`) and no
loop scaffolding / `MretTy`. It is synthesized by the *same* `synth_entail` from
the function's `return_wit`, with the `With` vars as inputs and the `Ensure`
vars as outputs:

```coq
Definition glibc_slist_clean_app_M : list Z -> list Z -> MONAD (list Z) :=
  fun l1 l2 =>
    r <- list_append_raw_M l1 l2;;
    return r.
```

Whether the binder is curried (`fun l1 l2 =>`, several arguments) or tupled
(`fun '(l1, l2, l3) =>`, one carrier argument) is read off the hole's type.

## Program shapes beyond the single loop

The `_segment_arms` role model — "pick which VCs are relevant, hand uniform arms
to `synth_branched`" — extends to richer control flow by adding *roles*, never by
changing the synthesizer. The template declares the shape (which holes exist);
each new role just routes to the right VCs (or, where the structure is fixed, a
type-correct passthrough).

**No-loop early return** (`list_append_raw`: `if (x==0) return y; … return x;`).
The template splits the function into `M_before : … -> MONAD (early_result MretTy
R)` and `M_normal : MretTy -> MONAD R`, with `MretTy` left abstract. Since there
is no `Inv`, the abstract carrier is the threaded inputs (the `With` vars) and
`MretTy` is defined as their tuple. `M_before` is an `early_result` branch like
any other: the **ReturnNow** arms are the before-region early returns; the
**Continue** arm threads the inputs through unchanged — a synthetic identity
entail guarded by the *negated* early-return discriminator (`l1 = nil` ⇒ the
Continue guard `l1 <> nil`), so the arms stay mutually exclusive. `M_normal` is
the straight-line tail, synthesized from the normal `return_wit` over the carrier.

**Loop forest** (`iter_back_2`: an outer loop whose body runs an inner loop). The
template names the loops `_M_loop{k}_*` and adds nesting glue — `to_inner`
(outer carrier → inner carrier before the inner loop) and `after_inner` (outer
carrier + inner result → outer carrier after it), i.e. the outer loop *calls* the
inner one. `MretTy` is the shared loop carrier. The outermost `before` is
synthesized from the loop-entry entail; the glue and per-loop `M1`/`M2`/`end`
holes that the tool leaves without VCs are filled with type-correct identity
passthroughs (`fun r => return r`, `fun a r => return r`). When the tool emits
incomplete inner VCs (degenerate invariants, ungenerated guards), this yields a
**well-typed** scaffold — not a refinement-faithful body; completing it needs the
upstream VCs.

*Design choice — the inner-loop continuation drops the parent carrier.* The
nested-loop "tail" glue (`_M_loop{k}_tail`, the continuation handed to inner loop
`k`) is typed `_M_loop{k}_MretTy -> MONAD <result>` — it takes **only** the inner
loop's result, not the parent carrier. We assume the parent carrier has already
been folded into the inner loop's carrier by `to_inner` *before* entering the
inner loop, so the inner `MretTy` is self-sufficient and there is no outer state
left to re-attach on resume. This is why `after_inner` collapses to the identity
in the common case: when `to_inner` carries the whole parent state inward, the
inner result already *is* the resumed outer carrier. Consequently `after_inner_{c}{k}`
drops its parent-carrier argument too — it is retyped `_M_loop{c}_MretTy ->
MONAD <outer-carrier>` (the identity becomes `fun r => return r`, not `fun a r =>
return r`). The cost is that we forbid
nestings where the inner loop deliberately ignores part of the parent state and
needs it back verbatim afterwards (which would require threading a parent-carrier
argument `a_p` through the tail); should such a case arise, the tail signature
would have to widen back to `MretTy -> parent_carrier -> MONAD _`. For the
current benchmark family the carry-everything-inward assumption holds.

**Recursion** (`iter_back`: `sum = iter_back(x->next); …`). A whole-function `_M`
hole whose VCs call the function itself becomes a `Fixpoint`. The arms already
synthesize the right body — a base arm (`l1 = nil`) and a step arm that calls
`…_M` on the tail — but the tail is introduced by `any`, so the self-call is not
structural. `synth_recursive` rewrites the single-input destructuring `any +
assume` into a `match` on the recursion argument, so the matched tail *is* a
subterm and the `Fixpoint` guard-checks:

```coq
Fixpoint glibc_slist_clean_iter_back_M (l1 : list Z) : MONAD (list Z) :=
  match l1 with
  | nil => return nil
  | x :: l1' => r <- glibc_slist_clean_iter_back_M l1';; return (x :: r)
  end.
```

## How a segment is synthesized

For an entailment/return VC of type `<inputs> -> MONAD <outputs>`:

1. **Inputs (provenance / roots).** The *Precondition existentials* are the
   variables *in scope* at the VC — but some of them are derived, so we trace
   each to its origin:
   - a variable is **introduced by a call** iff it is one of that call's
     *Postcondition existentials*; trace it through the call's *With-variable
     instantiation* to the actual arguments;
   - a variable that nothing introduces is a **root**, bound by the annotation
     that *precedes this VC's program point* in the code: the loop `Inv` when
     the point is inside/after that loop (loop-body step, post-loop return), or
     the function's `With`/`Require` precondition when no in-body annotation
     precedes it. The latter covers both a loop-free function *and* the
     **loop-entry** VC of a loop function — its point sits before the loop body,
     so its roots are the `With` vars (which is exactly why `M_loop_before`
     takes the `With` vars while `M_loop_M2`/`M_loop_end` take the `Inv`
     carrier).

   The roots whose base name (`l1_424` → `l1`) is in the input group are the
   segment's inputs. They may sit directly in the context (e.g. `return x;`,
   where the `With` var `l1_10_free` is itself the context existential) or be
   reached only by tracing a call (`return list_append_raw(x, y);`, whose
   context existential `l3_401` is the call result, traced back to the roots
   `l1_388_free`/`l2_387_free`). No call is assumed. Which annotation the roots
   come from is encoded by the caller's choice of input group (`With` vars vs
   `Inv` carrier). The lambda binds the canonical input names — tupled
   `fun '(l1, l2, l3) =>` for a loop carrier, or curried `fun l1 l2 =>` for a
   multi-argument function.
2. **Outputs** — each `exist_mapping` line `lN -> <term>` gives an output list
   as a term over inputs and fresh variables; the base name of `lN` fixes its
   tuple position (loop-`Inv` order for the carrier, `Ensure` order for the
   result).
3. **Fresh variables** (those in the output terms not bound as inputs) are
   collected and each is explained *before* the `return`:
   - a mapping annotated `[lR: from call to FN]` becomes
     `r <- FN_M arg1 arg2;;`, with arguments read from the matching
     `funccall_wit` block's *Callee With-variable instantiation*;
   - a leftover prop `known == term` containing the fresh var introduces
     *every* fresh var in `term` with `v <- any <ty>;;` and then
     `assume!! (known = term);;`. The **type `<ty>` is inferred** from the
     operator signatures (`GenMonads/data/list_op_signatures.json`), not
     assumed — `cons(Z, x, t)` yields `x : Z`, `t : list Z`, so the constraint
     `l2 == cons(Z, x, t)` becomes `x <- any Z;; t <- any (list Z);;
     assume!! (l2 = x :: t);;`. Nothing here is specific to lists or `cons`.

A leftover prop that introduces **no** fresh variable (e.g. `l == nil`, or a
disequality `l != nil`) is a *pure guard*; it is kept (globally) and emitted as a
bare `assume!! (l = nil)` / `assume!! (l <> nil)`. These matter for branched
segments (below) but are also kept in the single-VC case for faithfulness.

**Every** logical-list prop in `leftover_props` is covered, both `==` and `!=`:
`==` over a list constructor may introduce fresh variables (a definition), while
`!=` is always a pure guard (we never `any`-introduce variables under a
disequality — it would be vacuous). Pointer (dis)equalities such as
`x != (Ez_val 0)` are *not* covered: their RHS parses to a bare variable rather
than a list constructor, so the `isinstance(term, Op)` filter excludes them
(they feed `facts.py` instead, deriving the logical-list `!=` facts below).

**Ordering — eager / as-soon-as-ready.** Each bind is emitted the moment every
variable it mentions is in scope:
- a destructure fires when the list it splits is in scope;
- a pure guard `assume!! (v = nil)` fires immediately once `v` is in scope (so
  it lands right after whatever introduced `v`);
- a call fires once its arguments are in scope.

Dependencies dominate (a call whose argument is a destructured variable comes
after that destructure; a constraint destructing a call's *result* comes after
the call). Independent ready binds are ordered by the constraint's VC-variable
name — an intrinsic key, so sibling branches linearize their shared binds
**identically**, which is what makes the branch factoring below work. The
`return` is always last.

### Branched segments (a loop body with an inner `if`)

One program point can yield several entail VCs — `entail_wit_2_1`,
`entail_wit_2_2`, … all re-establish the same invariant along different paths,
so they fill the *one* `M_loop_M2` hole. They are grouped by their leading wit
number. Each arm is synthesized independently into (binder, binds, return); the
**longest common bind prefix** is emitted once and the divergent tails combined
with `choice`:

```coq
fun '(l1, l2) =>
  x  <- any Z;;
  l1' <- any (list Z);;
  assume!! (l1 = x :: l1');;          (* common prefix *)
  choice
    ( x0 <- any Z;; l1'' <- any (list Z);; assume!! (l1' = x0 :: l1'');;
      return (l1'', x0 :: (x :: l2)) )   (* arm: l1' is a cons *)
    ( assume!! (l1' = nil);;
      return (nil, x :: l2) ).           (* arm: l1' is nil *)
```

The first divergent bind of each arm *is* its discriminating guard
(`assume!! (l1' = x0 :: l1'')` vs `assume!! (l1' = nil)`); because a list is
`nil` xor `cons`, the arms are mutually exclusive and the `choice` is
deterministic. This is exactly why pure guards must be kept: in arm 2 the
`l1' = nil` constraint contributes no output variable, but it is the guard that
makes the branch sound.

### Fact augmentation from the SEP antecedent

Each proof block now carries its separation-logic antecedent:

```
Separation-logic state (antecedent P):
SEP[ sll(x_385_pre, l1_388_free); sll(y_382_pre, l2_387_free) ]
```

`facts.augment` derives logical-list facts by combining a heap predicate with a
pointer (dis)equality, mirroring guardgen's predicate rules:

```
sll(p, l)  with  p == (Ez_val 0)   =>   l == nil(Z)
sll(p, l)  with  p != (Ez_val 0)   =>   l != nil(Z)
```

Derived facts are appended to `leftover_props` (skipping any already present).
This is what makes a **Continue** arm self-sufficient: an entailment that only
states the pointer fact `x != (Ez_val 0)` gains `l1 != nil(Z)` directly, so its
list discriminator no longer has to be inferred as the complement of the paired
early return. Rules live in `facts.RULES` (currently `sll`; extensible).

### Data witnesses & pointer existentials (the abstract state's shape)

A loop `Inv exists …` (or `Ensure exists …`) binds more than the abstract
state's logical lists: it also binds the program's **pointer** existentials (the
`next` field, `x_next`) and any scalar **data witnesses** (the `Z` value carried
out of a node, `x_v` in `list_tail`). The abstract carrier / result tuple holds
only the logical ones — `witness.py` resolves which is which **from the
registered operator signatures**, never by name:

- a component mapped to a list constructor, or to a variable the signatures type
  as `list T`, is a **list**;
- a component mapped to a variable typed as a `cons`/`app` *element* `T` (e.g.
  `x_v -> x_427_free` where `cons(Z, x_427_free, …)`) is a **witness** (scalar);
- a component with no inferable logical type (it only appears in pointer/`store`
  positions) is dropped.

The surplus over the template's declared component count
(`(list Z * list Z * Z)`) is dropped (the pointer existentials), and the
survivors are ordered to the template's slots — so `list_tail`'s
`Inv exists x_next x_v l1 l2` becomes the carrier `(l1, l2, x_v)`, dropping
`x_next`. The witness itself needs **no** synthesis change: it is produced
exactly like any `cons` element (`x_v <- any Z`). List-only functions are
untouched (no surplus, no witnesses → identity).

A data witness is not always a carried *element*: in `iter` it is an
**accumulated sum** — `s -> (s + x)` (the step) and `s -> (Ez_val 0)` (the loop
entry), and both live in the VC's **`EliminateLocal`** section rather than its
`exist_mapping`. Two registry-driven pieces handle this, with **no** synthesis
change:

* `+` is just another registered operator (see below), parsed from its infix
  proof-block syntax and rendered as Coq `+`; its `result: scalar` is what tells
  `witness.py` the component is a `Z` witness (sorted into the `Z` slot), not a
  list.
* `_merge_witness_substitutions` (in `__init__.py`) lifts each `EliminateLocal`
  substitution whose base name is a logical carrier/ensure component into the
  `exist_mapping` the synthesizer reads, stripping the `Ez_val` val-coercion in
  this scalar context (`(Ez_val 0)` → `0`). The witness is then produced like
  any other output term (`return (l1 ++ (x :: nil), l2', s + x)`).

### A scalar witness carried as a bare flag/literal

A data witness is not always reachable through an operator. A boolean **flag**
(`multi_merge`'s `take_y`, the carrier's `ty`) is assigned literal `0`/`1` per
branch, so its `exist_mapping` (`ty -> 1`) carries no operator/type evidence for
the inference above. It is still a scalar: the registry-style signal is its
**store type** — `store(&take_y, int, ty)` stores an *int*, not a pointer.
`vcparse.scalar_witness_bases` collects the base names stored at any non-pointer C
type (`int`/`long`/…), and `witness._classify` treats those as scalar `Z`
witnesses outright, sorting them into the carrier's `Z` slot. The branch guards
that toggle the flag (`ty == 0`, `ty != 0`) ride along as the pure scalar
`assume!!` guards already covered above.

### Multi-result calls

A callee may return several logical values at once —
`list_tail : list Z -> MONAD (list Z * Z)` returns a prefix list *and* the popped
element. Its results appear together in one `funccall_wit`'s *Postcondition
existentials*, in the callee's result-tuple order. One bind destructures the
whole tuple result with a pattern (`'(r1, r2) <- …`), binding a fresh name per
component:

```coq
'(r1, r2) <- list_tail_M l1;;
return (r1 ++ (r2 :: l2)).
```

How many components a call contributes is read from the **output cone** — the
variables that actually flow into the result tuple (reached from the output
terms through constructor equations and chained-call arguments). A
post-existential that feeds only a *dropped* witness (e.g. the numeric return of
a list-returning recursive call) is therefore not mistaken for an extra tuple
component, so a single-list callee stays a single bind.

### Operator signatures are external data

`GenMonads/data/list_op_signatures.json` describes each term operator:
whether its first argument is the element type (`type_arg`), the role of each
operand (`elem`/`scalar` → `T`, `list` → `list T`) for type inference, how it is
written in proof blocks (`parse`: `call` = `head(args)`, `infix` = `a SYM b`),
how to render it in Coq (`render`), and the kind of value it yields (`result`:
`list` vs `scalar`). Add an operator there to support it — the generator code
stays unchanged. For example, `add` (`+`) is `parse: infix "+"`,
`render: infix "+"`, `result: scalar`, with `Z` operands — nothing about `+` is
hardcoded in `terms.py`.

## Files

- `terms.py` — signature-driven term AST + parser, type inference
  (`collect_var_types`), and Coq renderer; loads the operator registry.
- `vcparse.py` — parse the spec (`With`/`Inv`/`Ensure`) and the `/* !!! ... !!! */`
  proof blocks.
- `template.py` — locate the `Parameter` holes and the carrier type.
- `regions.py` — classify entail/return VCs by program region (before/loop) and
  pick the loop-exit return for `M_loop_end` (multi-return safe).
- `facts.py` — augment a VC's leftover props with logical-list facts derived
  from its `SEP[...]` antecedent (see below).
- `witness.py` — resolve a function's `Inv`/`Ensure` existentials into the
  abstract state's logical components (lists + scalar data witnesses), dropping
  pointer existentials and ordering to the template tuple (see below).
- `synth.py` — `referenced_funccalls` (the funccall blocks a VC depends on,
  transitively over list dataflow; usually empty), `synth_parts`/`synth_entail`
  (synthesize one segment from its VC + those precomputed dependencies), and
  `synth_branched` (combine several branch VCs into one segment via a common
  prefix + `choice`).
- `__init__.py` — orchestration (`fill_template`, `fill_from_paths`). Every
  VC-driven hole (`before`/`M2`/`end`/`M`, plus the new shapes' `before_noloop`/
  `normal`/`fbefore`) goes through **one** path: `_segment_arms` picks the
  relevant VCs (the *only* role-specific logic) and hands a list of arms to
  `synth_branched`. Whether the hole is curried, branched, or `early_result` is
  encoded entirely in the arms — single vs many, the per-arm output group, and
  the per-arm `Continue`/`ReturnNow` wrap — not in the dispatch. Relevant VCs are
  scoped to the hole's own function, so in a multi-function file one function's
  returns never leak into another's loop body (and a no-loop `M` with several
  returns simply becomes a branched segment). The non-VC-driven holes are
  `MretTy` (a type definition), `M_loop_M1` (the fixed break branch), the loop
  forest's identity glue (`fM1`/`fM2`/`fend`/`to_inner`/`after_inner`), and a
  self-recursive `M` (emitted as a `Fixpoint` over a `match` — `synth_recursive`).
- `cli.py` — command-line entry point.
