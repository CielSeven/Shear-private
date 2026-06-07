# Plan: skill for adding `assert` to abstract programs to unlock manual proofs

> **Generality (do not over-fit).** The abstract program is whatever monadic
> program the `*_rel.c` references via its `Extern Coq` block — it may be
> **hand-written** (e.g. `MonadLib/Examples/kmp.v`) or generated, built from
> `repeat_break` / `range_iter` / `range_iter_break` / `while` / recursion, and
> organized in `Section`s with several loops. The most common assert is an
> **array-index bound** at the *top of a loop body* (e.g. `assert (0 <= j <
> Zlength str)` so `str[j]` is safe), not an overflow bound and not the
> synthesized `M_loop_M1/M2` scaffold. See `tutorial/kmp.md`.

## Problem

`symexec` generates manual proof goals (`*_entail_wit_*`, `*_return_wit_*`,
`*_safety_wit_*`) for a `*_rel.c` file. Some are **unprovable** because they
need *value/range* facts that the abstract program does not expose. Example
(`glibc_slist_clean_iter_back_2`): the C statement `sum += node->data` must not
overflow, which needs `-100 <= data <= 100` and a bound on the accumulator — but
the synthesized `M_loop_M2` is

```coq
fun a => let '(l, s) := a in
  l' <- any (list Z);;  v <- any Z;;
  assume!! (l = l' ++ v :: nil);;
  return (l', s + v).
```

so the goal's `safeExec` hypothesis carries no bound on `v` or `s`.

## The mechanism (MonadErr `assert` + `safeExec`)

- `assert P` errors exactly when `~P` (`monadlib/MonadErr/MonadErrBasic.v:102`);
  `assertS P` is its state-dependent form (`:106`).
- `safeExec`'s `weakestpre` carries `~ c.(err) σ` (`MonadErr/MonadErrHoare.v:1454`),
  so a `safeExec … (assert P ;; c) …` hypothesis **implies `P`**.
- The function's Require already provides the range precondition:
  `…_range(l1) && safeExec(ATrue, M(l1), X) && sll(x,l1)`.
- Inserting `assert (range-derived fact)` into `M` makes every goal's loop-state
  `safeExec` hypothesis yield that fact, extracted with `safeExec_assert_seq`
  (`monadesafe_lib.v:629`) / the `safe_step` tactic (`:772`). The extracted bound
  then discharges the arithmetic obligation.

This is cleaner than the existing hand-crafted `_v1_` example
(`glibc_slist_iter_back_2_rel_v1_manual_try3/`), which instead carried a stronger
loop invariant (extra `lfull` component) plus manual range lemmas threaded through
every entailment goal. The `assert` approach keeps the program's state shape and
injects the per-state facts through the program structure itself.

### Hard soundness gate (the crux the user stressed)

Adding `assert P` strengthens `M`, so the spec stays **sound only if `range(l1)`
makes every assert non-erroring along every reachable loop state.** Each asserted
`P` must be **exactly** entailed by `range(l1)` + the reachable state:

- **Over-asserting** (stronger than `range` gives) ⇒ `M` errors on valid inputs ⇒
  `safeExec(ATrue, M(l1), X)` unrealizable ⇒ spec vacuous/unsound.
- **Under-asserting** ⇒ goals still unprovable.

So the asserts must hit precisely the entailed facts the goals consume, and must
be backed by lib lemmas proving they follow from `range`.

## Prerequisite

`assert`/`assertS` are **MonadErr-only** primitives — StateRelMonad has no error
primitives. So this skill applies only when the lib was generated with
`--monad staterr` (the backend added earlier). The abstract program must already
be in MonadErr (`Export StateRelMonadErr.`).

## Skill scope (decided)

**Insert asserts + lib lemmas only**, and **general + tool-driven** (not specific
to any one function). Two scripts bracket the LLM edit:

1. `scripts/extract_unproved_goals.py` — packages the unprovable goals'
   symbolic-execution info into JSON so the LLM gets a structured digest, not raw `.v`.
2. The LLM reads the JSON + lib, inserts `assert`/`assertS` into the abstract
   program, and appends soundness lemmas.
3. `scripts/verify_assert_edit.py` — proves the edit added **only** asserts (plus
   append-only new lemmas) and changed nothing else; optional `coqc` gate.

It then **hands off** VC regeneration (`symexec`) and goal-proving to the existing
`vc-proving` / `refinement-vc-solver` skill (which `safe_step H` to pull each
asserted fact out).

### `extract_unproved_goals.py` (built + tested)
Reads `<base>_rel_goal.v` (statements) + `<base>_rel_manual.v` (`Admitted` = open;
or a `proof_report.json` with `status != solved`), optional `_rel.c`. Emits
`assert_goals.json` with per-goal `statement`, `hypotheses_pure`,
`safeExec_hypotheses`, `abstract_programs_referenced`, `range_predicates_in_goal`.
Verified on the real `output/gen/vcs/glibc_slist_iter_back_2_rel_*.v`: 7 open
goals, range predicate detected, `range_predicates_in_goal: []` on inner loop
goals — the precise signal that range never reached them.

### `verify_assert_edit.py` (built + tested)
Diffs the edited lib vs its `.bak`; strips monadic-assert lines
(`^<ws>assertS?(...) ;;<ws>$`), and the remainder must equal the baseline as a
prefix with only an append-only trailing region. Reports `assert_only_ok` +
inserted asserts (with enclosing definition) + appended blocks + violations;
optional `--coqc-cmd` compile gate. Verified: insert-assert + append-lemma passes;
a one-line program change (`return (l1,0)` → `return (l1,42)`) is rejected with the
exact diff.

## Per-goal LLM reasoning (driven by the JSON)

Read the actual abstract program — do not assume its shape.

1. **Diagnose** — for each failing goal, classify the missing fact: most often an
   **array-index/length bound** for a safe access (`0 <= i < Zlength arr`),
   sometimes an arithmetic/overflow or element bound.
2. **Localize** — place each assert at the program point matching the failing C
   operation, over the variables live there. For loop accesses this is usually the
   **top of the relevant loop body**, before the access (e.g. `assert (0 <= j <
   Zlength str);;` at the start of `inner_body`). There is no fixed scaffold.
3. **Insert minimal asserts** — `assert (P);;` (pure) or `assertS` (state-dependent),
   exactly the fact the goal consumes — no more.
4. **Append soundness material (never modify existing defs):** a Hoare triple (or
   invariant lemma) showing each asserted `P` holds under the function's `Require`
   on every reachable state — proved once via `Hoare_range_iter` /
   `Hoare_repeat_break` / `Hoare_range_iter_break` (see `inner_jrange_inv` in
   `kmp.v`). The entailing facts come from `Require` (array lengths, loop bounds, an
   explicit `*_range`, …), not necessarily a `*_range` predicate.
5. **Verify** with `verify_assert_edit.py` — `assert_only_ok` must be true with no
   violations (and compile if `--coqc-cmd` given).
6. **Hand off** — the program changed, so VCs must be regenerated and re-proved by
   the `vc-proving` skill; its proofs do `unfold_loop` + `safe_step` to extract each
   asserted fact (see `tutorial/kmp.md`).

## Reference card the skill must carry (verbatim names)

| Name | File | Use |
|---|---|---|
| `assert (P:Prop)` / `assertS (P:Σ->Prop)` | `MonadErrBasic.v:102,106` | the primitives to insert |
| `safeExec_assert_seq` | `monadesafe_lib.v:629` | `safeExec P (assert B;; c) X -> B /\ safeExec P c X` |
| `safeExec_assertS_seq` | `monadesafe_lib.v:641` | state-dependent version |
| `safe_step H` | `monadesafe_lib.v:772` | auto-extracts asserts/assumes from a `safeExec` hyp |
| `safeExec_any_bind` | `monadesafe_lib.v:574` | resolve an `any A` by a witness |
| `prog_nf [in H]` | `MonadErrBasic.v:707` | normalize bind/choice/ret |

## Skill layout (`.codex/skills/abstract-program-assert/`) — built

```
SKILL.md                                 # general workflow, soundness gate, reference card
scripts/
  extract_unproved_goals.py              # symexec/goal info -> assert_goals.json
  verify_assert_edit.py                  # assert-only diff gate (+ optional coqc)
tutorial/
  kmp.md                                 # canonical: hand-written multi-loop, index-bound asserts
  glibc_slist_clean_iter_back_2.md       # simpler variant: generated single-loop, overflow asserts
```

## Open questions

1. `function_require` parsing in the extractor is best-effort regex; if rel.c spec
   formatting varies it may need hardening.
2. Multi-loop / multi-function files: assert per loop section; confirm the
   per-function `{func}_` prefixing is respected (extractor already filters refs by
   detected base).
3. The verifier currently focuses on the lib; if we want to also assert that
   `_rel.c` / `_rel_goal.v` were untouched by the LLM, add their `.bak` compares
   (today the LLM only writes the lib, so it is implied).
