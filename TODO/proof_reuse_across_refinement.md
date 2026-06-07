# Proof Reuse Across Annotation Refinement

## Problem

Annotations are sometimes not correct/strong enough on the first try, so the
VCs they generate cannot all be proved. The annotations later get refined
(**not our task**) and the VCs are **regenerated**. Regeneration rewrites the
`_goal.v` definitions and the `_manual.v` lemma list, so:

- Some VCs are byte-for-byte the same as before (the refinement didn't touch
  that path) — their old proofs should still work verbatim.
- Some VCs changed slightly (a witness shape, an extra conjunct) — their old
  proofs are a strong starting point but need adapting.
- Some VCs are genuinely new.

Today, when we re-run the `refinement-vc-solver` skill on a regenerated manual
file, every goal starts from scratch. Any proof effort from the previous round
is thrown away, even for VCs that did not change. This is wasteful and, for
large files, dominates the cost.

Our task is still **only to prove the VCs** — we do not edit annotations. But
after a refinement there is now a pool of **old proofs** that we should mine.

## Goal

When proving a regenerated manual file, automatically reuse proofs from prior
rounds:

1. **Unchanged VC → free win.** If the underlying goal is identical to one we
   proved before, splice the old proof in and recompile. If it still compiles,
   mark it solved without invoking the LLM agent.
2. **Changed-but-similar VC → warm start.** If the goal is close to a
   previously-proved goal, hand the old proof to the agent as a reference to
   adapt, instead of starting cold.
3. **New VC → cold start.** Unchanged behavior.

Hard constraint (carry over from [refinement_vc_no_cheat_plan.md](./refinement_vc_no_cheat_plan.md)):
**no archived proof is ever merged without recompiling it against the current
goal + lib.** Reuse is a shortcut to a *candidate* proof, never a shortcut past
verification.

## Key design fact: match on goal content, not lemma name

The manual file only contains `Lemma proof_of_X_entail_wit_N : X_entail_wit_N.`
The real content of the VC is the `Definition X_entail_wit_N := <entailment>` in
the companion `_goal.v`. When annotations change:

- `entail_wit_N` numbering **shifts** (a new witness in the middle renumbers the
  rest), so the lemma name is an unreliable key.
- Two regenerations can both have an `entail_wit_2` that mean completely
  different entailments.

Therefore the identity of a VC for reuse purposes is a **normalized hash of the
underlying goal definition body**, read from `_goal.v`. The lemma name is kept
only as a weak secondary signal.

## Proposed Design

Four pieces: an **archive**, a **matcher**, a **fast-path reuse gate**, and an
**agent hint injector**. They slot into the existing five-step skill workflow.

### 1. Proof archive (persistent)

A per-project cache that accumulates confirmed proofs across runs.

**The archive unit is the goal file.** A goal file (one function) has many proof
obligations; some are auto-discharged by the strategies, and the rest are proved
manually in `_manual.v`. Only the manually-solved lemmas carry a reusable proof,
so the archive stores exactly those. One obligation can fan out into a family of
sub-lemmas `entail_wit_N_1 … _N_k` (one per branch of the entailment); each is a
separate lemma with its own goal body and proof, hence its own entry.

- **Location / layout:** **one file per goal file** —
  `<vcs-dir>/.proof_archive/<basename>.jsonl`. Default dir is
  `<vcs-dir>/.proof_archive/` (sibling of the manual files); override via
  `CONFIGURE` key `PROOF_ARCHIVE_DIR` or a CLI flag.
- **One entry per manually-solved lemma**, keyed by `goal_hash`:
  - `goal_hash` — normalized hash of the **literal RHS body** of
    `Definition <name> := <body>` in `_goal.v` (whitespace-collapsed,
    comment-stripped). No transitive expansion: in these files the body is
    always a fully-inlined `forall … |-- EX …` entailment over primitive
    predicates (`listrep`, `lseg`, points-to, pure props) — it never references
    other named `Definition`s — so the literal text is the goal's true identity.
  - `basename` — e.g. `sll_zip_rel` (also the archive file's name).
  - `lemma_name` — e.g. `proof_of_sll_zip_entail_wit_2_1` (secondary key).
  - `statement_body` — the normalized definition body (for similarity scoring
    and human inspection).
  - `proof_block` — the `Proof. … Qed.` text.
  - `lib_fingerprint` — hash of the `_rel_lib.v` it was proved against, so we can
    detect when the lib moved underneath the proof.
  - `created_at`.
- **Writer:** `validate_and_merge.py` archives each lemma right after it confirms
  it as `solved` (compiles, no `Admitted.`); equivalently, `archive_solved_manual`
  batch-archives a whole solved manual file. Re-proving an existing `goal_hash`
  refreshes the entry (newest wins).
- Stored as newline-delimited JSON (`<basename>.jsonl`), so it is greppable and
  diffable.

### 2. Matcher — classify each new goal against the archive

New script `seed_from_archive.py <manifest> [--archive DIR]`, run as **Step 1.5**
(after `split_manual_goals.py`, before `prepare_agent*.py`).

For each goal in the manifest:

1. Resolve its underlying definition body from the regenerated `_goal.v` and
   compute `goal_hash`.
2. Look up the archive:
   - **`exact`** — `goal_hash` matches an archived entry. Strong candidate for
     verbatim reuse.
   - **`name_match`** — `lemma_name` matches but `goal_hash` differs. Reference.
   - **`similar`** — token/AST similarity of `statement_body` to some archived
     entry exceeds a threshold (start with a cheap token-set Jaccard; AST-level
     can come later). Reference. Keep the top-1 (or top-k) match.
   - **`none`** — no useful match.
3. Annotate the manifest entry with `reuse_class`, the matched
   `archived_proof_ref` (archive id), and the matched `lib_fingerprint`.

The matcher only reads/writes the manifest and archive — it never edits goal
files. This keeps it composable with both sequential and concurrent prepare.

### 3. Fast-path reuse gate (exact matches → no agent)

New script `apply_archived_proofs.py <manifest> [--archive DIR]`, run after
`prepare_agent*.py` and **before** `run_agent*.py`.

For every goal with `reuse_class == "exact"`:

1. Splice the archived `proof_block` into the prepared split goal file.
2. Recompile it against the **current** lib (reuse `check_rocq_file_with_deps`).
3. **Compiles** → mark the goal `solved` in a `reuse_report.json`; the runner
   skips it (no LLM spend).
4. **Fails** (lib changed, goal subtly different despite hash collision risk,
   etc.) → revert the splice and **demote** the goal to a `similar` reference so
   the agent still gets the old proof as a hint.

This gate is the no-cheat boundary: an exact match is *trusted only after it
recompiles*. A stale or coincidental match degrades gracefully to a hint.

### 4. Agent hint injection (similar / name_match / demoted-exact)

In `prepare_agent.py` / `prepare_group_workdir.py`, for goals with a reference
proof, embed the old proof in the split goal file as a clearly-delimited
comment the agent is told to adapt — e.g.:

```coq
(* === PRIOR PROOF (reuse_class: similar; goal changed since last round) ===
   The statement below differs from the one this proof was written for.
   Use it as a starting point: keep the tactic skeleton, re-derive witnesses
   and rewrites for the current goal. Do NOT assume it compiles as-is.
   <archived proof_block>
   === END PRIOR PROOF === *)
```

`AGENTS.md` gets a short section: "Some goals carry a PRIOR PROOF block — prefer
adapting it over starting cold, but always recompile; never paste it blindly."

### 5. Bootstrapping the archive on the first refinement

On the very first refinement there is no archive yet. Two supported sources:

- **Accumulated archive** (normal path): the archive is populated by the v1
  proving run's `validate_and_merge.py`. Nothing extra to do.
- **Seed from a prior manual/goal pair** (one-off): `seed_from_archive.py
  --from-manual <old_manual.v> --from-goal <old_goal.v>` ingests proofs straight
  from the previous (e.g. git-stashed or `.bak`) files into the archive before
  matching. Useful when v1 proofs live in a file rather than the cache.

## Pipeline Integration (summary)

```
Step 1   split_manual_goals.py              (unchanged)
Step 1.5 seed_from_archive.py    <-- NEW    classify goals vs archive, annotate manifest
Step 2   prepare_agent*.py                  (extended: inject PRIOR PROOF hints)
Step 2.5 apply_archived_proofs.py <-- NEW   exact matches: splice + recompile; skip-list for runner
Step 3   run_agent*.py                       (extended: skip goals already solved by 2.5)
Step 4   validate_and_merge.py               (extended: archive each confirmed-solved proof)
Step 5   verify_manual_goals.py              (unchanged)
```

## Acceptance Criteria

- An unchanged VC across a regeneration is solved by the fast-path gate with no
  LLM agent invocation, and only after it recompiles against the current lib.
- A changed-but-similar VC reaches the agent with the old proof embedded as a
  PRIOR PROOF reference; the agent is instructed to adapt, not paste.
- VC matching is content-based (`goal_hash` over the `_goal.v` definition body),
  robust to `entail_wit_N` renumbering.
- No archived proof is ever merged without recompiling — the no-cheat invariant
  holds.
- The archive is refreshed by every confirmed-solved goal, so reuse improves
  monotonically across refinement rounds.
- Works in both sequential and concurrent modes (the matcher/gate operate on the
  manifest, before grouping).
- A run with an empty archive behaves exactly like today (graceful no-op).

## Open Questions / Risks

- **Similarity metric.** Start with token-set Jaccard on the normalized
  definition body; revisit with an AST/structural metric if the warm-start hit
  rate is poor. Needs a tunable threshold (`--similar-threshold`).
- **`goal_hash` normalization.** Canonicalize whitespace and comments; consider
  alpha-renaming binder names so cosmetic regeneration noise doesn't defeat
  exact matches. Over-normalizing risks false `exact` matches — but the recompile
  gate catches those, so bias toward more normalization. (Transitive definition
  expansion is *not* needed: goal bodies are fully inlined — see §1.)
- **Headers are stable.** The `Require Import` prelude is stable per basename, so
  the archive does **not** store it; a spliced proof won't fail for import
  reasons. (Confirmed against current `_goal.v` / `_manual.v` output.)
- **Archive growth / staleness.** Keyed by `goal_hash`, so it is bounded by the
  number of distinct goals ever seen. Consider an LRU or a `--prune` later;
  ignore for v1.
- **Relationship to [agents_concurrency_proof_resuse.md](./agents_concurrency_proof_resuse.md).**
  That plan is reuse *within* one run (cluster + representative). This is reuse
  *across* runs (archive). They compose: the archive warm-starts a group, and
  intra-group clustering handles the rest.

---

# Addendum: implemented design + concurrent-mode unification

**STATUS: implemented.** PR1 (concurrent reuse) and PR2 (fold sequential into the
one-group machinery, delete the presolved note + AGENTS regen) are both done.
`apply_proof_reuse.py` runs before prepare in both modes; `prepare_agent.py` /
`run_agent.py` are thin wrappers over the concurrent group machinery
(`chunk_size = ∞`); the goal-`.vo` staleness fix lives in `recompile_stale_deps`.

This section supersedes the speculative step numbering above with what was
actually built.

## What is already implemented (sequential)

- `proof_archive.py` — the archive (one `<basename>.jsonl` file per goal file),
  content-keyed by `goal_hash`, with classify (`exact`/`similar`/`name_match`/
  `none`), splice/hint helpers, and batch `archive_solved_manual` /
  `classify_manual`. Tested.
- `apply_proof_reuse.py` — copies the archive into the work dir, classifies each
  goal, runs the **exact-reuse gate** (splice + recompile; pass ⇒ `solved_by_reuse`),
  injects `PRIOR PROOF` hints for `similar`/`name_match`, regenerates AGENTS.md
  for active goals (+ a presolved note). Archive path is an explicit `--archive`.
- `run_agent.py` skips `solved_by_reuse` goals.
- `validate_and_merge.py` writer archives every confirmed-solved proof.
- Goal-`.vo` staleness fix: `recompile_stale_deps` (ordered, cascading) rebuilds
  `_rel_lib.v` then `_goal.v` from source before any compile, so we never prove
  against a stale `.vo`.

## Target architecture (the unification)

Both modes use **one structure**: a base work dir holding *all* split files, and
one or more group dirs holding only the **active** goals the agent works on.
"Sequential" becomes "concurrent with a single group" (the code already claims
this). Reuse runs once on the base, before grouping.

```
base work dir:   ALL split files (solved ones spliced in place, active ones too)
group_NN/:       only ACTIVE goals copied in — the agent's sandbox
agent runs in:   a group dir, never the base
copy-back:       group_NN/<name>.v → base split file   (identical in both modes)
validate:        reads the base manifest (all goals): solved-spliced + copied-back
```

Consequences:
- Solved-by-reuse goals live only in the base and are **never grouped**, so the
  agent never sees them in **either** mode → the presolved AGENTS.md note and the
  `_regenerate_agents_md` step are **removed** (they were band-aids for the old
  "agent runs in the base dir" sequential layout).
- AGENTS.md is generated by `prepare_group` *after* reuse, for the group's active
  goals only → correct by construction, no regeneration.

## Unified step sequence

```
1. split_manual_goals                         → base work dir + manifest (all lemmas)
2. apply_proof_reuse  (OPTIONAL, on BASE)      → ensure base env, classify, exact-gate
       splice/hint base files, mark reuse_status, record proof_archive_dir + lib_files
3. prepare  (prepare_agent = 1 group  |  prepare_agent_concurrent = N groups)
       group ACTIVE goals only; per group copy active files + lib + tutorial + ARCHIVE;
       refresh stale _goal.vo once; emit AGENTS.md for the group's active goals
4. run     (agent per group, in its group dir; finalize copy-back → base)
5. validate_and_merge  (base manifest, fresh deps, merge, archive-on-solve writer)
6. verify
```

Reuse moves to run **before** prepare (so grouping can exclude solved goals).
Because prepare no longer precedes reuse, `apply_proof_reuse` provides its own
minimal compile env (it needs it for the gate anyway).

## File-by-file changes

### `apply_proof_reuse.py` — make it run on the base, self-providing its env
- `--lib …` fallback: resolve lib files from the manifest if present, else from
  this arg (the base pre-pass runs before prepare records them). Record the
  resolved `lib_files` into the manifest for prepare to reuse.
- Ensure compile env on the work dir it runs in: if `work_dir/_CoqProject` is
  missing, copy it from `coqproject_root` (resolved from the source manual or a
  `--coqproject` override); then `recompile_stale_deps([*lib, goal])`.
- Keep: classify, exact-gate (splice + recompile), hint injection, mark
  `reuse_status`, `reuse_report.json`, record `proof_archive_dir`, copy archive
  into its work dir (now a base/debug copy).
- **Remove** `_regenerate_agents_md` and the presolved-note path — AGENTS.md is
  now always produced by prepare *after* reuse.
- Same module serves both modes: sequential historically ran it on the single
  work dir; now it runs on the base in both modes, before grouping.

### `prepare_group_workdir.py` / `prepare_agent_concurrent.py`
- **Filter active goals:** group only `[e for e in lemmas if
  e.get("reuse_status") != "solved_by_reuse"]`. Zero active ⇒ write an empty
  groups manifest (skip the agent phase, go straight to validate).
- **Archive per group:** in `prepare_group`, after copying the (already
  hinted/spliced-free) active split files in, call
  `copy_proof_archive(group_dir, archive_dir, basename)` using
  `manifest["proof_archive_dir"]`. Each group's sandboxed agent reads prior
  proofs from its own `group_NN/proof_archive/` (must be per-group: sandbox
  isolation, same reason lib/tutorial are copied per group).
- **Staleness refresh once:** call `recompile_stale_deps([*lib, goal])` in
  `prepare_groups` before creating groups (move it out of `prepare_agent`).
- **Drop** the `{presolved_note}` template slot (revert that addition); AGENTS.md
  lists only the group's active goals.
- `lib_files`: use `manifest["lib_files"]` if reuse recorded them, else the CLI arg.

### `prepare_agent.py` — thin "one group" wrapper
- Delegate to the group machinery with a single group (chunk_size = ∞). Sequential
  thereby gains the base→group split and copy-back for free, and stops being a
  special case.

### `run_agent.py` — thin wrapper over `run_agents`
- Delegate to the concurrent runner with the single-group manifest so sequential
  gets the same copy-back-to-base finalize. Drop the bespoke "skip
  solved_by_reuse + run in base dir" logic (no longer needed — solved goals are
  never grouped, agent runs in the group dir).

### `run_agent_concurrent.py`
- `run_agents` already builds prompts from `gm["goals"]`, which now contain only
  active goals → no change. Add an early exit when there are zero groups.
- `finalize` copy-back already copies group files to base; solved base files are
  never grouped, so they're never clobbered → no change.

### `validate_and_merge.py`
- No change. Already runs on the base manifest (all goals), compiles against
  fresh deps, merges, and runs the archive-on-solve writer.

## Edge cases
- **All goals solved by reuse** ⇒ zero groups ⇒ skip agent phase ⇒ validate.
- **Exact-gate failure** in the base pre-pass ⇒ revert + demote to hint ⇒ the
  goal is *not* `solved_by_reuse` ⇒ it gets grouped normally (with the hint).
- **`--skip-prepare` reruns** (concurrent) ⇒ groups already exclude solved goals;
  base manifest carries `reuse_status`; consistent on rerun.
- **No reuse run at all** ⇒ no `reuse_status` keys ⇒ everything is "active" ⇒
  grouping includes all goals ⇒ behaves exactly like today.

## Testing
- Sequential parity: existing reuse + run_agent + validate tests adapted to the
  one-group structure (agent runs in group_00, copy-back to base).
- Concurrent integration (fake coqc + mocked gate): base pre-pass marks K solved
  ⇒ only the survivors are grouped; each group dir has
  `proof_archive/<basename>.jsonl`; solved base files carry spliced proofs;
  copy-back doesn't clobber them; all-solved ⇒ zero groups.
- Unit: active-goal filter in `group_goals` caller; `prepare_group` archive copy;
  `apply_proof_reuse` env self-setup (copies `_CoqProject`, refreshes deps).

## Net simplification
Folding sequential into the group machinery and moving reuse before grouping
lets us **delete** the presolved-note slot and `_regenerate_agents_md` — the
unification removes code rather than adding a parallel path.
