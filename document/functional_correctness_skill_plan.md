# Functional Correctness Skill — Plan

A new skill `.codex/skills/functional-correctness/` that derives functional
correctness for an already-refined C program (`*_rel.c` + `*_rel_lib.v` +
`*_rel_goal.v` + `*_rel_manual.v`) by extending the C file with a
`high-level-spec`, augmenting the Rocq lib with the supporting definitions
and a Hoare triple about the abstract program, regenerating the VCs, and
discharging both old and new manual obligations.

## Design: one agent, scripted helpers

A **single sandboxed coding agent** (invoked the same way
`refinement-vc-solver` invokes `codex` via `run_agent.py`) does the whole
job end-to-end. It reads a checklist in `AGENTS.md`, edits the project
files, calls helper scripts when it needs deterministic operations, and
re-runs Rocq until everything checks.

Scripts are **tools**, not pipeline stages. The skill ships a small set of
scripts that the agent (and only the agent) calls — each one exists because
it does something the agent should not be left to do by hand: file-locating,
diffing Rocq lemma headers, splicing previously-proved tactic blocks back
into a regenerated `_manual.v`, or auditing whether the agent illegally
mutated existing definitions in the lib file.

There is no "stage 1 / stage 2 / …" pipeline driven from outside. The agent
itself decides when to run symexec, when to recompile, when to invoke the
diff helper, etc.

## What the agent does (its checklist in `AGENTS.md`)

Given a `<base>` (e.g. `glibc_slist_app`) plus a one-sentence NL spec:

1. Read `<base>_rel.c`, `<base>_rel_lib.v`, `<base>_rel_goal.v`,
   `<base>_rel_manual.v`, and the worked examples under
   `tutorial/fc_examples/`.
2. **Snapshot** — call `tools/snapshot.py <base>` once, which saves
   `.bak` copies of `_rel.c`, `_rel_lib.v`, `_rel_goal.v`, `_rel_manual.v`
   and records a hash of the existing top-level definitions in the lib
   (`Definition`, `Fixpoint`, `Inductive`, `Parameter`, `Lemma`, …) so the
   agent can later be audited for "append only".
3. Decide the high-level spec from the NL sentence + the function signature.
   Decide which Rocq symbols (e.g. `app`) it needs and whether they already
   exist in the lib's imports.
4. Edit `<base>_rel.c`:
   - Insert a `high-level-spec <= low_level_spec` block immediately before
     the existing low-level spec block of the function.
   - Add the new symbols to the existing `Extern Coq` cluster.
   - Do not touch the existing low-level spec or the function body.
5. Append (never modify!) to `<base>_rel_lib.v`:
   - Helper definitions for the new spec symbols.
   - A Hoare triple lemma about `<func>_M`, e.g.
     `Hoare ATrue (<func>_M l1 l2) (fun r _ => r = app l1 l2)`, with proof.
6. Recompile the lib (`coqc`). On error, fix the appendix and retry.
7. Re-run symbolic execution (`tools/symexec.py <base>`) to regenerate
   `_rel_goal.v` and a fresh `_rel_manual.v` skeleton (full of `Admitted.`).
8. **Diff** old vs new goals — call `scripts/diff_goals.py <base>`. It reads
   `_rel_goal.v.bak` and the new `_rel_goal.v`, classifies every lemma as
   *unchanged* / *changed-statement* / *new*, and writes `goal_diff.json`.
9. **Patch old proofs** — call `scripts/patch_old_proofs.py <base>`. It
   splices proofs of *unchanged* lemmas verbatim from `_rel_manual.v.bak`
   into the new `_rel_manual.v`. *Changed* and *new* lemmas are left as
   `Admitted.` and listed in `pending_goals.json`.
10. **Solve unsolved goals** — for every lemma in `pending_goals.json`,
    prove it. The new `<func>_derive_high_level_spec_by_low_level_spec`
    lemma uses the Hoare triple from step 5 plus the tactic schema in
    `tutorial/fc_examples/`. If a lemma is too involved, the agent may
    delegate that single lemma to the `refinement-vc-solver` skill.
11. Run `scripts/verify.py <base>` — the **final no-cheat gate**:
    - `coqc` succeeds on lib, goal, and manual.
    - No `Admitted.` survives in `_rel_manual.v`.
    - The lib audit (from step 2's snapshot) confirms that no pre-existing
      `Definition`/`Fixpoint`/etc. body in the lib was modified — only
      appended-to.
    - The original low-level spec block and function body bytes in
      `<base>_rel.c` are unchanged.

If the gate fails, the agent reads the report and iterates.

## Scripts (called by the agent)

| Script | What it does | Why a script (not freehand) |
|---|---|---|
| `snapshot.py <base>` | `cp` the four files to `.bak`; hash existing top-level lib definitions into `lib_audit.json` | Reproducible baseline for the final audit; agent can't be trusted to remember byte-exact originals. |
| `symexec.py <base>` | Wraps `scripts/symexec.sh` with the right paths | Keeps the agent from having to know the project's path conventions. |
| `diff_goals.py <base>` | Lex Rocq lemma headers from `_goal.v.bak` vs `_goal.v`; emit `goal_diff.json` (unchanged / changed-statement / new) | Mechanical Rocq-vernacular tokenization; error-prone by hand. |
| `patch_old_proofs.py <base>` | Using `goal_diff.json`, splice proofs of *unchanged* lemmas from `_manual.v.bak` into the new `_manual.v`; emit `pending_goals.json` | Pure text splice driven by the diff — must be deterministic so the verifier can audit it. |
| `verify.py <base>` | `coqc` lib/goal/manual; reject `Admitted.`; re-hash lib defs vs `lib_audit.json`; byte-diff protected regions of `_rel.c` | The audit is the whole point — the agent can't grade its own work. |

Five small scripts. Everything else is in the agent's prompt.

## Skill layout

```
.codex/skills/functional-correctness/
  SKILL.md                # how a caller invokes the skill
  AGENTS.md               # the checklist above, given to the sandboxed agent
  scripts/
    snapshot.py
    symexec.py
    diff_goals.py         # old vs new _goal.v → goal_diff.json
    patch_old_proofs.py   # splice unchanged proofs from _manual.v.bak into the new _manual.v
    verify.py
  tutorial/
    fc_examples/          # 2-3 worked end-to-end examples (sll_app, sll_rev)
```

The skill is invoked the standard way (caller mentions the skill in a
prompt; the SKILL.md frontmatter routes to it). No bespoke launcher script.

## Multi-function files

The skill argument accepts either a single `<func>` or `--all`. With
`--all`, the same single agent is invoked once with a JSON
`{func_name: nl_spec}` mapping; the agent iterates per-function inside its
own loop. The lib file is shared; the audit allows multiple appends per
agent run.

## Open questions

1. **Lib audit granularity** — should we hash full top-level blocks
   (`Definition foo := …`) or also forbid changes to `Require Import`
   ordering? Strict version is safer; loose version is more practical when
   the appendix needs an extra import.
2. **Symexec invocation** — confirm the exact CLI the project uses
   end-to-end (CLAUDE.md mentions `scripts/symexec.sh`; we'll need the flag
   set that regenerates `_goal.v` + `_manual.v` skeleton in place).
3. **Delegation policy** — does the single agent attempt every Hoare proof
   itself, or always hand the Hoare triple to `refinement-vc-solver`? A
   uniform "always delegate" rule is simpler to reason about.
4. **`.bak` retention** — drop after success, or keep for forensic diff?
