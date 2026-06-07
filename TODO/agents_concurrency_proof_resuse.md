# Agent Concurrency With Proof Reuse

## Problem

The current concurrent VC runner uses a two-wave seed strategy:

1. Split goals into fixed-size groups.
2. Solve the first goal in each group as a seed.
3. Re-run the group agent on the remaining goals with the seed proof pasted into `AGENTS.md`.

This helps only when the first goal is structurally close to the remaining goals. In practice, a group may contain multiple proof families. For example, one solved goal may help the next read-rank goal, while a later write-parent/update goal needs a different proof pattern. The useful reuse often happens inside the agent after it solves a non-seed goal, not from the original seed.

## Goal

Keep parallelism across groups while allowing each group agent to perform adaptive proof reuse inside its own working directory.

The desired behavior is:

- Run one agent per goal group.
- Let each agent inspect all assigned goals first.
- Ask the agent to cluster similar goals before solving.
- Solve one representative per cluster.
- Reuse each solved representative for similar goals in the same cluster.
- Compile after each goal and update `proof_report.json`.

## Proposed Design

**Replace** the current wave-1/wave-2 seed workflow with a single adaptive group workflow. This is a full replacement, not a new mode flag — the old seed code is dropped.

For each group:

1. Prepare a group work directory containing all assigned goals.
2. Generate `AGENTS.md` with all assigned goals, not just a seed.
3. Spawn one Codex agent for that group.
4. The agent works sequentially inside the group, but groups still run in parallel.

This preserves concurrency at the group level while giving each agent enough context to reuse proofs within the group.

### Per-group resources

- **Lib file**: each group still gets a read-only copy of `_lib.v`, same as the current concurrent mode. If a goal needs lib changes, the agent reports it and leaves `Admitted.`
- **Tutorial**: read-only copy of the tutorial directory.
- **`max_retries`**: hard cap per goal, so the total budget per group is `N × max_retries` where `N` is the number of assigned goals. The agent self-enforces.
- **`--timeout`**: per-group (per agent invocation). To make sizing intuitive, also accept `--timeout-per-goal`; when set, the actual agent timeout becomes `timeout-per-goal × len(group)`.

## Agent Instructions

`AGENTS.md` for the group should include:

```text
Before editing proofs, inspect all assigned goal files and classify them into similar proof families based on statement similarity (predicates, control flow, witness shapes).

For each proof family:
1. Pick the simplest representative goal.
2. Solve and compile that representative first.
3. Use the solved proof as a local reference for the remaining goals in that family.
4. Adapt the proof carefully; do not blindly copy variable names.

If the chosen representative fails to solve, pivot to a different cluster member as the new candidate. Do not waste retries on a single blocked goal.

If a goal introduces a new proof pattern, solve it as a new representative and reuse it for later similar goals.

If a follow-up goal in a cluster fails despite the reference proof, leave it with `Admitted.` and write a clear failure entry in proof_report.json. Do not loop on it.

After each goal:
- run coqc on that split goal;
- fix compile errors before moving on;
- update proof_report.json only after the goal compiles.

Also write proof_strategy_report.json describing your clusters and reuse decisions (see "Reports" below).
```

## Reports

Each group agent writes two JSON files in its work dir:

- `proof_report.json` — same format as today: one entry per goal with `{goal, status, report?}`.
- `proof_strategy_report.json` — short summary of the agent's clustering and reuse decisions:
  ```json
  {
    "clusters": [
      {"name": "A", "representative": "goal_0__proof_of_foo_entail_wit_1",
       "members": ["goal_0__proof_of_foo_entail_wit_1", "goal_1__proof_of_foo_entail_wit_2", "goal_2__proof_of_foo_entail_wit_3"]}
    ],
    "notes": "goal 1 reused goal 0's proof; goal_3 needed new representative"
  }
  ```
  Optional but recommended — useful for debugging poor solve rates and tuning `chunk_size`.

## Example

Given one group:

```text
goal_0 goal_1 goal_2 goal_3 goal_4
```

If `goal_1` and `goal_2` are similar:

```text
cluster A: goal_1, goal_2
cluster B: goal_0
cluster C: goal_3
cluster D: goal_4
```

The agent should solve:

```text
goal_0
goal_1   # representative for cluster A
goal_2   # reuse/adapt goal_1
goal_3
goal_4
```

The runner does not need to paste `goal_1` into a new prompt for `goal_2`, because both files are in the same agent context.

## Runner Changes

Modify `run_agent_concurrent.py` in place — no new mode flag. The wave-1/wave-2 logic is removed entirely.

Implementation outline:

1. Keep `group_goals(...)` for coarse group partitioning. Grouping remains name-based at the runner level (sort + chunk). Statement-similarity grouping happens *inside* each agent.
2. Remove wave-1/wave-2 orchestration; remove seed-proof injection.
3. Replace `prepare_wave1`/`prepare_wave2` with a single `prepare_group(...)`:
   - create the group workdir;
   - copy only the assigned goal files;
   - copy the tutorial directory and the read-only lib copy;
   - generate `AGENTS.md` listing all assigned goals (no seed proof);
   - write a group manifest listing assigned goals.
4. Spawn one agent per group with the full goal list, in parallel (bounded by `--max-parallel`).
5. After agents finish:
   - copy back only the assigned goal files (already covered by `_copy_back_goals`);
   - merge per-group `proof_report.json` files into `<work-dir>/proof_report.json`;
   - merge per-group `proof_strategy_report.json` files into `<work-dir>/proof_strategy_report.json`;
   - `validate_and_merge.py` runs separately as before.

The runner does not need a step to remove stale `goal_*.v` files — only assigned files are copied, and only assigned files are copied back.

## Compile-after-each-goal

Instruction-only. The runner does not enforce per-goal compilation — that would require post-processing each agent invocation (parse proof_report.json, run coqc, retry on failure), which significantly complicates the runner. Trust the agent to compile, and verify authoritatively in `validate_and_merge.py`.

## Acceptance Criteria

- Each group agent sees all assigned goals at once.
- `AGENTS.md` explicitly asks the agent to cluster goals and reuse solved representatives, with explicit fallback rules for representative failure and follow-up failure.
- The runner still runs groups in parallel.
- Each group's `proof_report.json` contains entries for exactly the assigned goals.
- Per-group `proof_report.json` files are merged into a single `<work-dir>/proof_report.json` for `validate_and_merge.py` to consume.
- `validate_and_merge.py` continues to be the authoritative validation step (unchanged).
- Logs make it clear which goals were assigned to each group.
- `proof_strategy_report.json` is produced per group and merged at the work dir root.

