# Refinement VC Solver — Concurrency Plan
Add concurrent goal solving to the refinement-vc-solver skill. Currently one Codex agent solves all goals sequentially. This plan introduces wave-based concurrency: solve seed goals first, then fan out remaining goals in parallel with seed proofs as reference.

## Architecture

```
Wave 1 (seeds)          Wave 2 (parallel fan-out)
                        
 group A seed ──────┬──► group A goal 2  (with seed proof)
                    ├──► group A goal 3  (with seed proof)
                    └──► group A goal 4  (with seed proof)
                        
 group B seed ──────┬──► group B goal 2  (with seed proof)
                    └──► group B goal 3  (with seed proof)
```

## Steps

### Phase 1: Goal grouping module

- [x] **1.1** Create `scripts/group_goals.py` — a standalone module with a pluggable grouping interface
  - Function signature: `group_goals(lemmas: list[dict]) -> list[list[dict]]`
  - Returns list of groups, each group is a list of lemma entries from manifest
  - First element of each group is the seed (to be solved first)

- [x] **1.2** Implement sort+chunk strategy as the default
  - Sort lemma names lexicographically
  - Split into chunks of size K (configurable, default 5)
  - First element of each chunk is the seed
  - Simple, no dependencies, good enough for structured naming like `entail_wit_1..N`, `return_wit_1..N`

- [x] **1.3** Add tests for `group_goals.py`
  - Test with real lemma names from sll_merge (16 goals), sll_multi_merge (19 goals)
  - Verify entail_wit goals land in same/adjacent groups
  - Verify return_wit goals land together
  - Edge case: single goal, two goals, goals with no number suffix

### Phase 2: Per-goal work directories

**One work dir per group, not per goal.** Each group gets a single work dir containing all its goal files. Agents within the same group share the work dir.

**Preparation and execution are interleaved per wave**, driven by `run_agent_concurrent.py` (Phase 3). The flow for each group:

1. `prepare_group_workdir.py` creates the work dir with symlinked group goals + wave 1 AGENTS.md (targets seed only)
2. Codex agent runs, solves seed
3. `prepare_group_workdir.py --wave2 --seed-proof <text>` regenerates AGENTS.md in the same work dir (targets remaining goals, seed proof inlined)
4. Codex agent runs, solves remaining goals

Steps 1-2 run in parallel across groups (wave 1). Steps 3-4 run in parallel across groups (wave 2). The concurrent runner orchestrates this.

**Seed proof isolation**: the solved seed proof text is read and embedded inline into the wave 2 AGENTS.md. No separate seed file for the agent to modify.

- [x] **2.1** Refactor shared setup logic into `manual_goal_utils.py`
  - Extract common helpers from `prepare_agent.py` (symlink lib, copy tutorial, resolve coqc flags, generate config.toml) into `manual_goal_utils.py`
  - Keep all shared functions in `manual_goal_utils.py` — no new utility files
  - Update `prepare_agent.py` to call the extracted helpers

- [x] **2.2** Create `scripts/prepare_group_workdir.py` — sets up a work dir for a goal group
  - Takes: list of goal file paths for the group, lib file path, manifest path
  - `--wave2 --seed-proof <text>`: regenerate AGENTS.md for wave 2 (in existing work dir)
  - Creates: work dir with symlinked goal files (edits go to originals), lib/ read-only copy, tutorial/ copy, .codex/config.toml, AGENTS.md
  - Calls the shared helpers from `manual_goal_utils.py` (extracted in 2.1)

- [x] **2.3** Add tests for Phase 2
  - Test new `manual_goal_utils` helpers: `setup_lib_readonly_copy`, `make_readonly`, `copy_coqproject`, `generate_rocq_mcp_config`
  - Test `prepare_wave1()`: creates work dir, copies goals, lib is read-only copy (not symlink), generates wave 1 AGENTS.md targeting seed only
  - Test `prepare_wave2()`: regenerates AGENTS.md with seed proof inlined, or no-seed fallback
  - Test CLI `--wave2 --seed-proof` flag

### Phase 3: Concurrent runner

- [x] **3.1** Create `scripts/run_agent_concurrent.py` — the wave-based concurrent runner
  - Input: manifest.json (after split), lib file path
  - Args: `--max-parallel N` (default: 4), `--chunk-size K` (default: 5), `--timeout`, `--max-retries`
  - Flow:
    1. Load manifest, group goals via `group_goals()`
    2. **Wave 1**: for each group, prepare + run agent for seed goal (parallel across groups, bounded by max-parallel)
    3. Collect seed proofs (read solved goal files)
    4. **Wave 2**: for each group, prepare + run agents for remaining goals (parallel, bounded by max-parallel), seed proof injected into prompt
    5. Agent writes `proof_report.json` in the work dir for every goal:
       - Solved: `{"goal": "...", "status": "solved"}`
       - Unsolved: `{"goal": "...", "status": "admitted", "report": "..."}`
    6. Runner collects `proof_report.json` from each group and prints a quick summary (agent-reported, not yet validated)
    7. Phase 4 (`validate_and_merge.py`) does authoritative validation (compiles, checks Admitted, merges)

- [x] **3.2** Implement wave 1: seed solving
  - For each group, call `prepare_goal_workdir.py` (no seed proof)
  - Spawn Codex agent per seed (using subprocess, same sandbox flags as current `run_agent.py`)
  - Use `concurrent.futures.ProcessPoolExecutor` or `asyncio.subprocess` for parallelism
  - Wait for all wave 1 agents to complete

- [x] **3.3** Implement wave 2: parallel fan-out with seed proofs
  - For each group, read the seed goal file to extract the solved proof
  - Call `prepare_goal_workdir.py` with `--seed-proof <path>` for each remaining goal
  - Spawn Codex agents in parallel (bounded by max-parallel)
  - Wait for all wave 2 agents to complete

- [x] **3.4** Handle seed failure gracefully
  - If a seed goal fails (agent times out or can't solve), still fan out remaining goals in that group without a seed proof (fall back to no-reference mode)
  - Log a warning so the user knows

### Phase 4: Validate & merge

Keep the existing `_has_admitted`, `_goal_is_solved`, `_merge_goal` functions unchanged. Add new wrapper/helper functions on top for `proof_report.json` refinement.

`validate_and_merge.py` depends on the **original** `manifest.json` (from `split_manual_goals.py`) which points to goal files at their original split locations. Goal files in group dirs are symlinked to the originals, so edits go directly to the original split files — no copy-back step needed.

`validate_and_merge.py` reads the agent's `proof_report.json`, validates each entry against actual compilation, corrects discrepancies (e.g., agent claimed "solved" but file doesn't compile → "broken"), and writes a final authoritative `proof_report.json` as its summary output.

- [x] **4.1** ~~Add a copy-back step~~ → Goal files are symlinked, no copy-back needed
  - `prepare_wave1` symlinks goal files from group dir to original split locations
  - Agent edits go directly to the originals via symlink
  - `_copy_back_goals` removed from `run_agent_concurrent.py`

- [x] **4.2** Update `validate_and_merge.py` to read and refine `proof_report.json`
  - Read agent's `proof_report.json` from the work dir
  - For each goal, validate against actual file state:
    - Agent says "solved" + file has `Qed.` + compiles → confirmed `solved`, merge back
    - Agent says "solved" but file doesn't compile → override to `broken`
    - Agent says "admitted" + file has `Admitted.` → confirmed `admitted`, keep agent's report
    - Goal missing from report → add as `broken`
  - Write the validated `proof_report.json` back (overwriting the agent's version)
  - This is the authoritative final summary

- [x] **4.3** Verify `validate_and_merge.py` works unchanged after copy-back
  - It reads `manifest.json`, checks each `split_rocq_file` for `Admitted.`, compiles, merges — all at original paths
  - `verify_manual_goals.py` also works as-is since it checks the original manual file

### Phase 5: Update SKILL.md and integrate

- [ ] **5.1** Update `SKILL.md` to document the concurrent workflow
  - Add Step 3 alternative: `run_agent_concurrent.py`
  - Document `--max-parallel` and `--chunk-size` flags
  - Keep the sequential `run_agent.py` as a fallback option

- [ ] **5.2** End-to-end test
  - Run on `sll_merge_rel_manual.v` (16 goals) and compare solve rate / wall time vs sequential

### Future: Better grouping strategies

- [ ] **F.1** Add Levenshtein edit distance clustering to `group_goals.py`
  - Hierarchical agglomerative clustering with distance threshold
  - Better grouping when category sizes are uneven (e.g., 10 entail_wit + 6 return_wit)
  - Still stdlib-only (Levenshtein is easy to implement)

- [ ] **F.2** Add content-based grouping
  - Parse the actual lemma statement to group by structure, not just name
  - More robust but more complex — defer until name-based grouping proves insufficient
