# Refinement Skill: Isolated Agent Execution Plan

## Problem

When the LLM proves refinement VCs directly in the project directory, it inherits the full project context (CLAUDE.md, settings, file access). This causes:
- Distraction from unrelated project files
- Risk of unintended reads/edits outside the proof scope
- Polluted context that wastes tokens and degrades proof quality

## Goal

When the skill runs, it should spawn a **sandboxed code agent** (e.g. Codex) in an isolated working directory with:
- **Read access**: only the split goal file, the tutorial, and the corresponding `_lib.v`
- **Write access**: only the split goal file and the `_lib.v`
- **No access** to the rest of the project

## Design

### 1. Working directory layout

The split script already creates:

```
output/gen/vcs/.manual_goals/sll_append_rel_manual/
  manifest.json
  goal_01__lemma_name.v
  goal_02__lemma_name.v
  ...
```

Extend this to also symlink reference files — no copies:

```
output/gen/vcs/.manual_goals/sll_append_rel_manual/
  manifest.json                           # read-only (inventory)
  AGENTS.md                               # generated instructions for the agent
  .codex/
    config.toml                           # rocq-mcp server config
  goal_01__lemma_name.v                   # editable (proof target)
  goal_02__lemma_name.v                   # editable (proof target)
  ...
  lib/
    sll_append_rel_lib.v  -> ../../sll_append_rel_lib.v   # symlink, edits go to original
  tutorial/
    refinement_proof_tutorial.md  -> <skill-dir>/...      # symlink to read-only source
```

- `.codex/config.toml` configures `rocq-mcp` so the agent can develop proofs interactively — stepping through tactics, inspecting proof state, and iterating without recompiling the whole file.
- `lib/` contains symlinks to the real `_lib.v` files. Edits through the symlink modify the original directly — no merge-back needed.
- `tutorial/` contains a symlink to the tutorial in the skill directory. The original file should be read-only (`chmod a-w`) so the agent cannot modify it through the symlink.

### 2. `AGENTS.md` generation

`prepare_agent.py` generates an `AGENTS.md` in the work directory that tells the agent:

```markdown
# Refinement VC Solver

You are solving Rocq refinement proof obligations.

## Instructions
- Read `tutorial/refinement_proof_tutorial.md` for proof strategy guidance.
- Work on one goal file at a time (e.g. `goal_01__lemma_name.v`).
- Only edit the proof body of the lemma. Do not change the lemma statement.
- If the proof requires changes to definitions, edit `lib/<name>_rel_lib.v`.
- Use `rocq-mcp` to develop proofs interactively — step through tactics, inspect proof state, and iterate without recompiling the whole file.
- Alternatively, compile manually with: `coqc <flags> <file>`
- Do not read or modify any files outside this directory.
- Do NOT modify anything in `tutorial/`.

## Files
- `goal_*.v` — one lemma per file (editable)
- `lib/*_rel_lib.v` — abstract program skeleton (editable if needed)
- `tutorial/refinement_proof_tutorial.md` — proof tutorial (READ-ONLY)
- `manifest.json` — goal inventory (read-only)
```

### 3. Agent invocation

Add a new script `scripts/validate_and_merge.py` that:

1. Reads `manifest.json` to discover the work directory and goal files
2. Filters out already-solved goals (verified by compilation)
3. Spawns **one** Codex agent with all unsolved goal files in a single prompt:

```bash
codex \
  -C <work-dir> \
  -c sandbox_mode="workspace-write" \
  --full-auto \
  "Solve all the following Rocq refinement proof goals: ..."
```

Key config overrides:
- `-C <work-dir>`: sets the agent's cwd to the isolated work directory
- `sandbox_mode="workspace-write"`: agent can only write within the workspace (the work dir)
- `--full-auto`: no interactive approval prompts
- `--timeout 1200`: 20-minute timeout for the entire agent session (configurable)

The `tutorial/` directory is `chmod a-w` so the sandbox cannot modify it even with workspace-write access. Goal files and `lib/` remain writable.

4. After the agent exits, validates each goal by compilation (recompiling `_lib.v` first if the agent edited it)
5. Merges each solved goal back via `merge_manual_goals.py --in-place`
6. Prints a summary of solved/unsolved goals

### 4. Changes to existing scripts

| Script | Change |
|---|---|
| `split_manual_goals.py` | No changes — keeps doing split only |
| `prepare_agent.py` (new) | Takes `manifest.json` + `_lib.v` path + `--max-retries N`, creates `lib/` and `tutorial/` symlinks, generates `AGENTS.md` and `.codex/config.toml` (rocq-mcp) in the work dir |
| `manifest.json` | Add `"lib_file"` and `"coqc_flags"` fields so the agent script knows how to compile |
| `SKILL.md` | Update workflow to describe the agent-based approach |

### 5. `_CoqProject` and compilation in the sandbox

`prepare_agent.py` resolves `coqc` flags from the nearest `_CoqProject` and stores them in `manifest.json`. The generated `AGENTS.md` includes the exact compile command as a fallback. The primary compilation method is `rocq-mcp` (configured via `.codex/config.toml`), which also supports interactive proof development — the agent can step through tactics and inspect proof state without recompiling the whole file.

### 6. Workflow summary

```
1. User: "prove output/gen/vcs/sll_append_rel_manual.v"

2. split_manual_goals.py <manual.v>
   → creates work dir with goal files + manifest.json

3. prepare_agent.py <manifest.json> <lib.v> [--max-retries N]
   → symlinks lib/, tutorial/, generates AGENTS.md + .codex/config.toml (rocq-mcp), stores coqc flags + max_retries in manifest

4. run_agent.py <manifest.json> [--timeout 1200]
   - Spawns sandboxed Codex agent (sandbox_mode="workspace-write")
   - Agent can ONLY read/write within the work directory
   - Agent reads AGENTS.md, uses rocq-mcp for interactive proofs
   - LLM native subagents MUST NOT be used (they share full workspace)

5. validate_and_merge.py <manifest.json>
   - Rejects goals still containing Admitted.
   - Recompiles lib if agent edited it (stale .vo detection)
   - Compiles each goal, merges solved ones back into the manual file
   - Prints summary

6. verify_manual_goals.py — final gate
```

## Open Questions

1. **Claude Code support**: Can Claude Code be invoked similarly with restricted file access? If so, we could support both agents.
2. **Parallel goals**: Can we run multiple goal agents in parallel? The goal files are independent, but `_lib.v` edits (via symlink to same original) could conflict.
3. **Cost control**: Each agent invocation costs tokens. Should we add a `--max-cost` or `--max-tokens` flag?
