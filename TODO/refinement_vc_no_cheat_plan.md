# Refinement VC No-Cheat Plan

## Goal

Make the refinement-VC workflow safe against silent goal loss.

The key requirement is:

- splitting must not modify the original `*_manual.v`
- each split file corresponds to exactly one lemma from the original manual file
- merging must patch only that one lemma back into the original manual file
- after all tasks finish, we must verify from recorded metadata that the original manual file did not lose any goals

This plan does **not** use `*_goal_check.v`.

## Correct Workflow

### Step 1: Split a manual file into N Rocq files

Input:

- one original file such as [`output/gen/vcs/sll_copy_rel_manual.v`](/Users/cielseven/Projects/LLM4PV/output/gen/vcs/sll_copy_rel_manual.v)

Behavior:

1. Read the original `*_manual.v`.
2. Find every lemma in that file.
3. For each lemma, create one separate Rocq file.
4. Each split file should contain:
   - the shared prelude/imports from the original file
   - exactly one lemma from the original file
5. Do **not** modify the original `*_manual.v` during split.
6. Write a JSON manifest that records:
   - source manual file path
   - number of goals
   - ordered list of lemma names
   - mapping from each lemma name to its split Rocq file
   - enough source-position metadata to find and replace that lemma inside the original file later

### Step 1.5: Use a dedicated local work directory

The workflow should use one local directory to hold all generated and intermediate files.

Behavior:

1. Create a work directory for the task.
2. By default, place split files, manifest JSON, logs, and any intermediate merge/check artifacts there.
3. Allow the user to point out a custom work directory path.
4. If the user does not point out a path, use a default local work directory near the target manual file or under a tool-specific workspace directory.
5. After the whole workflow finishes, remove the work directory by default.
6. If the user enables debug mode, keep the work directory instead of removing it.

This gives us:

- a clean place for generated files
- predictable intermediate-file management
- optional postmortem debugging when needed

### Step 2: Work on split files one by one

For each split Rocq file:

1. Let the LLM attempt the proof in that one file only.
2. The result may end in either:
   - `Qed.`
   - or still `Admitted.`
3. Either way, that split file becomes the current result for that lemma.

### Step 3: Merge one lemma at a time back into the original manual file

Merge should **not** rebuild the whole manual file from scratch.

Instead, for one completed split file:

1. Run `scripts/check_rocq.sh --FILE=<split-file>` before merge.
2. Read the split file and extract its single lemma block.
3. Compare that lemma against the original `*_manual.v`.
4. Locate the matching lemma in the original manual file.
5. Replace only the old lemma block in the original manual file.

Examples:

- If the split file now contains:

```coq
Lemma xxxx : xxxxxxx.
...
Qed.
```

then replace the matching original block:

```coq
Lemma xxxx : xxxxxxx.
...
Admitted.
```

with the new `Qed.` version.

- If the split file still contains:

```coq
Lemma xxxx : xxxxxxx.
...
Admitted.
```

then still replace the matching original block with that latest version, but only for that lemma.

Important rule:

- merge updates one lemma block only
- merge must run `check_rocq` on the split file before patching it into the original manual file
- merge must not regenerate the whole file from a list of split blocks
- merge must preserve all untouched lemmas byte-for-byte

### Step 4: Final no-cheat verification

After all per-lemma tasks are finished:

1. Re-read the original `*_manual.v`.
2. Recompute the list of lemmas currently present in it.
3. Compare it against the JSON manifest recorded at split time.
4. Run `scripts/check_rocq.sh --FILE=.../xxx_manual.v` on the final manual file.
5. Fail if:
   - any original lemma name disappeared
   - any new unexpected lemma appeared
   - any lemma name was changed
   - the lemma count changed
   - duplicates appeared
   - the final `check_rocq` on `xxx_manual.v` fails
6. Only succeed if the final manual file still has exactly the same goal inventory as the original split-time manifest and passes `check_rocq`.

This is the minimum guarantee needed to prevent cheating by dropping goals.

## Why The Current Whole-File Merge Is Not Good Enough

The current merge model reconstructs the whole manual file from split outputs.

That is risky because:

- it treats the split set as the whole source of truth
- if a goal is missing from the split/manifest set, the rebuilt manual file can silently omit it
- it makes it easier for an LLM workflow to lose a goal without noticing

The safer model is:

- split records the original inventory
- merge patches one lemma at a time into the original file
- final verification confirms the original inventory is still present

## Required Script Responsibilities

### Split script responsibilities

- parse all lemmas in the original manual file
- create one Rocq file per lemma
- never edit the original manual file
- produce a JSON manifest describing the original goal inventory
- record stable identification data for each lemma so merge can find the correct original block

### Per-lemma merge responsibilities

- accept one split lemma file
- verify it still contains exactly one lemma
- identify which original lemma it corresponds to
- replace only that lemma block in the original manual file
- preserve all other text exactly

### Final verification responsibilities

- read the original manifest
- re-parse the final manual file
- run `scripts/check_rocq.sh --FILE=.../xxx_manual.v`
- verify:
  - same lemma count
  - same ordered lemma names, or at minimum same lemma-name set if order is intentionally allowed to vary
  - no duplicates
  - no missing lemmas
  - no unexpected lemmas
  - final Rocq check succeeds

## JSON Manifest Design

Recommended fields:

```json
{
  "source_file": ".../xxx_manual.v",
  "work_dir": ".../.manual_goals/xxx_manual",
  "goal_count": 3,
  "lemma_order": [
    "proof_of_a",
    "proof_of_b",
    "proof_of_c"
  ],
  "lemmas": [
    {
      "name": "proof_of_a",
      "split_rocq_file": ".../goal_01__proof_of_a.v",
      "statement_header": "Lemma proof_of_a : ...",
      "original_start_line": 26,
      "original_end_line": 40
    }
  ],
  "cleanup_policy": "delete_on_success",
  "debug_keep_workdir": false
}
```

The exact schema can change, but the manifest must be sufficient to:

- know how many goals existed originally
- know what those goals were
- map each split file back to the original manual file
- know exactly which generated Rocq file corresponds to which goal
- verify at the end that no goal disappeared

## TODO

- [ ] Redefine split as a non-destructive operation on `*_manual.v`.
- [ ] Make split create exactly one Rocq file per lemma in the original manual file.
- [ ] Make split write a JSON manifest whose main purpose is inventory tracking, not just file listing.
- [ ] Make the JSON manifest explicitly map each goal name to its split Rocq file path.
- [ ] Add work-directory management for generated and intermediate files.
- [ ] Allow the user to specify the work-directory path.
- [ ] Define the default work-directory location when the user does not specify one.
- [ ] Add a debug/keep-workdir mode.
- [ ] Make successful runs delete the work directory by default.
- [ ] Decide the stable lemma identity format:
  - lemma name only
  - lemma name plus statement header
  - lemma name plus source position
- [ ] Decide whether final verification should require identical order or only identical set.
- [ ] Make merge operate on a single split file at a time.
- [ ] Make merge run `scripts/check_rocq.sh --FILE=<split-file>` before patching.
- [ ] Make merge patch only the corresponding lemma block in the original manual file.
- [ ] Make merge preserve all untouched text exactly.
- [ ] Make merge accept both successful `Qed.` and unsuccessful `Admitted.` outputs as patchable results.
- [ ] Make merge fail if the split file contains zero lemmas or more than one lemma.
- [ ] Make merge fail if it cannot match the split lemma back to exactly one original lemma.
- [ ] Make final verification compare the final manual file against the split-time manifest.
- [ ] Make final verification run `scripts/check_rocq.sh --FILE=<manual.v>` on the final manual file.
- [ ] Make final verification fail on:
  - missing goals
  - renamed goals
  - extra goals
  - duplicate goals
  - changed goal count
  - Rocq check failure on the final manual file
- [ ] Add tests for:
  - normal split
  - one-lemma patch with `Qed.`
  - one-lemma patch still ending in `Admitted.`
  - missing split file
  - duplicate lemma names
  - dropped lemma in final manual file
  - extra lemma inserted into final manual file
  - merge mismatch against wrong lemma
- [ ] Update the skill instructions so the LLM workflow becomes:
  - split once
  - record all generated files under one work directory
  - prove one split file
  - run `check_rocq` on that split file
  - patch one lemma back
  - repeat
  - run final manifest-based no-cheat verification
  - run final `check_rocq` on the manual file
  - remove the work directory unless debug mode says to keep it

## Recommendation

The no-cheat guarantee should come from file-inventory checks and one-lemma patching, not from trusting the LLM and not from rebuilding the whole manual file.

The final gate should be:

- manifest-based inventory verification
- then `check_rocq` on the resulting `*_manual.v`
