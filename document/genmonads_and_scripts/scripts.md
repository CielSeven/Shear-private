# `scripts/` File Guide

This guide documents the utility scripts under `scripts/`. Most of them are operational wrappers around the translation, symbolic execution, loop-invariant, or Rocq-checking workflow.

## Shared Conventions

Several shell scripts share the same conventions:

- They resolve the repository root from the script location.
- They read default paths from `CONFIGURE` at the repository root.
- They support `--KEY=value` or `-KEY=value` command-line overrides.
- They convert relative paths to absolute paths rooted at the repository.

## Files

| File | Type | Purpose | Important behavior |
| --- | --- | --- | --- |
| `check_rocq.sh` | Bash | Check generated `_rel_lib.v` files with `coqc` | Loads `COQ_LIB_DIR` from `CONFIGURE`, finds the nearest `_CoqProject`, expands its flags, then compiles either one file or every `*_rel_lib.v` in the library directory |
| `clean_rel.sh` | Bash | Remove generated translated C files | Loads defaults from `CONFIGURE`; supports configured source-directory cleanup, single-file cleanup via `FILE`, explicit source-directory cleanup via `C_DIR`, and full-tree cleanup via `ALL` |
| `clean_rocq.sh` | Bash | Remove Rocq build artifacts | Deletes `.vo`, `.vok`, `.vos`, and `.glob` files from `COQ_LIB_DIR` |
| `clean_symexec.sh` | Bash | Remove symbolic-execution outputs and logs | Deletes log and proof artifacts matching either a selected file or every `.c` file in `C_DIR` |
| `extract_and_normalize_assertions.py` | Python | Extract and normalize assertion blocks from log files | Finds `"Assertion normal"` blocks after while-loop unrolling, normalizes generated variable names, strips log noise, and writes `.normalized.txt` outputs |
| `loopinv_c.sh` | Bash | Batch-run a loop-invariant tool over C files | Calls the configured `LOOPINV` executable for each `.c` file and produces log, goal, auto-proof, and manual-proof files |
| `symexec.sh` | Bash | Batch-run a symbolic executor over C files | Calls the configured `SYMEXEC` executable for one file or a whole directory and writes log and generated proof artifacts |

## Suggested Usage Order

For the common translation and verification workflow, use the commands in this order:

1. `symexec.sh` or `loopinv_c.sh`
2. `extract_and_normalize_assertions.py` if you need cleaned assertion logs
3. translation via the Python package in `GenMonads/`
4. `_rel_lib.v` generation via `GenMonads/absprog/cli.py`
5. `check_rocq.sh`
6. cleanup with `clean_rel.sh`, `clean_rocq.sh`, or `clean_symexec.sh` as needed

## Workflow Details

### 1. `symexec.sh`

Primary role:
- Batch-run symbolic execution over C sources.

Inputs:
- `C_DIR`, `LOGDIR`, `SYMEXEC`, `SYMEXEC_INCLUDE_DIRS`, `OUTPUT_PATH`, and optional `FILE`

Behavior:
- Supports both single-file and directory-wide runs
- Passes one `-I...` flag per entry in `SYMEXEC_INCLUDE_DIRS`
- `SYMEXEC_INCLUDE_DIRS` is a colon-separated list of include directories
- Produces `${base}_goal.v`, `${base}_auto.v`, `${base}_manual.v`, and matching logs
- Uses the same argument shape as `loopinv_c.sh`, which keeps the workflows parallel

Example commands:

```bash
scripts/symexec.sh
scripts/symexec.sh --FILE=./shape_invdataset/sll/sll_copy.c
scripts/symexec.sh --FILE=./shape_invdataset/sll/sll_copy.c --SYMEXEC_INCLUDE_DIRS=./shape_invdataset/sll:/Users/cielseven/Projects/RHLProjects/EncRelTheory-Private/QCP/QCP_examples:/Users/cielseven/Projects/QCP/sac_c_parser/examples
scripts/symexec.sh --C_DIR=./output/gen/rel/sll --OUTPUT_PATH=./output/gen/vcs/ --LOGDIR=./output/gen/logs/
scripts/symexec.sh --C_DIR=./shape_invdataset/dll --OUTPUT_PATH=./output/shape/vcs/ --LOGDIR=./output/shape/logs/
```

Useful when:
- Generating symbolic-execution proof artifacts for one benchmark or a full folder

### 1. `loopinv_c.sh`

Primary role:
- Batch-run the configured loop-invariant executable over C sources.

Inputs:
- `C_DIR`, `LOGDIR`, `LOOPINV`, and optional `OUTPUT_PATH`

Behavior:
- Iterates over all `.c` files in `C_DIR`
- Invokes the configured executable with `--goal-file`, `--proof-auto-file`, and `--proof-manual-file`
- Captures tool output in one log file per source file
- Reports each file as success or failure using the logged exit code

Example commands:

```bash
scripts/loopinv_c.sh
scripts/loopinv_c.sh --C_DIR=./shape_invdataset/sll
scripts/loopinv_c.sh --C_DIR=./shape_invdataset/dll --OUTPUT_PATH=./output/gen/vcs
```

Useful when:
- Generating proof obligations and loop-invariant artifacts for an entire dataset directory

### 2. `extract_and_normalize_assertions.py`

Primary role:
- Turn raw tool logs into cleaner assertion snapshots.

Key functions:
- Detects `Unrolling while loop N times` sections
- Extracts `"Assertion normal"` blocks
- Renames generated variables and field/value-derived tokens into a normalized form
- Removes noise lines such as `branch name`

Output:
- One `.normalized.txt` file per processed input log

Example commands:

```bash
python3 scripts/extract_and_normalize_assertions.py ./output/shape/logs
python3 scripts/extract_and_normalize_assertions.py ./output/shape/logs/sll_copy_log.txt
python3 scripts/extract_and_normalize_assertions.py ./output/shape/logs --out-dir ./normalizedinv
python3 scripts/extract_and_normalize_assertions.py ./output/shape/logs --recursive
```

Useful when:
- You need stable textual assertions for comparison, inspection, or downstream documentation

### 3. Translation via `GenMonads/`

Primary role:
- Translate annotated C files into `_rel.c` outputs with rewritten specs, invariants, `safeExec(...)`, and generated Coq declarations.

Example commands:

```bash
uv run llm4pv shape_invdataset/sll/sll_copy.c output/shape/rel/sll/sll_copy_rel.c
uv run llm4pv shape_invdataset/sll output/shape/rel/sll
uv run llm4pv shape_invdataset/dll output/shape/rel/dll
```

Useful when:
- Turning source benchmarks into the translated C form expected by the later Rocq-side workflow

### 4. `_rel_lib.v` generation via `GenMonads/absprog/cli.py`

Primary role:
- Generate `_rel_lib.v` skeletons that match the translated C outputs.

Behavior:
- Reuses the translation pipeline to infer loop-state arity and generated guards
- Emits function-scoped guard names such as `sll_rotate_left_guardP` in multi-function files
- Defines `maketuple` in the generated lib when a translated function returns multiple logical results

Example commands:

```bash
uv run llm4pv-rellib shape_invdataset/sll/sll_copy.c
uv run llm4pv-rellib shape_invdataset/sll
uv run llm4pv-rellib shape_invdataset/dll --output-dir ./output/gen/libs
```

Useful when:
- Creating Rocq-side abstract program skeletons after C translation

### 5. `check_rocq.sh`

Primary role:
- Syntax-check generated Rocq libraries.

Inputs:
- `COQ_LIB_DIR` from `CONFIGURE` or CLI override
- Optional `FILE` argument to check one target

Behavior:
- Walks upward from `COQ_LIB_DIR` until it finds `_CoqProject`
- Reads `_CoqProject` line by line into `coqc` flags
- Runs `coqc` for each target file and prints a pass/fail summary

Example commands:

```bash
scripts/check_rocq.sh
scripts/check_rocq.sh --COQ_LIB_DIR=/path/to/lib
scripts/check_rocq.sh --FILE=/path/to/lib/sll_copy_rel_lib.v
```

Useful when:
- You have already generated `_rel_lib.v` files and want a fast validation pass before deeper proof work

### 6. `clean_rel.sh`

Primary role:
- Remove generated C translation outputs.

Inputs:
- Default `REL_DIR` from `CONFIGURE`
- Default `C_DIR` from `CONFIGURE`
- Optional `FILE` to remove one matching generated rel file
- Optional `C_DIR` to remove rel outputs matching all `*.c` files in a source directory
- Optional `ALL` to remove every `*_rel.c` under `REL_DIR`

Behavior:
- With no selector, removes `${base}_rel.c` for each `*.c` file in configured `C_DIR`
- With `FILE`, removes the matching `${base}_rel.c`
- With `C_DIR`, removes `${base}_rel.c` for each `*.c` file in the directory
- With `ALL`, recursively deletes every `*_rel.c` under `REL_DIR`
- If `REL_DIR` is the rel root, `FILE` and `C_DIR` infer the generated subdirectory from the source basename
- `FILE` and `C_DIR` are mutually exclusive
- `ALL` cannot be combined with `FILE` or `C_DIR`

Configured defaults:

```bash
C_DIR="${C_DIR:-./shape_invdataset/dll/}"
REL_DIR="${REL_DIR:-./output/shape/rel}"
```

Path resolution examples:

1. Default mode

Command:

```bash
scripts/clean_rel.sh
```

If `CONFIGURE` contains:

```bash
C_DIR="./shape_invdataset/dll/"
REL_DIR="./output/shape/rel"
```

Then the script removes:

- `output/shape/rel/dll/${base}_rel.c`

for each source file:

- `shape_invdataset/dll/${base}.c`

2. Single file mode with inferred output subdirectory

Command:

```bash
scripts/clean_rel.sh --FILE=./shape_invdataset/sll/sll_copy.c
```

Resolution:

- source file basename: `sll_copy.c`
- generated output basename: `sll_copy_rel.c`
- source parent directory basename: `sll`
- default rel root: `output/shape/rel`

Resulting target:

```text
output/shape/rel/sll/sll_copy_rel.c
```

3. Source directory mode with inferred output subdirectory

Command:

```bash
scripts/clean_rel.sh --C_DIR=./shape_invdataset/sll
```

Result:

- target directory: `output/shape/rel/sll`
- removed files: `${base}_rel.c` for every `${base}.c` in `shape_invdataset/sll`

4. Custom output directory

Command:

```bash
scripts/clean_rel.sh --REL_DIR=./output/gen/rel/sll --FILE=./shape_invdataset/sll/sll_copy.c
```

Resulting target:

```text
output/gen/rel/sll/sll_copy_rel.c
```

In this case the script does not append another inferred subdirectory because `REL_DIR` already points at the concrete rel output directory.

Useful when:
- You want to regenerate translated C outputs cleanly

### 6. `clean_rocq.sh`

Primary role:
- Remove Rocq compiler artifacts from the current library directory.

Inputs:
- `COQ_LIB_DIR` from `CONFIGURE` or CLI override

Behavior:
- Limits deletion to one directory level under `COQ_LIB_DIR`
- Removes `.vo`, `.vok`, `.vos`, and `.glob`

Example commands:

```bash
scripts/clean_rocq.sh
scripts/clean_rocq.sh --COQ_LIB_DIR=/path/to/lib
```

Useful when:
- Rocq outputs are stale and you want a clean recompilation

### 6. `clean_symexec.sh`

Primary role:
- Delete symbolic-execution logs and generated proof files.

Inputs:
- `C_DIR`, `LOGDIR`, `OUTPUT_PATH`, and optional `FILE`

Behavior:
- Matches each source `.c` file by basename
- Removes `${base}_log.txt`, `${base}_goal.v`, `${base}_auto.v`, `${base}_manual.v`, and `${base}_goal_check.v`
- Can clean a single file’s artifacts or a whole directory’s artifacts

Example commands:

```bash
scripts/clean_symexec.sh
scripts/clean_symexec.sh --C_DIR=./shape_invdataset/sll --OUTPUT_PATH=./output/shape/vcs/ --LOGDIR=./output/shape/logs/
scripts/clean_symexec.sh --FILE=./shape_invdataset/sll/sll_copy.c
scripts/clean_symexec.sh --C_DIR=./output/shape/rel/sll --OUTPUT_PATH=./output/shape/vcs/ --LOGDIR=./output/shape/logs/
```

Useful when:
- Re-running symbolic execution and wanting to avoid mixing old and new logs
