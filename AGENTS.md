# AGENTS.md

This file provides guidance to Codex (Codex.ai/code) when working with code in this repository.

## Project Overview

LLM4PV is a research project for translating C programs annotated with shape assertions into programs using data predicates and abstract programs for formal verification in Coq. The core pipeline lives in `GenMonads/`.

## Commands

All commands run from repo root:

```bash
# Translate a single C file
uv run llm4pv shape_invdataset/sll/sll_copy.c output/shape/rel/sll/sll_copy_rel.c
uv run llm4pv --FILE=shape_invdataset/sll/sll_copy.c --OUTPUT_PATH=output/shape/rel/sll/sll_copy_rel.c

# Translate an entire directory
uv run llm4pv shape_invdataset/sll output/shape/rel/sll

# Generate _rel_lib.v skeleton (abstract program scaffolding for Coq)
uv run llm4pv-rellib shape_invdataset/sll/sll_copy.c
uv run llm4pv-rellib shape_invdataset/sll/            # whole directory
uv run llm4pv-rellib shape_invdataset/sll/ /tmp/lib   # positional output dir
uv run llm4pv-rellib shape_invdataset/sll/ -o /tmp/lib # custom output dir
uv run llm4pv-rellib --FILE=shape_invdataset/sll/sll_copy.c --OUTPUT_PATH=/tmp/lib

# Run all tests
uv run --with pytest pytest

# Run a single test file or test
uv run --with pytest pytest GenMonads/tests/test_transshape_pipeline.py
uv run --with pytest pytest GenMonads/tests/test_addabstract.py::TestLoopInvariantSafeExec::test_basic_safeexec
```

### Library API

Other Python projects can use GenMonads as a library after `uv pip install /path/to/LLM4PV`:

```python
from GenMonads import translate_c_file, translate_directory

translate_c_file("input.c", "output_rel.c")
results = translate_directory("input_dir/", "output_dir/")
```

Shell scripts (in `scripts/`, configured via `CONFIGURE` file at repo root):
- `scripts/loopinv_c.sh` — batch process C files with external loopinv tool
- `scripts/symexec.sh` — batch symbolic execution
- `scripts/clean_rel.sh` — remove generated `_rel.c` output files (default: `output/shape/rel/`, override with `--REL_DIR=`)
- All scripts resolve paths relative to repo root, can be invoked from anywhere

## Architecture

The translation pipeline has four stages, each in its own module under `GenMonads/`:

### 1. TransShape (`transshape/`)
Extracts annotations (`/*@ ... */`) from C files and translates shape predicates to data predicates. Supports **multiple functions per file**. `preprocess.py` handles extraction (with `parse_spec_content` and `process_func_body` as reusable helpers); `parser.py` parses assertions into ASTs; `translator.py` performs the predicate renaming and adds list variables (`?l1`, `?l2`, etc.) with optional prefixing for multi-loop disambiguation; `process_and_translate.py` orchestrates.

### 2. GuardGen (`guardgen/`)
Generates Coq guard functions from loop conditions. Uses a registry pattern (`registry.py`) where predicates are registered in `predicates/` (e.g., `sll.py`, `tree.py`). Has its own condition lexer/parser in `cond/` and invariant parsing in `parsing/`.

### 3. AddAbstract (`addabstract/`)
Wraps translated loop invariants with `safeExec(ATrue, bind(func_M_loop(vars), func_M_loop_end), X)` predicates and `exists` quantifiers for abstract program refinement. Ensure clauses with multiple return variables use `maketuple` wrapping (e.g., `return(maketuple(l2, l3))`).

### 4. C File Translation (`translate_c_file.py`)
End-to-end orchestrator: runs stages 1-3, then replaces annotations in the original C file and translates header includes. Output files use `_rel.c` suffix. Supports both multi-function mode (using `replace_inner_assertions_for_func` per function body) and single-function fallback. Also handles annotations placed before or after the function header.

### 5. Abstract Program Skeleton (`absprog/`)
Generates `{basename}_rel_lib.v` files for Coq verification. Each file contains:
- **Concrete definitions**: `guardP` (from GuardGen), `M_loop_body` (repeat\_break scaffolding), `M_loop_aux`, `M_loop` (curried wrapper), `M` (full composition via bind)
- **Parameters** (to be synthesized by LLM): `M_loop_before` (initial state), `M_loop_M1` (break branch), `M_loop_M2` (continue branch), `M_loop_end` (post-loop)
- CLI: `llm4pv-rellib`; output directory configured via `COQ_LIB_DIR` in `CONFIGURE`

### Configuration
- `data/predicate_mappings.json` — maps shape predicates to data predicates (e.g., `listrep` → `sll`)
- `data/header_mappings.json` — maps shape header includes to data header includes
- `predicate_mapping.py` and `header_mapping.py` — loaders for the above
- `CONFIGURE` — shell-style config for tool paths and output directories (`COQ_LIB_DIR`, `OUTPUT_PATH`, etc.)

## Key Conventions

- **Annotation format**: `/*@ Require ... Ensure ... */` for specs, `/*@ Inv ... */` for loop invariants
- **Multi-function support** — C files may contain multiple functions; the pipeline processes each independently. Single-function files still work via backward-compatible fallback.
- **Variable naming**: translated predicates get `?l1`, `?l2`, `?l3` (numbered continuously across Require/Ensure); invariant variables use `l1`, `l2`, `l3` (without `?`). When multiple loops exist, variables are prefixed to avoid collision (e.g., `l1_1`, `l1_2`).
- **Abstract programs**: named `{func_name}_M`, `{func_name}_M_loop`, `{func_name}_M_loop_end`
- **Return types**: `M` and `M_loop_end` return type matches the number of Ensure-only variables: `(list Z)` for 1, `(list Z * list Z)` for 2, etc. Multiple return vars use `maketuple` in the `return` call (e.g., `return(maketuple(l2, l3))`).
- **No external Python dependencies** — uses only the standard library (pytest is an optional test dependency)
- **No linter/formatter configured**

## Data Flow

```
shape_invdataset/       →  GenMonads pipeline  →  output/shape/rel/
  sll/*.c, dll/*.c         (translate_c_file)       sll/*_rel.c, dll/*_rel.c

shape_invdataset/       →  llm4pv-rellib        →  COQ_LIB_DIR/
  sll/*.c, dll/*.c         (absprog)                *_rel_lib.v (Coq abstract program skeletons)

output/shape/rel/       →  symexec             →  output/shape/vcs/
  *_rel.c                  (external tool)          *.v (Rocq verification conditions)
```
