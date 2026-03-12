# GenMonads

Internal documentation for the translation pipeline modules. For usage instructions, see the [top-level README](../README.md).

## Translation Pipeline Details

### 1. Annotation Extraction (`transshape/preprocess.py`)

Extracts from C files:
- Function specifications (`Require`/`Ensure`/`With`)
- Loop invariants (`Inv`)
- Command guards (while conditions)

### 2. Shape Translation (`transshape/translator.py`)

- Renames predicates via `data/predicate_mappings.json`
- Adds list variables with continuous numbering across `Require`/`Ensure`
- Wraps `Inv` assertions with `exists` quantifiers

### 3. Guard Generation (`guardgen/`)

Uses a registry pattern — predicates are registered in `guardgen/predicates/` (e.g., `sll.py`, `tree.py`). Has its own condition lexer/parser in `guardgen/cond/` and invariant parsing in `guardgen/parsing/`.

Adding a new predicate = register a new `PredicateSpec` in `guardgen/predicates/`; no other code changes needed.

### 4. Abstract Predicate Addition (`addabstract/addexec.py`)

Adds `safeExec(PRE, bind(PROGRAM_LOOP(vars), PROGRAM_LOOP_END), POST)` where:
- `PRE` defaults to `ATrue`, `POST` defaults to `X`
- `PROGRAM_LOOP` = `{func_name}_M_loop`, `PROGRAM_LOOP_END` = `{func_name}_M_loop_end`
- Generated variables become program arguments

### 5. C File Replacement (`translate_c_file.py`)

Replaces `/*@ ... */` annotations in-place and translates header includes via `data/header_mappings.json`. All other code is preserved unchanged.
