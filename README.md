# LLM4PV

Translating C programs with shape assertions to data predicates and abstract programs for formal verification in Rocq (Coq).

## Quick Start

Requires [uv](https://docs.astral.sh/uv/).

```bash
# Translate a single C file
uv run llm4pv shape_invdataset/sll/sll_copy.c output/shape/rel/sll/sll_copy_rel.c
uv run llm4pv --FILE=shape_invdataset/sll/sll_copy.c --OUTPUT_PATH=output/shape/rel/sll/sll_copy_rel.c

# Translate an entire directory
uv run llm4pv shape_invdataset/sll output/shape/rel/sll

# Generate abstract program Rocq libs
uv run llm4pv-rellib shape_invdataset/sll

# Generate synthesis contexts for abstract-program generation
uv run llm4pv-context shape_invdataset/sll/sll_copy.c ./output/gen/context/sll_copy.auto.json

# Run the abstract-program synthesis pipeline
uv run llm4pv-synth shape_invdataset/sll/sll_copy.c ./output/gen/synth/sll_copy

# Generate a Rocq guard from an invariant and loop condition
uv run llm4pv-guard "sll(p, l1) * sll(y, l2)" "p != null"

# Run tests
uv run --with pytest pytest
```

## What It Does

The pipeline takes C files annotated with shape predicates and produces C files with data predicates and abstract program specifications for refinement verification.

### Input (sll_copy.c)

```c
struct list * sll_copy(struct list * x)
/*@ Require listrep(x)
    Ensure  listrep(__return) * listrep(x)
 */
{
    ...
    /*@ Inv t != 0 && t -> next == 0 && lseg(x@pre,p) * listrep(p) * lseg(y, t) */
    while (p) { ... }
}
```

### Output (sll_copy_rel.c)

```c
#include "sll_def.h"
#include "safeexec_def.h"

/*@ Import Coq Require Import sll_copy_rel_lib */
/*@ Extern Coq (MretTy :: *) */
/*@ Extern Coq
               (maketuple: {A} {B} -> A -> B -> (A * B))
               (sll_copy_M: list Z -> program unit (list Z * list Z))
               (sll_copy_M_loop: list Z -> list Z -> list Z -> Z -> program unit MretTy)
               (sll_copy_M_loop_end: MretTy -> program unit (list Z * list Z))
                */

struct list * sll_copy(struct list * x)
/*@
    With X l1
    Require safeExec(ATrue, sll_copy_M(l1), X) && sll(x, l1)
    Ensure exists l2 l3, safeExec(ATrue, return(maketuple(l2, l3)), X) && sll(__return, l2) * sll(x, l3)
 */
{
    ...
    /*@ Inv exists v l1 l2 l3, safeExec(ATrue, bind(sll_copy_M_loop(l1,l2,l3,v), sll_copy_M_loop_end), X) && t != 0 && t -> next == 0 && t -> data == v && sllseg(x@pre, p, l1) * sll(p, l2) * sllseg(y, t, l3) */
    while (p) { ... }
}
```

Note: the data witness `v` (bound by `t -> data == v` in the original invariant) is automatically lifted into the abstract loop state.  When the original Ensure has no `__return` predicate on a non-void function (e.g. a scalar return), a synthetic witness `r` is added and threaded through `return(...)` so the abstract program's return type matches its body.

## Use From Other Projects

### CLI

```bash
uv run --from /path/to/LLM4PV llm4pv input.c output_rel.c
uv run --from /path/to/LLM4PV llm4pv-guard "sll(p, l1)" "p"
uv run --from /path/to/LLM4PV llm4pv-context input.c output.auto.json
uv run --from /path/to/LLM4PV llm4pv-synth input.c output_dir
uv run --from /path/to/LLM4PV llm4pv-rellib input.c output_lib_dir
```

### Library

```bash
uv add /path/to/LLM4PV
```

```python
from GenMonads import translate_c_file, translate_directory, gen_coq_guard

translate_c_file("input.c", "output_rel.c")
results = translate_directory("input_dir/", "output_dir/")
guard = gen_coq_guard("sll(p, l1) * sll(y, l2)", "p != null")
```

## Pipeline Stages

1. **TransShape** (`GenMonads/transshape/`) — Extract `/*@ ... */` annotations and translate shape predicates to data predicates (`listrep` -> `sll`, `lseg` -> `sllseg`), adding list variables (`?l1`, `?l2`, ...). Supports multiple functions per file and variable prefixing for multi-loop disambiguation. Pure data-field clauses like `t -> data == w` promote `w` (type `Z`) into the abstract loop state via the configurable `GenMonads/data/data_fields.json` (`data`, `key`, `val` by default).
2. **GuardGen** (`GenMonads/guardgen/`) — Generate Rocq guard functions from loop conditions: null checks, pointer equality, bare `p`/`!p` sugar, and field dereferences. `<root>-><field>` comparisons resolve through a per-predicate field-deref handler (e.g. `x->next != 0` with `sll(x, l)` ⇒ `tl l <> []`). Also resolves pointer aliases from pure equalities in invariants (e.g., `u->next == w`).
3. **AddAbstract** (`GenMonads/addabstract/`) — Wrap loop invariants with `safeExec(ATrue, bind(...), X)` and `exists`. Require existentials are lifted into the `With` clause; Ensure keeps the `exists` quantifier. When the function has a non-void return type and the Ensure has no `__return` predicate, a witness `r` is synthesized and the abstract program's return type widens accordingly. Functions whose abstract return type is `unit` emit `return(tt)` rather than a bare `return`.
4. **C File Translation** (`GenMonads/translate_c_file.py`) — Orchestrate stages 1-3, replace annotations in the original C file, translate header includes. Handles multi-function files and annotations placed before or after function headers. Auto-inserts `#include "safeexec_def.h"` and generates `Import Coq` / `Extern Coq` declaration blocks.

## Predicate Mappings

| Shape Predicate | Data Predicate |
|----------------|----------------|
| `listrep(x)` | `sll(x, ?l1)` |
| `lseg(x, y)` | `sllseg(x, y, ?l1)` |
| `dlistrep(x)` | `dll(x, ?l1)` |
| `dlseg(x, p, n, y)` | `dllseg(x, p, n, y, ?l1)` |

Mappings are configured in `GenMonads/data/predicate_mappings.json`.  Guard-side translations (root-null, segment-eq, field-deref) for the same predicates live in `GenMonads/data/guard_predicates.json`, and the list of struct fields treated as "data" (for invariant data-witness extraction) is in `GenMonads/data/data_fields.json`.

## Abstract Program Lib Generation

Generate `_rel_lib.v` files from one C file or a whole directory:

```bash
uv run llm4pv-rellib shape_invdataset/sll/sll_copy.c
uv run llm4pv-rellib shape_invdataset/sll
uv run llm4pv-rellib shape_invdataset/sll ./output/gen/libs
uv run llm4pv-rellib shape_invdataset/sll --output-dir ./output/gen/libs
uv run llm4pv-rellib --FILE=shape_invdataset/sll/sll_copy.c --OUTPUT_PATH=./output/gen/libs
```

The output directory is read from the `COQ_LIB_DIR` environment variable or `CONFIGURE` at repo root — there is no hardcoded fallback in the Python source.
These CLIs also accept alias-style path flags such as `--FILE`, `--C_DIR`, and `--OUTPUT_PATH` in addition to positional arguments.

Skeleton conventions:

- Loop-bearing functions get the full scaffold (`M_loop_before`, `M_loop_M1`, `M_loop_M2`, `M_loop_end`, plus concrete `M_loop_body` / `M_loop_aux` / `M_loop` / `M`).
- Loop-less functions with at least one early-return branch get a split scaffold: `M_before : args -> MONAD (early_result MretTy (ret))` plus `M_normal : MretTy -> MONAD (ret)`, joined by a concrete `M` that pattern-matches on the `Continue` / `ReturnNow` branches.
- Straight-line loop-less functions get a single opaque `Parameter {fn}_M`.
- Single-function libs share `Parameter MretTy : Type.`; multi-function libs declare `Parameter {func}_MretTy : Type.` per function to avoid result-type clashes.
- `maketuple` is defined when any function returns multiple logical results.
- Multi-function guard names are function-scoped (e.g. `sll_rotate_left_guardP`).

## Context Generation

Generate JSON contexts that capture the loop-invariant synthesis inputs for one file or a whole directory:

```bash
uv run llm4pv-context shape_invdataset/sll/sll_copy.c ./output/gen/context/sll_copy.auto.json
uv run llm4pv-context shape_invdataset/sll ./output/gen/context/sll
uv run llm4pv-context --FILE=shape_invdataset/sll/sll_copy.c --OUTPUT_PATH=./output/gen/context/sll_copy.auto.json
```

If the output path ends with `.json`, a single context file is written. Otherwise, the command writes one `*.auto.json` file per discovered synthesis context.

## Abstract Program Synthesis

Run the abstract-program synthesis pipeline on a C file, a context JSON file, or a whole directory:

```bash
uv run llm4pv-synth shape_invdataset/sll/sll_copy.c ./output/gen/synth/sll_copy
uv run llm4pv-synth few-shot-examples/absprog/sll_reverse.auto.json ./output/gen/synth/sll_reverse
uv run llm4pv-synth shape_invdataset/sll ./output/gen/synth/sll --jobs=2
uv run llm4pv-synth --FILE=shape_invdataset/sll/sll_copy.c --OUTPUT_PATH=./output/gen/synth/sll_copy
uv run llm4pv-synth shape_invdataset/sll/sll_copy.c ./output/gen/synth/sll_copy \
  --backend=command \
  --command 'codex exec - --output-last-message {response_file}'
```

Useful options:

- `--func-name` selects a target function in multi-function C files. If omitted on a multi-function file, every target function is synthesized into its own subdirectory under the output directory, and the accepted per-function libs are merged into a single `{basename}_rel_lib.v` in `COQ_LIB_DIR`.
- `--backend` chooses the generation backend: `gold-example`, `response-file`, or `command`.
- `--few-shot` adds repeatable few-shot example JSON files to the prompt.
- `--no-check` skips the Rocq syntax check step.
- `--max-retries` retries repair after the initial generation attempt.
- `--exclude` and `--jobs` control directory-mode batching.

## Residual Abstract Programs

Append residual abstract-program definitions for a callee call inside a generated Rocq library file:

```bash
uv run llm4pv-residual output/gen/libs/sll_multi_merge_rel_lib.v sll_merge_M sll_multi_merge_M
uv run llm4pv-residual --FILE=output/gen/libs/sll_multi_merge_rel_lib.v --CALLEE=sll_merge_M --CALLER=sll_multi_merge_M
```

Use `--NO-POLISH` to append raw residual definitions without the post-processing cleanup step.

## Shell Scripts

For generating Rocq verification conditions with the external `symexec` tool:

```bash
scripts/symexec.sh                              # use defaults from CONFIGURE
scripts/symexec.sh --FULL_AUTO=true             # add --full-auto when invoking symexec
scripts/symexec.sh --C_DIR=./output/gen/rel/sll --OUTPUT_PATH=./output/gen/vcs/ --LOGDIR=./output/gen/logs/
scripts/clean_symexec.sh --C_DIR=./shape_invdataset/sll --OUTPUT_PATH=./output/shape/vcs/ --LOGDIR=./output/shape/logs/
```

For cleaning generated `_rel.c` translation output files:

```bash
scripts/clean_rel.sh                                    # clean rel outputs matching configured C_DIR
scripts/clean_rel.sh --REL_DIR=./output/shape/rel/sll   # clean specific subdirectory
scripts/clean_rel.sh --FILE=./shape_invdataset/sll/sll_copy.c  # clean one generated rel file
scripts/clean_rel.sh --C_DIR=./shape_invdataset/sll     # clean rel outputs matching all .c files in a source dir
scripts/clean_rel.sh --ALL                              # clean all _rel.c files under REL_DIR
```

Configured via the `CONFIGURE` file at repo root.

## Limitations

- Requires specific annotation format `/*@ ... */`
- Guard generation limited to registered predicates
