# LLM4PV

Translating C programs with shape assertions to data predicates and abstract programs for formal verification in Rocq (Coq).

## Quick Start

Requires [uv](https://docs.astral.sh/uv/).

```bash
# Translate a single C file
uv run llm4pv shape_invdataset/sll/sll_copy.c output/shape/rel/sll/sll_copy_rel.c

# Translate an entire directory
uv run llm4pv shape_invdataset/sll output/shape/rel/sll

# Generate abstract program Rocq libs
uv run llm4pv-rellib shape_invdataset/sll

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
               (sll_copy_M: list Z -> program unit (list Z))
               (sll_copy_M_loop: list Z -> list Z -> list Z -> program unit MretTy)
               (sll_copy_M_loop_end: MretTy -> program unit (list Z))
                */

struct list * sll_copy(struct list * x)
/*@
    With X l1
    Require safeExec(ATrue, sll_copy_M(l1), X) && sll(x, l1)
    Ensure exists l2 l3, safeExec(ATrue, return(l2, l3), X) && sll(__return, l2) * sll(x, l3)
 */
{
    ...
    /*@ Inv exists l1 l2 l3, safeExec(ATrue, bind(sll_copy_M_loop(l1,l2,l3), sll_copy_M_loop_end), X) && t != 0 && t -> next == 0 && sllseg(x@pre, p, l1) * sll(p, l2) * sllseg(y, t, l3) */
    while (p) { ... }
}
```

## Use From Other Projects

### CLI

```bash
uv run --from /path/to/LLM4PV llm4pv input.c output_rel.c
uv run --from /path/to/LLM4PV llm4pv-guard "sll(p, l1)" "p"
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

1. **TransShape** (`GenMonads/transshape/`) — Extract `/*@ ... */` annotations and translate shape predicates to data predicates (`listrep` -> `sll`, `lseg` -> `sllseg`), adding list variables (`?l1`, `?l2`, ...). Supports multiple functions per file and variable prefixing for multi-loop disambiguation.
2. **GuardGen** (`GenMonads/guardgen/`) — Generate Rocq guard functions from loop conditions (null checks, pointer equality, `p->field` dereferences). Resolves pointer aliases from pure equalities in invariants (e.g., `u->next == w`).
3. **AddAbstract** (`GenMonads/addabstract/`) — Wrap loop invariants with `safeExec(ATrue, bind(...), X)` predicates and `exists` quantifiers. Require vars are lifted into the `With` clause; Ensure vars are wrapped with `exists`.
4. **C File Translation** (`GenMonads/translate_c_file.py`) — Orchestrate stages 1-3, replace annotations in the original C file, translate header includes. Handles multi-function files and annotations placed before or after function headers. Auto-inserts `#include "safeexec_def.h"` and generates `Import Coq` / `Extern Coq` declaration blocks.

## Predicate Mappings

| Shape Predicate | Data Predicate |
|----------------|----------------|
| `listrep(x)` | `sll(x, ?l1)` |
| `lseg(x, y)` | `sllseg(x, y, ?l1)` |
| `dlistrep(x)` | `dll(x, ?l1)` |
| `dlseg(x, p, n, y)` | `dllseg(x, p, n, y, ?l1)` |

Mappings are configured in `GenMonads/data/predicate_mappings.json`.

## Abstract Program Lib Generation

Generate `_rel_lib.v` files from one C file or a whole directory:

```bash
uv run llm4pv-rellib shape_invdataset/sll/sll_copy.c
uv run llm4pv-rellib shape_invdataset/sll
uv run llm4pv-rellib shape_invdataset/sll --output-dir ./output/gen/libs
```

By default, the output directory comes from `COQ_LIB_DIR` in `CONFIGURE`.
Generated libs use function-scoped guard names in multi-function files and define `maketuple` when a function returns multiple logical results.

## Shell Scripts

For generating Rocq verification conditions with the external `symexec` tool:

```bash
scripts/symexec.sh                              # use defaults from CONFIGURE
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
