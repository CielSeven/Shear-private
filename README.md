# LLM4PV

Translating C programs with shape assertions to data predicates and abstract programs for formal verification in Rocq (Coq).

## Quick Start

Requires [uv](https://docs.astral.sh/uv/).

```bash
# Translate a single C file
uv run llm4pv shape_invdataset/sll/sll_copy.c output/shape/rel/sll/sll_copy_rel.c

# Translate an entire directory
uv run llm4pv shape_invdataset/sll output/shape/rel/sll

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
struct list * sll_copy(struct list * x)
/*@ Require sll(x, ?l1)
    Ensure  sll(__return, ?l2) * sll(x, ?l3)
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

1. **TransShape** (`GenMonads/transshape/`) — Extract `/*@ ... */` annotations and translate shape predicates to data predicates (`listrep` -> `sll`, `lseg` -> `sllseg`), adding list variables (`?l1`, `?l2`, ...)
2. **GuardGen** (`GenMonads/guardgen/`) — Generate Rocq guard functions from loop conditions (null checks, pointer equality)
3. **AddAbstract** (`GenMonads/addabstract/`) — Wrap loop invariants with `safeExec(ATrue, bind(...), X)` predicates and `exists` quantifiers
4. **C File Translation** (`GenMonads/translate_c_file.py`) — Orchestrate stages 1-3, replace annotations in the original C file, translate header includes

## Predicate Mappings

| Shape Predicate | Data Predicate |
|----------------|----------------|
| `listrep(x)` | `sll(x, ?l1)` |
| `lseg(x, y)` | `sllseg(x, y, ?l1)` |
| `dlistrep(x)` | `dll(x, ?l1)` |
| `dlseg(x, p, n, y)` | `dllseg(x, p, n, y, ?l1)` |

Mappings are configured in `GenMonads/data/predicate_mappings.json`.

## Shell Scripts

For generating Rocq verification conditions with the external `symexec` tool:

```bash
scripts/symexec.sh                              # use defaults from CONFIGURE
scripts/symexec.sh --C_DIR=./shape_invdataset/sll  # override input dir
scripts/clean_symexec.sh --C_DIR=./shape_invdataset/sll  # clean generated files
```

Configured via the `CONFIGURE` file at repo root.

## Limitations

- Each C file should contain one main function
- Requires specific annotation format `/*@ ... */`
- Guard generation limited to registered predicates
