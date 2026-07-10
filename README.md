# LLM4PV

Translating C programs with shape assertions to data predicates, replaying their
verification proofs, and generating relational C programs plus Rocq (Coq)
refinement lemmas.

## Quick Start

Requires [uv](https://docs.astral.sh/uv/) and a working QCP `symexec`
configuration in [`CONFIGURE`](CONFIGURE). Run all commands from the repository
root.

The current workflow uses the verified shape program as the proof source. It
first translates that program to a data-predicate version, asks `symexec` to
record the successful data proof, and then deterministically replays that proof
to generate the relational program, abstract code, and refinement lemmas.

### 0. Check the shape-program baseline

Run `symexec` on a shape-annotated C file or directory:

```bash
scripts/symexec.sh --C_DIR=shape-bench/glibc_slist/
```

Before continuing, inspect the generated `*_proof_manual.v` files under the
configured `OUTPUT_PATH`. They must be empty or contain **only**
`*_safety_wit_*` goals. Any remaining `*_entail_wit_*` or `*_return_wit_*`
means the shape proof is not fully automatic and is not yet a suitable replay
source.

For the default `OUTPUT_PATH=./output/shape/vcs`, this check should print no
matches:

```bash
rg -n '_(entail|return)_wit_' output/shape/vcs/*_proof_manual.v
```

### 1. Generate the data version and record its proof

Translate all shape predicates and sibling headers to their data forms:

```bash
uv run llm4pv shape-bench/glibc_slist \
  bench-gen/glibc_slist/datac \
  --data-only --translate-header
```

This emits `*_data.c` files. Run `symexec` with automatic VC recording enabled:

```bash
scripts/symexec.sh \
  --C_DIR=bench-gen/glibc_slist/datac \
  --AUTO_VC \
  --AUTOVC_DIR=bench-gen/glibc_slist/datac/autovc \
  --OUTPUT_PATH=bench-gen/glibc_slist/datac/vcs/ \
  --LOGDIR=bench-gen/glibc_slist/logs/datac/
```

The important replay artifacts are
`bench-gen/glibc_slist/datac/autovc/*_data_autovc.c`.

### 2. Replay the proof to generate code and lemmas

```bash
uv run llm4pv shape-bench/glibc_slist \
  bench-gen/glibc_slist/relc \
  --autovc-dir=bench-gen/glibc_slist/datac/autovc \
  --coq-lib-dir=bench-gen/glibc_slist/libs \
  --translate-header --monad=staterr --seg-lemmas
```

`segcodegen` is the default backend. It consumes the recorded data VCs without
an LLM synthesis call and produces:

- `bench-gen/glibc_slist/relc/*_rel.c` — relational C programs;
- `bench-gen/glibc_slist/libs/*_rel_lib.v` — filled abstract programs; and
- `bench-gen/glibc_slist/libs/*_seg_lemmas.v` — per-arm, branch-selection, and
  fused refinement lemmas, all closed with `Qed`.

Use `--seg-lemmas-check` instead of `--seg-lemmas` to additionally compile each
generated lemma file with `coqc`.

The same workflow accepts a single C file: use `--FILE=<path>` with
`scripts/symexec.sh`, and pass explicit `*_data.c` / `*_rel.c` output paths to
`llm4pv`. Sibling-header translation is a directory-mode feature.

Run the Python test suite with:

```bash
uv run --with pytest pytest
```

### `llm4pv` flags

The end-to-end command exposes per-stage opt-outs and synthesis passthrough flags:

| Flag | Default | Notes |
|---|---|---|
| `--no-rel-lib` | off | Skip stage 2. Incompatible with default synth — pair with `--no-synth`. |
| `--coq-lib-dir DIR` | `COQ_LIB_DIR` from env/CONFIGURE | Where filled `_rel_lib.v` files and segment lemmas land. |
| `--no-synth` | off | Skip stage 3. |
| `--synth-output-dir DIR` | — | Required by `command`/`response-file`; unused by `segcodegen`. |
| `--backend` | `segcodegen` | `segcodegen`, `response-file`, or `command`. |
| `--autovc-dir DIR` | — | Directory containing the recorded `*_data_autovc.c` proofs required by `segcodegen`. |
| `--data-only` | off | Emit only raw `*_data.c`; implies `--no-rel-lib --no-synth`. |
| `--translate-header` | off | In directory mode, translate sibling headers as well as C files. |
| `--monad` | `staterel` | Generate `staterel` or error-aware `staterr` abstract programs. |
| `--seg-lemmas` | off | Generate proved segment refinement lemmas after replay. |
| `--seg-lemmas-check` | off | Generate segment lemmas and compile them with `coqc`. |
| `--command` | empty | Deprecated compatibility flag; workdir-mode owns the Codex invocation. |
| `--few-shot` | — | Repeatable few-shot JSON. |
| `--max-retries` | `2` | Repair attempts after the first try. |
| `--no-patch-rel-c` | off | Skip post-synth patching of the generated `_rel.c`. |
| `--no-check` | off | Skip the Rocq syntax check inside synthesis. |

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
# Shape -> data only (the first Python step in the replay workflow)
uv run --from /path/to/LLM4PV llm4pv input_dir data_dir \
  --data-only --translate-header

# Plain shape -> relational translation without lib generation or replay
uv run --from /path/to/LLM4PV llm4pv input.c output_rel.c \
  --no-rel-lib --no-synth

uv run --from /path/to/LLM4PV llm4pv-guard "sll(p, l1)" "p"
uv run --from /path/to/LLM4PV llm4pv-context input.c output.auto.json
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

1. **Shape baseline** (`scripts/symexec.sh`) — Verify that the source shape
   proof leaves no manual entailment or return witnesses.
2. **Data translation** (`--data-only`) — Extract `/*@ ... */` annotations and
   translate shape predicates to data predicates (`listrep` -> `sll`, `lseg`
   -> `sllseg`) without adding `safeExec`. With `--translate-header`, sibling
   headers and their specifications are translated too.
3. **Proof recording** (`scripts/symexec.sh --AUTO_VC`) — Verify each
   `*_data.c` and record the successful `WitnessTrySolve` trace in
   `*_data_autovc.c`.
4. **Relational translation** (`GenMonads/transshape/`, `guardgen/`, and
   `addabstract/`) — Generate guards, lift data witnesses into monadic state,
   wrap specifications in `safeExec`, and emit `*_rel.c`.
5. **Abstract code generation** (`GenMonads/absprog/segcodegen/`) — Build the
   `{basename}_rel_lib.v` skeleton and deterministically fill its abstract
   program definitions from the recorded data proof. The generated `_rel.c` is
   patched to use the concrete return type and any required residual programs.
6. **Refinement lemma generation** (`--seg-lemmas`) — Emit proved per-arm,
   loop branch-selection, and fused segment lemmas in
   `{basename}_seg_lemmas.v`.

Because `symexec` is external to the Python process, the replay workflow uses
the three commands in Quick Start rather than one monolithic command. For an
already-recorded proof, `uv run llm4pv` performs stages 4–6 in one pass.

### Cross-file callees and directory ordering

When a function in `a.c` calls a function defined in sibling `b.c`, the caller's `a_rel_lib.v` emits `Require Import b_rel_lib.` instead of an opaque `Parameter b_M`. For Rocq to compile the merged libs, `b_rel_lib.v` must be filled before `a` is generated.

In directory mode, `llm4pv` builds a dependency graph from sibling `.c` calls and processes files in topological order — callees first. The chosen order is printed as `Processing order (callees first): ...`. A cyclic dependency triggers a warning and falls back to alphabetical order; you'll need to break the cycle manually (e.g., synthesize one side once with `--no-synth`, then come back).

Truly external callees (defined outside the directory, e.g. libc) stay as opaque `Parameter callee_M : <type>.` in the caller's lib — no ordering is needed for them.

## Predicate Mappings

| Shape Predicate | Data Predicate |
|----------------|----------------|
| `listrep(x)` | `sll(x, ?l1)` |
| `lseg(x, y)` | `sllseg(x, y, ?l1)` |
| `dlistrep(x)` | `dll(x, ?l1)` |
| `dlseg(x, p, n, y)` | `dllseg(x, p, n, y, ?l1)` |

Mappings are configured in `GenMonads/data/predicate_mappings.json`. Guard-side translations (root-null, segment-eq, field-deref) for the same predicates live in `GenMonads/data/guard_predicates.json`. Data-witness extraction no longer relies on a hand-maintained field list — it walks `store(addr, T, var)` predicates (typed from the C `struct` definitions) and carries `var` iff `T` is a scalar/boolean type.

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

## Abstract Program Generation Backends

The default `segcodegen` backend fills abstract programs deterministically from
the proof recorded by `symexec --AUTO_VC`. It can also be run through the
stage-isolated CLI:

```bash
uv run llm4pv-synth shape-bench/glibc_slist \
  --backend=segcodegen \
  --autovc-dir=bench-gen/glibc_slist/datac/autovc \
  --coq-lib-dir=bench-gen/glibc_slist/libs \
  --monad=staterr
```

The `command` and `response-file` backends remain available for experimental
LLM-driven generation and require an artifact output directory:

```bash
uv run llm4pv-synth shape_invdataset/sll/sll_copy.c ./output/gen/synth/sll_copy \
  --backend=command
```

Useful options:

- `--func-name` selects a target function in multi-function C files. If omitted on a multi-function file, every target function is synthesized into its own subdirectory under the output directory, and the accepted per-function libs are merged into a single `{basename}_rel_lib.v` in `COQ_LIB_DIR`.
- `--backend` chooses `segcodegen`, `response-file`, or `command`.
- `--autovc-dir` points `segcodegen` to the recorded data-proof directory.
- `--coq-lib-dir` is the output directory for filled libraries.
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
scripts/symexec.sh --C_DIR=./data --AUTO_VC     # record replayable proofs in ./data/autovc
scripts/symexec.sh --C_DIR=./output/gen/rel/sll --OUTPUT_PATH=./output/gen/vcs/ --LOGDIR=./output/gen/logs/
scripts/symexec.sh --clean --C_DIR=./shape_invdataset/sll --OUTPUT_PATH=./output/shape/vcs/ --LOGDIR=./output/shape/logs/
```

Pass `--AUTOVC_DIR=<dir>` to choose the proof-recording directory explicitly.

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
