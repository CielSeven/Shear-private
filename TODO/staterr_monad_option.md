# Plan: Optional StateErrMonad (MonadErr) backend for rel_lib generation

## Goal

Today the generated `{basename}_rel_lib.v` files are hard-wired to the **state
relational monad** (`StateRelMonad`). Add a CLI option so that running `llm4pv`
(and `llm4pv-rellib` / `llm4pv-synth`) can instead generate rel_lib files against
the **error-aware state relational monad** (`MonadErr`, a.k.a. "stateErrMonad").

Surface: a `--monad {staterel,staterr}` flag, default `staterel` (keeps current
behavior). Both monads live in `../RHLProjects/EncRelTheory-Private/monadlib/`.

## The only generated difference: the import/export header

The two monads export the **same** combinator names and notations
(`program`, `MONAD`, `bind`/`;;`, `ret`, `choice`, `any`, `assume`/`assume!!`,
`break`/`continue`/`repeat_break`/`CntOrBrk`, `safeExec`). So the generated
**body is byte-for-byte identical** — only the header changes.

Current header (`GenMonads/absprog/gen_rel_lib.py:85-102`):

```coq
From MonadLib Require Import MonadLib.
Export StateRelMonad.
Export MonadNotation.
Local Open Scope monad.
```

`staterr` header:

```coq
From FP Require Import PartialOrder_Setoid BourbakiWitt.
From MonadLib.MonadErr Require Import StateRelMonadErr.
Import MonadNotation.
Local Open Scope monad.
```

The staterr header imports the err monad **directly** — *not* via
`From MonadLib Require Export MonadLib`. Importing the aggregated `MonadLib` pulls
in StateRelMonad as well, leaving both monads' `program` (hence `MONAD`, `bind`, …)
in scope and ambiguous; under the body that builds MonadErr programs this is a bug.
Importing only `MonadLib.MonadErr.StateRelMonadErr` keeps `program`/`MONAD`
unambiguously the MonadErr ones, and `Import` (not `Export`) avoids re-exporting the
monad downstream. The extra `From FP … BourbakiWitt` is needed because MonadErr's
`repeat_break` is built on the Bourbaki-Witt fixpoint.

## Implementation steps

### 1. Make the import header monad-aware (`gen_rel_lib.py`)
- Replace the `COQ_IMPORTS` constant (`:85-102`, used at `:561`) with a helper
  `def coq_imports(monad: str = "staterel") -> str: ...` that emits the shared
  prelude plus the monad-specific header lines, keyed by:
  ```python
  MONAD_EXPORTS = {"staterel": "StateRelMonad", "staterr": "StateRelMonadErr"}
  ```

### 2. Thread `monad` through generation (`gen_rel_lib.py`)
- `generate_rel_lib(...)` (`:548`) — add `monad="staterel"`; pass to `coq_imports` at `:561`.
- `generate_rel_lib_for_file(...)` (`:656`) — add `monad`; forward to `generate_rel_lib`.
- `generate_func_block(...)` and the no-loop / simple-block paths need **no change**
  (bodies are monad-agnostic).

### 3. Standalone rel_lib CLI (`absprog/cli.py`)
- Add `--monad {staterel,staterr}` (default `staterel`) near `:37-45`.
- Pass `monad=args.monad` into `generate_rel_lib_for_file(...)` (`:77-86`).

### 4. Synthesis pipeline (`absprog/synth_cli.py` + `synthesize.py`)
- `synth_cli.py`: add `--monad` (alongside `:142-231`); forward into
  `run_synthesis_pipeline(...)` (`:67-80`, `:272-286`).
- `synthesize.py`: add `monad="staterel"` to `run_synthesis_pipeline(...)`
  (`:609-624`); forward to skeleton generation and to
  `assemble.merge_rel_libs_into_file(...)` (multi-function merge re-emits the
  header — keep it consistent).

### 5. Top-level `llm4pv` CLI (`translate_c_file.py`)
- Add `--monad` near the pipeline flags (`:953-1004`).
- `_run_stage2(...)` (`:1087-1090`) — add `monad`, forward to `generate_rel_lib_for_file`.
- Pass `monad=args.monad` at the stage-2 call site (`:1221`) and the synth call site.

## Files to touch

| File | Change |
|---|---|
| `GenMonads/absprog/gen_rel_lib.py` | `coq_imports()` helper + `monad` param on `generate_rel_lib` / `generate_rel_lib_for_file` |
| `GenMonads/absprog/cli.py` | `--monad` arg, forward to generator |
| `GenMonads/absprog/synth_cli.py` | `--monad` arg, forward to pipeline |
| `GenMonads/absprog/synthesize.py` | `monad` param on `run_synthesis_pipeline`, forward to skeleton + merge |
| `GenMonads/translate_c_file.py` | `--monad` arg, `_run_stage2` param, forward to stage-2 + synth |
| `CLAUDE.md` | document the new flag |

## Open questions

1. **Is `From FP Require Import PartialOrder_Setoid BourbakiWitt.` strictly needed**
   at the rel_lib site, or already transitive via `MonadLib`? Default to emitting it;
   the compile probe decides.
2. **Does `assemble.merge_rel_libs_into_file` re-emit or copy the header?** Determines
   how step 4's merge branch threads the flag.
3. **Should `--monad` have a `CONFIGURE` default** (like `COQ_LIB_DIR`)?

## Verification / testing

1. **Coq probe (do first):** hand-write a `staterr`-header `_rel_lib.v` with an
   existing skeleton body (e.g. `sll_copy`) and compile against MonadLib — confirms
   the header and the `From FP` line before any Python changes.
2. **Golden-file test:** generate `sll_copy_rel_lib.v` with `--monad staterel` vs
   `--monad staterr`; assert the only diff is the header. Add under `GenMonads/tests/`.
3. **Regression:** existing tests pass unchanged with the default (`staterel`).
