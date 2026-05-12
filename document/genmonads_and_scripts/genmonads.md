# `GenMonads/` File Guide

This guide documents the source-facing files under `GenMonads/`. It focuses on what each file is for, the main entry points it exposes, and how it fits into the translation pipeline.

## Directory Structure

```text
GenMonads/
├── __init__.py
├── README.md
├── header_mapping.py
├── predicate_mapping.py
├── translate_c_file.py
├── conversation.md
├── refinement_proof_tutorial.md
├── data/
├── transshape/
├── guardgen/
├── addabstract/
├── absprog/
└── tests/
```

## Core Pipeline

| Stage | Main file | Responsibility |
| --- | --- | --- |
| Annotation extraction | `transshape/preprocess.py` | Finds `/*@ ... */` blocks, parses `With`/`Require`/`Ensure`, and extracts `Inv` assertions plus loop conditions |
| Assertion parsing | `transshape/parser.py` | Builds and recovers ASTs for shape assertions |
| Shape translation | `transshape/translator.py` | Renames predicates and appends existential list variables |
| Pipeline orchestration | `transshape/process_and_translate.py` | Runs extraction, translation, and optional guard generation |
| Guard generation | `guardgen/translate.py` | Converts loop conditions into Coq guard formulas over abstract values |
| `safeExec` injection | `addabstract/addexec.py` | Wraps translated `Require`/`Ensure`/`Inv` assertions with execution predicates |
| C file rewrite | `translate_c_file.py` | Applies the transformed annotations to C sources and inserts Coq blocks |
| Rocq skeleton generation | `absprog/gen_rel_lib.py` | Produces `_rel_lib.v` stubs and loop-program scaffolding |

## Top-Level Files

| File | Purpose | Key details |
| --- | --- | --- |
| `README.md` | Package-level overview of the translation pipeline | Summarizes extraction, translation, guard generation, `safeExec`, and C-file replacement |
| `__init__.py` | Public package export surface | Re-exports `translate_c_file`, `translate_directory`, and `gen_coq_guard` |
| `header_mapping.py` | Header include translation support | Persists include-name mappings in `data/header_mappings.json`; translates both `"header.h"` and `<header.h>` forms |
| `predicate_mapping.py` | Shape-predicate rename table management | Persists mapping from shape predicates to data predicates and the number of abstract list arguments to inject |
| `translate_c_file.py` | End-to-end annotated C rewriter | Replaces function specs and loop invariants, adds `safeexec_def.h`, inserts `Import Coq` and `Extern Coq` blocks, and writes `_rel.c` outputs |
| `conversation.md` | Example proof-assistant conversation log | Stores a detailed prompt/response style artifact for a concrete VC-proof workflow |
| `refinement_proof_tutorial.md` | Long-form proof tutorial | Explains the generated VC style, assertion syntax, and proof tactics for Rocq/Coq refinement proofs |

## Data Files

| File | Purpose | Notes |
| --- | --- | --- |
| `data/header_mappings.json` | Persisted header translation map | Defaults include `sll_shape_def.h -> sll_def.h` and `dll_shape_def.h -> dll_def.h` |
| `data/predicate_mappings.json` | Persisted predicate translation map | Stores shape-to-data predicate mappings in JSON list form |
| `data/guard_predicates.json` | Guard-generation predicate config | Stores built-in guard rules for root and segment predicates such as `sll`, `sllseg`, and `store_tree` |

### `GenMonads/data` JSON Schemas

These files are standard JSON files and should stay comment-free.

`header_mappings.json`

- Shape: `{ "original_header.h": "translated_header.h" }`
- Example:

```json
{
  "sll_shape_def.h": "sll_def.h",
  "dll_shape_def.h": "dll_def.h"
}
```

`predicate_mappings.json`

- Shape: `{ "shape_predicate": ["data_predicate", num_list_args] }`
- Example:

```json
{
  "listrep": ["sll", 1],
  "lseg": ["sllseg", 1]
}
```

`guard_predicates.json`

- Purpose: configure how `guardgen` interprets built-in predicates when generating Coq guards
- Supported top-level fields per predicate:
  - `kind`: `"root"` or `"segment"`
  - `arity`: number of predicate arguments
  - `payload`: map from payload field name to positional argument index
  - `abs_names`: payload fields that contribute abstract values to the generated Coq lambda binding
  - `root_null`: for root predicates, templates for null and non-null checks
  - `segment_eq`: for segment predicates, templates for pointer equality and inequality
- Example:

```json
{
  "sll": {
    "kind": "root",
    "arity": 2,
    "payload": {
      "ptr": 0,
      "abs": 1
    },
    "abs_names": ["abs"],
    "root_null": {
      "eq": "{abs} = []",
      "ne": "{abs} <> []"
    }
  }
}
```

## `transshape/`

### What this package does

`transshape/` is the front half of the pipeline. It extracts annotations from C files, parses assertion syntax into an AST, translates shape predicates, and optionally hands the result to guard generation.

### Files

| File | Purpose | Key details |
| --- | --- | --- |
| `transshape/__init__.py` | Package export surface | Re-exports parser, translator, extractor, and combined processing APIs; sets `__version__ = "1.0.0"` |
| `transshape/README.md` | Detailed usage and architecture guide | Documents input/output formats, variable numbering, guard generation, and examples |
| `transshape/parser.py` | Assertion parser and pretty-printer | Defines AST nodes such as `Var`, `BinOp`, `FieldAccess`, `Predicate`, `SepConj`, `AndConj`, and `Exists`; provides `parse_assertion`, `recover_formula`, and `recover_assertion` |
| `transshape/preprocess.py` | C annotation extractor | `AnnotationExtractor` reads C files, parses `With`/`Require`/`Ensure`, extracts `Inv` assertions, captures following `while (...)` guards, and supports multi-function files |
| `transshape/translator.py` | Shape-to-data translator | `ShapeTranslator` loads predicate mappings, tracks generated variables like `?l1`, supports optional loop prefixes, and offers `translate_assertion` plus `translate_assertion_with_exists` |
| `transshape/process_and_translate.py` | Pipeline orchestrator | `AssertionProcessor` combines extraction, translation, and optional `guardgen`; also exposes `process_and_translate_file` and directory variants |
| `transshape/example_usage.py` | Parser/translator examples | Shows basic parsing, translation, existential handling, custom translator use, and batch processing |
| `transshape/example_complete_pipeline.py` | Full-pipeline examples | Demonstrates file and directory processing and compares different calling styles |
| `transshape/example_separate_guard_gen.py` | Two-step workflow example | Shows translation first, guard generation second, and how to disable automatic guards |

### Important implementation notes

- `preprocess.py` supports both older single-function behavior and newer multi-function extraction.
- `translator.py` preserves backward compatibility for single-loop files by keeping unprefixed variables like `l1`, `l2`.
- `process_and_translate.py` stores guard-generation failures as `coq_guard_error` instead of crashing the whole pipeline.

## `guardgen/`

### What this package does

`guardgen/` turns translated heap invariants and loop conditions into Coq guard expressions. Its main design choice is a predicate registry, so new heap predicates can be added without editing the main translation logic.

### Files

| File | Purpose | Key details |
| --- | --- | --- |
| `guardgen/__init__.py` | Package bootstrap | Imports built-in predicate modules so they self-register, then exports `gen_coq_guard` and `gen_coq_from_bool` |
| `guardgen/README.md` | Full subsystem documentation | Explains registry design, supported syntax, extension points, and examples |
| `guardgen/registry.py` | Predicate registration core | Defines `PredicateSpec`, `PredKind`, global `PREDICATES`, and `register_predicate` |
| `guardgen/translate.py` | Boolean-to-Coq translation engine | Normalizes pointer names, parses invariants and conditions, resolves aliases, handles root-null and segment-equality cases, and emits `fun a => ...` Coq guards |
| `guardgen/cli.py` | Command-line wrapper | Accepts an invariant string and a condition string, then prints the generated Coq guard |
| `guardgen/demo.py` | Example driver | Runs a set of invariant/condition pairs to exercise guard generation and error handling |

### `guardgen/cond/`

| File | Purpose | Key details |
| --- | --- | --- |
| `guardgen/cond/__init__.py` | Re-export module | Exposes `parse_cond_full`, `AtomKind`, `AtomCond`, and `BoolNode` |
| `guardgen/cond/ast.py` | Condition AST definitions | Models pointer-null and pointer-pointer atoms plus boolean tree nodes |
| `guardgen/cond/lexer.py` | Condition tokenizer | Tokenizes `&&`, `||`, `!`, `==`, `!=`, `<>`, `->`, identifiers, and `0` |
| `guardgen/cond/parser.py` | Boolean condition parser | Parses grouped boolean expressions and supports sugar such as bare `p` meaning `p != null` and `p->next` as a pointer expression |

### `guardgen/parsing/`

| File | Purpose | Key details |
| --- | --- | --- |
| `guardgen/parsing/__init__.py` | Re-export module | Exposes invariant normalization and parsing helpers |
| `guardgen/parsing/invariant.py` | Invariant parser | Splits spatial atoms, strips leading `exists`, resolves registered predicates, and extracts pure alias equalities like `u->next == w` |

### `guardgen/predicates/`

| File | Purpose | Key details |
| --- | --- | --- |
| `guardgen/predicates/__init__.py` | Built-in predicate bootstrap | Imports built-ins for registration side effects |
| `guardgen/predicates/sll.py` | Singly-linked-list predicate specs | Registers `sll` as a root predicate and `sllseg` as a segment predicate |
| `guardgen/predicates/tree.py` | Tree predicate spec | Registers `store_tree` as a root predicate |

### Important implementation notes

- `guardgen/translate.py` normalizes spacing around `->`, so `u -> next` and `u->next` resolve to the same pointer key.
- Alias extraction in `guardgen/parsing/invariant.py` lets conditions reuse pure equalities already present in the invariant.
- Segment predicates handle pointer equality/inequality, while null checks require a root predicate.

## `addabstract/`

### What this package does

`addabstract/` injects `safeExec(...)` predicates into translated assertions. It handles loop invariants and function specifications differently because function specs also need `With`-clause management.

### Files

| File | Purpose | Key details |
| --- | --- | --- |
| `addabstract/README.md` | User guide for `safeExec` insertion | Covers loop invariants, function specs, and integration with the translation pipeline |
| `addabstract/__init__.py` | Export surface | Re-exports loop-invariant and function-spec helpers from `addexec.py` |
| `addabstract/addexec.py` | `safeExec` transformation logic | Provides `add_safeexec_predicate`, `add_safeexec_to_assertion`, `add_with_parameter`, `extract_variables_from_assertion`, `add_safeexec_to_require`, `add_safeexec_to_ensure`, and `process_funcspec_with_safeexec` |

### Important implementation notes

- Loop invariants use `bind(program_loop(...), program_loop_end)` inside `safeExec(...)`.
- `Require` clauses move generated variables into the `With` clause (e.g. `With X l1`), drop the `?` prefix, and wrap the body with `safeExec(...)`. The leading `exists` is lifted away because the vars are now bound at `With` scope.
- `Ensure` clauses keep the `exists` quantifier in front of the body (e.g. `Ensure exists l2, safeExec(ATrue, return(l2), X) && sll(__return, l2)`).

## `absprog/`

### What this package does

`absprog/` generates Rocq-side program skeletons that line up with the translated C annotations and generated guards.

### Files

| File | Purpose | Key details |
| --- | --- | --- |
| `absprog/__init__.py` | Export surface | Re-exports `generate_rel_lib` and `generate_rel_lib_for_file` |
| `absprog/cli.py` | CLI for `_rel_lib.v` generation | Accepts a file or directory input, resolves the default output directory via `GenMonads.cli_common.read_configure_value("COQ_LIB_DIR")` (env var or `CONFIGURE` file — no hardcoded path fallback), and writes skeleton `.v` files |
| `absprog/gen_rel_lib.py` | Rocq library generator | Builds imports, `MretTy` (shared or per-function), function-scoped guard definitions such as `sll_copy_guardP`, loop-body scaffolding, and function-level `Parameter`/`Definition` blocks for each translated function |
| `absprog/assemble.py` | Per-function lib assembly and merge | Assembles one function's LLM-provided blocks into the skeleton; `merge_rel_libs_into_file` combines multiple per-function libs into a single multi-function lib (used by multi-function synthesis) |
| `absprog/synthesize.py` | Synthesis pipeline | Runs the LLM/backend loop, writes per-attempt artefacts, and promotes the accepted `_rel_lib.v` to `COQ_LIB_DIR`. `run_synthesis_pipeline` accepts `promote_rel_lib=False` so multi-function runs can defer promotion until after merge |
| `absprog/synth_cli.py` | `llm4pv-synth` CLI | Handles single-file, multi-function-auto, and directory modes; orchestrates the merge step for multi-function C files |

### Important implementation notes

- `gen_rel_lib.py` reuses `process_and_translate_file(...)` and `collect_func_extern_info(...)`, so the Rocq stub shape tracks the same translated assertion structure as the C rewrite stage.
- The first invariant guard, if available, becomes a concrete function-scoped guard definition such as `{func_name}_guardP`, which avoids name collisions in multi-function files.
- If any translated function returns more than one logical result, the generated `_rel_lib.v` also defines `maketuple` concretely as `(a, b)` so later VC files can reuse it.
- **`MretTy` scoping**: a single-function `_rel_lib.v` declares `Parameter MretTy : Type.` once at the top and shares it. A multi-function lib instead declares `Parameter {func}_MretTy : Type.` inside each function's section and uses that scoped name everywhere in the section. This prevents one function's synthesized `MretTy` body from clashing with another's.
- **Multi-function synthesis and merge**: `llm4pv-synth` on a multi-function C file without `--func-name` synthesizes each target into its own subdirectory, suppresses per-function promotion, then merges all accepted per-function libs into a single `{basename}_rel_lib.v` in `COQ_LIB_DIR`. Stale `{func}_rel_lib.v` files from older promotion runs are removed during merge.
- **Data witnesses**: loop invariants of the form `exists w, ... t -> data == w ...` promote `w` (type `Z`) into the abstract loop state. The field list (`data`, `key`, `val`) is stored in `GenMonads/data/data_fields.json`; extend it when new data-bearing fields appear. Existentials bound to pointer fields (e.g., `exists nxt, x -> next == nxt`) are intentionally excluded.

## Tests

### What the test suite covers

The tests under `GenMonads/tests/` validate parser behavior, extraction and translation, guard generation, `safeExec` insertion, header mapping, multi-function handling, and final file rewriting.

### Files

| File | Purpose | Key details |
| --- | --- | --- |
| `tests/conftest.py` | Test import bootstrap | Adds the repository root to `sys.path` so the package can be imported during pytest runs |
| `tests/test_addabstract.py` | `safeExec` insertion tests | Covers loop invariants, function specs, and integration on real dataset files |
| `tests/test_guardgen_cond.py` | Guard-condition parser and alias tests | Exercises `->` field dereferences, bare-pointer sugar, alias extraction, and guard generation integration |
| `tests/test_header_mapping.py` | Header mapping tests | Validates defaults, persistence helpers, resets, and include rewriting |
| `tests/test_multifunction.py` | Multi-function pipeline tests | Checks extraction, prefixed variable naming, function-local replacement, and end-to-end behavior on multi-function inputs |
| `tests/test_parser.py` | AST parser/recovery tests | Confirms parsing and round-tripping of predicates, conjunctions, field accesses, `exists`, and `emp` |
| `tests/test_translate_c_file.py` | Final C rewrite tests | Verifies translated outputs, `safeexec_def.h` insertion, generated Coq blocks, and directory translation |
| `tests/test_transshape_pipeline.py` | Integrated pipeline tests | Covers preprocessing, translation, optional guard generation, and consistency between automatic and manual modes |
| `tests/testtodo.md` | Test coverage checklist | Human-readable inventory of the intended test scenarios and current coverage |

## Reference and Notes Files

| File | Purpose | Notes |
| --- | --- | --- |
| `conversation.md` | Captured proof-oriented prompt history | Useful as an example of how the generated artifacts feed downstream proof work |
| `refinement_proof_tutorial.md` | Proof cookbook | Explains separation-logic syntax and common Rocq tactics such as `pre_process_default`, `entailer!`, `Intros`, `Exists`, and `sep_apply` |

## Practical Entry Points

If you need the smallest set of files to understand the main system, start here:

1. `GenMonads/README.md`
2. `GenMonads/transshape/preprocess.py`
3. `GenMonads/transshape/translator.py`
4. `GenMonads/transshape/process_and_translate.py`
5. `GenMonads/guardgen/translate.py`
6. `GenMonads/addabstract/addexec.py`
7. `GenMonads/translate_c_file.py`
8. `GenMonads/absprog/gen_rel_lib.py`
