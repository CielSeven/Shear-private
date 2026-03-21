# LLM4PV Implementation Plan

Objective: Extend the translator to handle real-world C code complexity (multiple functions, sequential/nested loops, etc.), as outlined in `streamA_plan.md`.

---

## Phase 1: Structural Complexity & Parser Refactoring
*Goal: Support multiple functions and complex loop structures within a single C file.*

- [x] **Research & Audit**: Analyze `transshape/parser.py` and `translate_c_file.py` for current function/loop handling logic
- [x] **Research & Audit**: Identify limitations when processing multiple `/*@ ... */` blocks across different functions
- [x] **Multi-function extraction**: Refactor `TransShape` (preprocess.py) to extract and maintain context for multiple functions per file
- [x] **Variable prefixing**: Implement unique variable naming per loop/function (`l1_1`, `l1_2`, etc.) in `translator.py`
- [x] **Orchestration**: Update `process_and_translate.py` to apply prefix logic (single Inv → no prefix, multiple → prefixed)
- [x] **AddAbstract**: Generate correct `exists` wrapping and `safeExec` for complex structures in `addexec.py`
- [x] **End-to-end integration**: Update `translate_c_file.py` for multi-function mode with per-function spec/invariant replacement
- [x] **Test**: Create `tests/test_complex_structure.c` with multiple functions and nested loops
- [x] **Test**: Comprehensive test suite in `test_multifunction.py` (77 tests) and `test_addabstract.py` (18 tests)
- [x] **Validate**: All 145 tests pass, no regressions

---

## Phase 2: Enhanced Condition Parsing in GuardGen
*Goal: Extend the condition lexer/parser to handle field dereference (`->`) so GuardGen can process real-world loop conditions like `while (u->next)`.*

*Key insight: The invariant parser already treats `u -> next` as a plain string argument to spatial predicates (e.g., `sll(u -> next, l1)` → `ptr = "u -> next"`). So we treat `u->next` as a compound pointer name string — no new AST types or predicate handlers needed.*

### Task 2.1: Extend lexer to tokenize `->` (arrow operator)
- [x] Add `ARROW` token to `guardgen/cond/lexer.py` regex: `(?P<ARROW>->)`
  - Insert before `ID` pattern to avoid partial match
- [x] Verify `u->next` no longer causes `Unexpected char` error

### Task 2.2: Extend parser to handle field access as compound pointer name
- [x] In `parse_atomic_cond()` (`guardgen/cond/parser.py:65`), after eating initial `ID`, check for `ARROW` token
  - If `ARROW` found: eat `ARROW`, eat next `ID` (field name), concatenate as `"ptr->field"` string
  - Use this compound string as `ptr1` in `AtomCond` — no AST changes needed
- [x] Bare `u->next` → `AtomCond(PTR_NE_NULL, ptr1="u->next")` (same sugar as bare `p`)
- [x] `u->next == null` / `u->next != 0` → standard null comparison with compound ptr1

### Task 2.3: Pointer name normalization + pure equality alias resolution
- [x] In `gen_coq_from_bool()` (`guardgen/translate.py`), normalize `->` spacing when building `roots_by_ptr` keys and `seg_ptrs`
  - Canonical form: strip spaces around `->` (e.g., `"u -> next"` → `"u->next"`)
- [x] Apply same normalization in `_render_root_null` and `_render_seg_eq` lookup
  - This ensures condition `"u->next"` matches invariant arg `"u -> next"`
- [x] Extract pure equalities from invariant (e.g., `u -> next == w`) to build alias map
  - Add `extract_pure_aliases()` in `guardgen/parsing/invariant.py`
  - Parse chunks like `X == Y` that aren't predicate calls
  - Build bidirectional alias map (normalized): `u->next` ↔ `w`
- [x] In `_render_root_null`, when direct lookup fails, resolve through alias map
  - e.g., `u->next` not in `roots_by_ptr` → alias says `u->next == w` → look up `w` → found `sll(w, l1)`
  - Same for `_render_seg_eq`: resolve aliases for both endpoints

### Task 2.4: Tests
- [x] Create `GenMonads/tests/test_guardgen_cond.py`:
  - Lexer: `u->next` tokenizes to `[ID, ARROW, ID]`
  - Lexer: `u -> next` (with spaces) tokenizes correctly
  - Parser: bare `u->next` → `AtomCond(PTR_NE_NULL, ptr1="u->next")`
  - Parser: `u->next == null` → `AtomCond(PTR_EQ_NULL, ptr1="u->next")`
  - Parser: `p && p->next` → compound boolean with field access
  - Integration: `gen_coq_guard("sll(u -> next, l1) * lseg(x, t, l2)", "u->next")` → `l1 <> []`
  - Error: `p->` without field name raises error
- [ ] Fixture test: run pipeline on `shape_invdataset/sll/sll_rotate.c` (both functions)
- [x] Full regression: `uv run --with pytest pytest` — 165 passed, 6 skipped

### Real-world conditions reference
| File | Condition | Status |
|---|---|---|
| `sll/sll_rotate.c:18` | `u->next` | **Needs this phase** |
| `sll/sll_rotate.c:43` | `u` | Already works |
| `sll/sll_merge.c:29` | `x && y` | Already works |
| All other sll/dll files | `p` / `u` / `curr` / `p != head` | Already works |

---

## Phase 3: safeexec_def.h Include & Coq Import/Extern Blocks
*Goal: Generate the `#include "safeexec_def.h"` and `/*@ Import Coq ... */` / `/*@ Extern Coq ... */` blocks required by the downstream Coq verification toolchain (`symexec`).*

- [x] **`insert_safeexec_include`**: Insert `#include "safeexec_def.h"` after the last `#include` line (idempotent)
- [x] **`collect_func_extern_info`**: Extract require var count and max inv var count per function; skip helper functions without loop invariants
- [x] **`generate_coq_blocks`**: Generate `/*@ Import Coq Require Import {basename}_rel_lib */`, `/*@ Extern Coq (MretTy :: *) */`, and multi-line `/*@ Extern Coq ... */` with `{func}_M`, `{func}_M_loop`, `{func}_M_loop_end` type signatures
- [x] **`insert_blocks_after_includes`**: Insert generated blocks after the last `#include` line
- [x] **Orchestration**: Update `translate_c_file()` to collect extern info during per-function processing and call new functions after header translation
- [x] **Tests**: 11 new tests in `test_translate_c_file.py` (unit + integration)
- [x] **Validate**: All 186 tests pass, no regressions

---

## Phase 4: Existential Quantification in Function Specifications
*Goal: Wrap function spec variables with `exists` and drop `?` prefix, so generated Require/Ensure use `exists l1, ... sll(head, l1)` instead of `... sll(head, ?l1)`.*

- [x] **Identify transformation point**: `addabstract/addexec.py` — `add_safeexec_to_require()` and `add_safeexec_to_ensure()` are where `?`-prefixed vars flow into the final Require/Ensure output
- [x] **Implement `exists` wrapping**: Modified both functions to strip `?`, replace in assertion body, and prepend `exists l1 l2 ...,`
- [x] **Preserve invariant behavior**: Loop invariant path (`add_safeexec_predicate`) already handled exists correctly — unchanged
- [x] **Tests**: Updated `test_addabstract.py` (8 assertions) and `test_translate_c_file.py` (1 assertion) to expect new format
- [x] **Validate**: All 186 tests pass, 6 skipped, no regressions

---

## Phase 5: Function Call Annotations & Inter-Procedural Translation
*Goal: Preserve or generate the annotations required for function calls inside translated `_rel.c` files, so downstream symbolic execution can reason about calls such as `sll_multi_merge_rel.c -> sll_merge`.*

- [ ] **Audit call sites**: Identify functions in `shape_invdataset/` whose translated `_rel.c` bodies call other annotated functions (e.g. `sll_multi_merge` calling `sll_merge`)
- [ ] **Specify call annotation format**: Define what annotation shape the downstream symbolic executor expects around a function call in generated `_rel.c`
- [ ] **Translation strategy**: Decide whether call annotations should be:
  - preserved from the original C source when already present
  - synthesized from the callee's translated `Require` / `Ensure`
  - or inserted via a dedicated call-annotation generation pass in `translate_c_file.py`
- [ ] **Function summary extraction**: Add a representation for translated per-function call summaries that can be reused at call sites
- [ ] **Call-site rewrite**: Update the translator/output stage so generated files add correct annotations for intra-file and cross-file function calls
- [ ] **Dataset example**: Add an explicit regression case for `sll_multi_merge_rel.c` calling `sll_merge`
- [ ] **Tests**: Add end-to-end tests proving symbolic execution no longer fails due to missing function call annotations
- [ ] **Validate**: Run `pytest` and at least one downstream symbolic-execution check on a translated file with calls

---

## Phase 6: Shape Complexity & Predicate Expansion
*Goal: Support all predicates from Section 3.1 and implement tree structures.*

- [ ] Update `GenMonads/data/predicate_mappings.json` to include `dlistrep`, `dllseg`, `dllsegR`
- [ ] Implement `store_tree` predicate mapping in `GenMonads/guardgen/predicates/tree.py` (or similar)
- [ ] Add support for recursive tree structures in the translator
- [ ] Add tree and doubly-linked list examples to `shape_invdataset/`
- [ ] Run full pipeline tests and verify predicate translations

---

## Phase 7: Dataset Expansion & Final Verification
*Goal: Ensure the pipeline works for the full expanded dataset.*

- [ ] Expand `shape_invdataset` with trees, sorted lists, and circular lists
- [ ] Update `main.tex` (in `../llm4pv-latex/`) with `sll_append` and `bst_search` examples
- [ ] Run `scripts/symexec.sh` on the entire dataset
- [ ] Final `pytest` run to confirm 100% pass rate on all structural and shape complexities

---
*Each phase must be validated with `pytest` before proceeding to the next.*
