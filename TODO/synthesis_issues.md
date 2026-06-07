# Synthesis Module Issues

## `parse_coq.py`

- [x] `_extract_definition_block` terminates at the first line ending with `.`. If the LLM mistakenly uses `.` as a statement separator inside a definition body (e.g. writes `x <- step s.` instead of `x <- step s;;`), the extractor stops early and returns a truncated definition. The parse stage succeeds without error, but the assembled `.v` file is broken. The Rocq check then catches it — however the failure is recorded as `"rocq"` rather than `"parse"`, so the repair prompt describes a Rocq error on a truncated definition, potentially misleading the LLM about what it got wrong.
  - **Fixed**: replaced the line-by-line `line.strip().endswith(".")` check with a character-level scanner that tracks `comment_depth` (`(* ... *)`), `in_string` (`"..."`), `paren_depth` (`([{`), and `match_depth` (`match`/`end`). Only treats `.` as a terminator when all depths are zero and it is followed by whitespace or EOF (distinguishing statement terminators from qualified names like `Module.foo`). Added 3 tests covering match, comment, and paren cases.

## `gen_func_residual.py`

- [x] `assert current_pattern is not None` inside `_parse_top_level_match` (line ~496) raises `AssertionError` on unexpected input. Replace with a descriptive `ValueError` so callers get a useful message.
  - **Fixed**: replaced both `assert` statements (lines 496, 511) with `raise ValueError("Malformed match: found branch body without a pattern")`.

## `synthesize.py`

- [x] `_append_missing_residual_decls_to_rel_c` uses a brittle string splice to insert new declarations before the closing `*/`, hardcoding `"\n               */"` as the expected suffix. If the actual whitespace differs, the file gets corrupted silently.
  - **Fixed**: regex now captures `(?P<closing_ws>[ \t]*)` before `*/`. Insertion point uses `match.start("closing_ws")` instead of arithmetic on `match.end()`. Per-line padding is inferred from existing body indentation rather than hardcoded.

- [x] `_format_residual_extern_decl` uses `str.strip("()")` to remove wrapping parens from the callee return type, which strips any leading/trailing mix of `(` and `)` characters individually rather than balanced pairs. Replace with a proper balanced-paren stripper (e.g. `_strip_wrapping_parens` from `gen_func_residual`).
  - **Fixed**: imported `_strip_wrapping_parens` from `gen_func_residual` and replaced `.strip("()")` with `_strip_wrapping_parens()`, which only removes parens when they form a matched pair around the entire expression.

- [x] The attempt-summary boilerplate (`_build_attempt_summary` → `_write_json` → `attempts.append` → set `previous_*` → `continue`) is duplicated ~6 times inside `run_synthesis_pipeline`. Extract into a helper to reduce repetition and make the loop easier to follow.
  - **Fixed**: extracted `_record_attempt()` (writes summary JSON, appends to attempts list, returns `(response_text, failure_kind, failure_message)` tuple for the `previous_*` state) and `_build_final_summary()` (builds the pipeline result dict with promotion and file copying). Each failure path is now a single `_record_attempt(...)` call + `continue`, and the two exit paths share `_build_final_summary()`.

## `early_return.py`

- [x] `find_first_top_level_loop` only searches for `while`/`for` keywords at brace depth 0 (`if depth == 0:`). When the loop is inside an `if/else` block (e.g. `sll_append.c`), it sits at brace depth 1 and is never found. `detect_early_return_shape` then returns `has_top_level_loop: False`, missing the `return y;` early return in the `if` branch before the loop.
  - **Fixed**: removed the `depth` variable and `{`/`}` tracking from `find_first_top_level_loop`. The scanner now finds the first `while`/`for` at any brace depth and returns immediately, so nested inner loops are not picked up. Updated test `test_find_first_top_level_loop_finds_loop_inside_if_else` to reflect the new behavior. Added `test_detect_early_return_shape_loop_inside_else_with_pre_return` covering the `sll_append.c` pattern.

## Cross-file callees

- [x] `_build_file_manifest_from_result` (`absprog/context.py`) and `collect_callee_functions` (`translate_c_file.py`) only consider functions defined in the current `.c` file. When a caller invokes a function defined in a sibling `.c` (e.g. `list_append_raw` calling `list_tail`), the manifest's `calls` graph is empty and `available_callees` never lists the helper. The LLM is then unaware of the helper's abstract program and synthesizes against an undefined name.
  - **Fixed**: added `_collect_sibling_manifest_entries(c_file, candidate_names)` to `context.py`. The manifest builder now scans each function body for `IDENT(` call sites, subtracts locally-defined names, and lazily parses only the matching sibling `.c` files via `process_and_translate_file`. Each sibling function becomes a manifest entry tagged `cross_file=True`, `should_synthesize=False`, with its full `externals.M` signature and low-level `spec`. `_select_function` filters by `cross_file` so sibling entries don't trigger multi-function disambiguation. The prompt template labels each callee as `(same-file)` or `(cross-file)` and tells the agent that cross-file callees come from `Require Import {callee}_rel_lib.` (do not redeclare).

- [x] `generate_rel_lib_for_file` (`absprog/gen_rel_lib.py`) generated rel-libs in isolation, with no awareness of cross-file callees. The output had no `Parameter list_tail_M` and no `Require Import list_tail_rel_lib`, so any reference to a sibling helper was an undefined name in Rocq.
  - **Fixed**: added `_collect_cross_file_callees(input_path, func_names, content)` which scans bodies for `IDENT(` and keeps callees whose `{callee}.c` exists as a sibling. `generate_rel_lib` accepts an `imported_rel_libs` list and emits `Require Import {callee}_rel_lib.` after the standard imports. No local `Parameter` is declared for cross-file callees — they come from the imported sibling rel-lib. Callees without a sibling `.c` are skipped entirely. Per-file Rocq checking is no longer guaranteed; directory-mode generation expects the user to run Rocq across the full set of generated libs.

## `synth_cli.py`

- [x] In parallel batch mode (`-j N`), `print` calls from different `ThreadPoolExecutor` workers interleave on stdout. Buffer each worker's output and flush atomically (e.g. collect into a string and print once per future completion).
  - **Fixed**: replaced per-line `print` calls in the `as_completed` loop with single `sys.stdout.write` / `sys.stderr.write` calls that join all lines into one string, followed by `flush()`. Each future's output is now emitted atomically.
