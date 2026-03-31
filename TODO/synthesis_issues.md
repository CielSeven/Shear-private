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

## `synth_cli.py`

- [x] In parallel batch mode (`-j N`), `print` calls from different `ThreadPoolExecutor` workers interleave on stdout. Buffer each worker's output and flush atomically (e.g. collect into a string and print once per future completion).
  - **Fixed**: replaced per-line `print` calls in the `as_completed` loop with single `sys.stdout.write` / `sys.stderr.write` calls that join all lines into one string, followed by `flush()`. Each future's output is now emitted atomically.
