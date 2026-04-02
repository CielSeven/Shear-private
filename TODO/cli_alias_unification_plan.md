# CLI Alias Unification Plan

## Goal

Make CLI entry points behave consistently for positional arguments and alias-style flags such as `--FILE`, `--C_DIR`, and `--OUTPUT_PATH`, while fixing the reviewed error-handling and UX issues without changing the user-facing command set.

## Dependency Notes

- The `resolve_cli_value(...)` fix is a hard dependency for the output-handling unification work.
- The `add_output_path_argument(...)` refactor is preparatory work for the CLI output-handling changes.
- The `llm4pv-rellib` and `synth_cli.py` output-handling updates can be implemented in parallel once the shared helper changes are done.
- The `translate_c_file.py` exit-code fix is independent and can be done at any time.
- The `synth_cli.py` error-message cleanup and `residual_cli.py` help cleanup are low-risk polish and should come after the functional fixes.

## TODO

- [x] Lock down the shared CLI contract for path-like arguments.
  Document the intended rules:
  positional `input` may be combined with `--FILE` or `--C_DIR`;
  positional `output` may be combined with `--OUTPUT_PATH` or command-specific aliases such as `-o` and `--output-dir`;
  matching duplicates are allowed;
  conflicting duplicates should raise an error;
  path-like arguments should resolve to normalized paths.

- [x] Fix `resolve_cli_value(...)` in `GenMonads/cli_common.py`.
  Change it so that when `is_path=True`, it returns the normalized path rather than the raw original string.
  Keep the current behavior for non-path arguments.
  Add tests for equivalent paths such as `foo/../bar` and `bar`.

- [x] Refactor `add_output_path_argument(...)` in `GenMonads/cli_common.py` so it can serve as the single source of truth for output aliases.
  Add support for optional extra flags such as `-o` and `--output-dir` instead of hand-wiring those separately in individual CLIs.
  Keep the helper compatible with the existing `--OUTPUT_PATH` behavior.

- [x] Unify output handling in `GenMonads/absprog/cli.py`.
  Move `llm4pv-rellib` output parsing onto the shared helper and shared resolver path.
  Preserve support for positional output, `--OUTPUT_PATH`, `-o`, and `--output-dir`.
  Ensure duplicate matching values are accepted and conflicting values fail through the shared validation path.

- [x] Unify output handling in `GenMonads/absprog/synth_cli.py`.
  Replace the manual positional `output_dir` plus `--OUTPUT_PATH` wiring with the shared output helper.
  While doing this, split the `_resolve_io(...)` error messages so missing input and missing output produce precise, non-confusing guidance.

- [x] Fix exit-code behavior in `GenMonads/translate_c_file.py`.
  Ensure failed single-file translation exits non-zero.
  Standardize directory mode so any failed translation in batch mode also yields a non-zero exit code, matching the pattern already used in batch-style CLIs such as `synth_cli.py`.
  Bundle the `✓/✗` cleanup into this change if we want plain-text status output for consistency.

- [x] Improve help readability in `GenMonads/absprog/residual_cli.py`.
  Keep the current parsing model if it remains the simplest implementation.
  Use clearer metavar values so `--help` presents positional usage as `FILE CALLEE CALLER` rather than internal variable names such as `file_path`.

- [x] Expand tests around the reviewed behaviors.
  Add tests for:
  normalized return values from `resolve_cli_value(...)`;
  `llm4pv-rellib` with positional output, `--OUTPUT_PATH`, `-o`, and `--output-dir`;
  conflicting duplicate output arguments on `llm4pv-rellib`;
  clearer `_resolve_io(...)` error messages in `synth_cli.py`;
  non-zero exit behavior for single-file and directory-mode failures in `llm4pv`;
  any residual CLI help assertions if metavar output changes.

- [x] Run a focused CLI regression suite after the fixes.
  Verify that:
  existing positional invocation still works;
  alias-style invocation works consistently;
  conflicting duplicates fail loudly;
  normalized paths are returned where expected;
  failure exit codes are correct.

- [x] Update docs only where needed after the behavior is stable.
  Review the currently existing docs in `README.md`, `AGENTS.md`, and any relevant notes under `TODO/` or `document/`.
  Refresh examples only in the places whose documented CLI forms no longer match the implementation.
