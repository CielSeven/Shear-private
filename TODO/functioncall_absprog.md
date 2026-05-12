# Residual Program Generation: Current Implementation

This document records the current implemented behavior for generating residual programs after abstract callee calls. It describes the code that exists now, not a future design.

## Goal

Given:

1. a synthesized Rocq `_rel_lib.v` file that already contains complete abstract-program definitions
2. a callee abstract program name such as `sll_merge_M`
3. a caller abstract program name such as `sll_multi_merge_M`

the residual generator computes, for each call site to the callee reachable from the caller, a Rocq definition:

```coq
Definition residual_prog_in_{caller_component}_call_{n} ...
```

Each residual program represents "the rest of the caller abstract program after this callee call returns".

## Main Implementation

File:

- `/Users/cielseven/Projects/LLM4PV/GenMonads/absprog/gen_func_residual.py`

Main APIs:

- `generate_func_residual_entries(coqfilepath, callee_M, caller_component)`
- `generate_func_residual_segments(coqfilepath, callee_M, caller_component)`
- `polish_residual_segment(entry)`
- `promote_captured_identifiers_to_arguments(definition, captured_identifiers, captured_identifier_types=None)`
- `append_func_residual_definitions(coqfilepath, callee_M, caller_component, polish=True)`

CLI:

- `uv run llm4pv-residual --FILE=... --CALLEE=... --CALLER=...`

## Residual Naming Rule

Residual definitions are named by the caller component in which the call is discovered:

```text
residual_prog_in_{caller_component}_call_{n}
```

Examples:

- `residual_prog_in_sll_multi_merge_M_call_1`
- `residual_prog_in_sll_multi_merge_M_call_2`

The order `call_1`, `call_2`, ... follows structural traversal order.

## Traversal Order

The current ordering rule is structural:

- for `m1 ;; m2`, every callee point in `m1` is ordered before every callee point in `m2`
- for `x <- m1 ;; m2`, every callee point in `m1` is ordered before every callee point in `m2`
- for `choice branch1 branch2`, branch 1 is traversed before branch 2
- for `match ... with ...`, branches are traversed in textual order

This means numbering follows abstract-program execution structure, not file-position sorting.

## Supported Structural Cases

The residual finder works by traversing the caller definition and composing continuations.

### 1. Bind

For:

```coq
x <- m1;;
m2
```

or:

```coq
x <- m1;;
m2 x
```

the finder:

- searches inside `m1`
- if a callee point is found in `m1`, its residual is composed with `fun x => m2`
- then searches inside `m2`

This is the core rule.

### 2. Match

For:

```coq
match e with
| p1 => b1
| p2 => b2
end
```

the finder descends into each branch body separately. The `match` itself does not add a new continuation layer.

### 3. Choice

For:

```coq
choice b1 b2
```

the finder descends into `b1` and `b2` in order. The `choice` itself does not add a new continuation layer.

### 4. Repeat Break

For:

```coq
repeat_break body s
```

the finder descends into `body s` and composes the residual with:

```coq
fun step =>
  match step with
  | by_continue a' => repeat_break body a'
  | by_break b => ret b
  end
```

This is how loop residuals are propagated.

### 5. Named Definition Unfolding

If the traversal reaches a named definition application such as:

```coq
f x
```

and the file contains:

```coq
Definition f := fun a => k
```

then the traversal unfolds by application:

```text
f x  ==>  k[x/a]
```

If the definition uses a pattern binder, unfolding is represented with `let`:

```text
fun PATTERN => k   applied to x   ==>   let PATTERN := x in k
```

This is important for cases like:

```coq
sll_multi_merge_M_loop_aux s
```

which first unfolds to:

```coq
repeat_break sll_multi_merge_M_loop_body s
```

and then continues into:

```coq
sll_multi_merge_M_loop_body s
```

with proper substitution of `s` into the body.

### 6. Let

The traversal also descends through:

```coq
let p := e in k
```

before later bind-style processing.

## Hygienic Binder Handling

Residual composition uses hygienic binder renaming.

Why this is needed:

- inner and outer continuations may both use names like `r`, `a'`, `s'`
- naive substitution can capture binders incorrectly
- naive substitution can also replace names inside nested match-pattern binders incorrectly

Current implementation:

- generates fresh binder names when conflicts are detected
- performs scope-aware substitution
- respects binders introduced by:
  - `fun ... =>`
  - `x <- ... ;;`
  - `let ... := ... in`
  - `match ... with | pattern => ... end`

This is required for examples such as:

```coq
a' <- return (ReturnNow (l4 ++ r));;
match step with
| by_continue a' => ...
| by_break b => ...
end
```

where the two `a'` names are not the same binder.

## Captured Identifiers

Each generated residual records captured identifiers: names that are used in the residual body but are not introduced locally by the residual lambda or its internal binders.

Examples from `sll_multi_merge`:

- `l4`
- `y0`

These come from the pre-program context around the original callee call.

## Captured Identifier Type Inference

The implementation also records type information for captured identifiers when it can infer them structurally.

This is done from:

- origin definition signatures
- tuple and pattern unpacking in `fun` and `let`
- `match` branch patterns
- known result types of definitions across binds

Example:

If the origin definition has:

```coq
Definition sll_multi_merge_M_loop_M2
  : (list Z * list Z * list Z * list Z)
    -> MONAD (...)
```

and its body starts with:

```coq
fun '(l1, l2, l3, l4) =>
```

then we infer:

- `l1 : list Z`
- `l2 : list Z`
- `l3 : list Z`
- `l4 : list Z`

If later we have:

```coq
match l1 with
| nil => ...
| y0 :: y' => ...
end
```

then we further infer:

- `y0 : Z`
- `y' : list Z`

So the captured identifiers for one residual may become:

```text
captured_identifiers = ['l4', 'y0']
captured_identifier_types = {'l4': 'list Z', 'y0': 'Z'}
```

## Residual Definition Headers

Captured identifiers are promoted into explicit definition arguments.

If a type is known, it is emitted in the header:

```coq
Definition residual_prog_in_sll_multi_merge_M_call_4 (l4 : list Z) (y0 : Z)
  : list Z -> MONAD (list Z) :=
```

The result type is:

```text
callee_return_type -> MONAD (caller_return_type)
```

So:

- captured identifiers become leading definition arguments
- the callee return type becomes the argument type of the residual function
- the caller return type becomes the `MONAD (...)` result

## Polishing

Residual generation is still copy-first, then polished.

Current polishing rules:

1. simplify `x <- return a ;; k` into `k[a/x]`
2. preserve correct parentheses for substituted constructor arguments, for example:
   - `break (Continue (l4 ++ r))`
   - `break (ReturnNow r')`

Important current behavior:

- the old rule eliminating `fun _ => ...` has been removed
- polishing is optional in the CLI and append API

## CLI

Command:

```bash
uv run llm4pv-residual \
  --FILE=output/gen/libs/sll_multi_merge_rel_lib.v \
  --CALLEE=sll_merge_M \
  --CALLER=sll_multi_merge_M
```

Flags:

- `--POLISH`
- `--NO-POLISH`

Default:

- polishing is enabled unless `--NO-POLISH` is passed

Behavior:

- compute residual definitions
- optionally polish them
- promote captured identifiers into typed arguments
- append the definitions to the end of the target `.v` file

CLI output is only:

```text
Appended N residual definition(s) to <file>
```

## Integration Into `llm4pv-synth`

Residual generation is no longer only a manual debug tool.

After successful synthesis, `llm4pv-synth` now performs a post-synthesis residual sync:

1. analyze the accepted synthesized `_rel_lib.v`
2. generate residual entries from the caller/callee relationships recorded in synthesis context
3. append residual definitions to the synthesized `_rel_lib.v`
4. derive residual signatures from those same entries
5. patch the canonical `_rel.c` `Extern Coq` block with the residual signatures

This logic lives in:

- `/Users/cielseven/Projects/LLM4PV/GenMonads/absprog/synthesize.py`

So the intended workflow is now:

1. `llm4pv` generates base `_rel.c`
2. `llm4pv-rellib` generates raw `_rel_lib.v`
3. `llm4pv-synth` synthesizes abstract code segments
4. `llm4pv-synth` immediately syncs residual definitions and residual signatures

## Residual Signatures in `_rel.c`

Residual signatures are derived from the residual definition type and appended to the `Extern Coq` block of the corresponding `_rel.c` file.

Example:

```coq
Definition residual_prog_in_sll_multi_merge_M_call_2 (l4 : list Z)
  : list Z -> MONAD (list Z) :=
```

becomes in `_rel.c`:

```c
/*@ Extern Coq (residual_prog_in_sll_multi_merge_M_call_2: list Z -> list Z -> program unit (list Z)) */
```

The order is:

1. captured argument types
2. callee return type
3. `program unit (caller_return_type)`

## Patching `_rel.c` (opt-in)

By default, `llm4pv-synth` does not modify any `_rel.c` file. The rel-lib is
synthesized, residual definitions are appended to the rel-lib, and nothing else.

To patch the corresponding `_rel.c`, pass both flags:

```bash
uv run llm4pv-synth input.c output/ \
  --patch-rel-c \
  --rel-c-path path/to/input_rel.c
```

The two flags are mutually required: `--patch-rel-c` without `--rel-c-path` (or
vice versa) is an error. Directory (batch) mode does not support `--patch-rel-c`.

When enabled, the rel-c patch step performs two rewrites on the file at
`--rel-c-path`:

1. **MretTy elimination.** It reads the concrete `Definition MretTy : Type := T.`
   from the synthesized rel-lib, removes the line
   `/*@ Extern Coq (MretTy :: *) */`, and rewrites every remaining `MretTy`
   token to the concrete type (parenthesized if it is not a bare identifier).
   For example, given `Definition MretTy : Type := list Z.`, the declaration
   `(demo_M_loop_end: MretTy -> program unit (list Z))` becomes
   `(demo_M_loop_end: (list Z) -> program unit (list Z))`.

2. **Residual signature append.** Any generated
   `residual_prog_in_{caller}_call_{n}` definitions get a matching
   `/*@ Extern Coq (... : ...) */` entry appended into the existing
   `Extern Coq` block. Duplicate entries are skipped, so re-running is safe.

## Example: `sll_multi_merge`

Current generated residual definitions in the synthesized rel-lib include:

```coq
Definition residual_prog_in_sll_multi_merge_M_call_1
  : list Z -> MONAD (list Z) := ...

Definition residual_prog_in_sll_multi_merge_M_call_2 (l4 : list Z)
  : list Z -> MONAD (list Z) := ...

Definition residual_prog_in_sll_multi_merge_M_call_3 (l4 : list Z)
  : list Z -> MONAD (list Z) := ...

Definition residual_prog_in_sll_multi_merge_M_call_4 (l4 : list Z) (y0 : Z)
  : list Z -> MONAD (list Z) := ...
```

and the corresponding patched `_rel.c` declarations include:

```c
/*@ Extern Coq (residual_prog_in_sll_multi_merge_M_call_1: list Z -> program unit (list Z)) */
/*@ Extern Coq (residual_prog_in_sll_multi_merge_M_call_2: list Z -> list Z -> program unit (list Z)) */
/*@ Extern Coq (residual_prog_in_sll_multi_merge_M_call_3: list Z -> list Z -> program unit (list Z)) */
/*@ Extern Coq (residual_prog_in_sll_multi_merge_M_call_4: list Z -> Z -> list Z -> program unit (list Z)) */
```

## Current Scope

This is a structural Rocq-level residual generator over synthesized abstract programs.

It is currently intended for the abstract-program shapes already produced by this project, especially:

- bind-based sequencing
- `match`
- `choice`
- `repeat_break`
- named definition unfolding inside generated rel-lib files

It is not a general whole-program interprocedural analyzer for arbitrary C or arbitrary Rocq code.

## Issues

- [x] **Tail-position callee call produces `None` body**: When the callee is in tail position (no continuation after it), the residual body is the literal string `"None"`, which is not valid Coq. See `_build_residual_segment` when `cont is None` (`gen_func_residual.py:1092`).

  **Plan**: In `_build_residual_segment`, when `cont is None`, emit `fun r => return r` (identity continuation) instead of `fun _ => None`. Change the `binder` to a fresh name (e.g. `r`) and `body` to `return r`. Update the existing test `test_generate_func_residual_segments_for_call_in_tail_has_no_residual` to assert the new valid Coq output instead of checking for `"None"`.

- [ ] **`append_func_residual_definitions` is not idempotent**: Running the CLI or API twice on the same file appends duplicate residual definitions. No check for existing definitions before appending.

  **Plan**: Before appending, scan the file text for existing `Definition residual_prog_in_{caller_component}_call_` blocks using `_DEF_RE`. Strip all matching blocks (from `Definition` to the next `Definition` or EOF). Then append the freshly generated ones. This makes re-runs replace rather than duplicate. Add a test that calls `append_func_residual_definitions` twice and asserts only one copy of each definition exists.

- [x] **Tuple-destructuring bind patterns not supported**: `_split_top_level_bind` (`gen_func_residual.py:854`) rejects any binder that is not a simple identifier (e.g., `'(x, y) <- m ;; k`).

  **Plan**: Extend `_split_top_level_bind` to accept tuple patterns. After finding `<-` and `;;`, if the binder text is not a simple identifier, check if it matches a tuple pattern (starts with `'(` or `(`). Return it as-is and let `_collect_residuals` handle the bind case by treating a tuple binder like a `let` decomposition: `v <- m ;; let '(x,y) := v in k`. Propagate types via `_bind_pattern_types`. Add a test with `'(x, y) <- callee_M a ;; k x y`.

- [ ] **`_render_polished_residual_definition` is a dead wrapper**: (`gen_func_residual.py:1120`) just delegates to `_render_residual_definition`.

  **Plan**: Inline the call — replace all uses of `_render_polished_residual_definition` (only in `polish_residual_segment`) with `_render_residual_definition` directly, then delete the wrapper function.

- [x] **`_strip_leading_fun` in `_collect_residuals` discards all `fun` layers without recording binders**: At `gen_func_residual.py:1211`, type info for inner parameters is lost.

  **Plan**: Replace the `_strip_leading_fun` call in `_collect_residuals` with a loop that uses `_parse_leading_fun` repeatedly. For each peeled `fun binder => body` layer, bind the binder into `type_env` using the definition's signature (via `_split_top_level_arrow_type` on the current block's signature, consuming one arg type per layer). This mirrors what `_infer_initial_type_environment` does but works for direct traversal entry points. Add a test where a curried `fun a b =>` body contains a callee, and assert the captured identifier types are inferred.

- [x] **`_parse_parameter_signatures` only matches single-line Parameter declarations**: The regex (`gen_func_residual.py:137`) requires everything on one line.

  **Plan**: Change the regex to first join continuation lines (lines starting with whitespace after a `Parameter` line) before matching. Alternatively, pre-process the file text to collapse multi-line Parameter declarations onto single lines before the regex runs. Add a test with a two-line `Parameter` declaration and assert its signature is parsed.

- [x] **`_collect_locally_bound_identifiers` uses a fragile regex for match patterns**: The regex `\|\s*(.*?)=>` (`gen_func_residual.py:994`) is non-greedy and single-line.

  **Plan**: Replace the regex-based match-pattern scan with a call to `_parse_top_level_match` (which already handles nesting correctly). Collect all patterns from the parsed branches and pass them through `_collect_pattern_bound_identifiers`. This reuses the robust structural parser instead of a fragile regex. Add a test with a multi-line match pattern and verify the bound identifiers are correct.

- [ ] **Type environment not propagated through `choice` branches**: (`gen_func_residual.py:1361`) type env is unchanged through choice.

  **Plan**: This is low-impact because `choice` branches don't introduce new bindings — the issue is only about the *result type* of the choice for an outer bind. The fix belongs in `_infer_application_result_type`: add a `choice` case that infers the result type as the type of either branch (they should agree). This allows an outer `x <- choice(...) ;; k` to give `x` a type. Add a test where a callee is inside a choice that's bound to a variable, and assert the variable's type propagates.

- [ ] **Only one callee supported per invocation**: The API takes a single `callee_M`. Multiple callees require multiple runs.

  **Plan**: Add a `--CALLEE` repeat option to the CLI (accept comma-separated or multiple `--CALLEE` flags). In the API, add `append_func_residual_definitions_multi(coqfilepath, callees, caller)` that loops over callees, accumulates all entries with a shared `position_ref` counter, then appends them all at once. The single-callee API remains unchanged for backward compatibility. Document the limitation in this file's "Current Scope" section until the multi-callee API is implemented.

- [ ] **Document does not describe behavior for recursive callers**: The `seen_defs` guard (`gen_func_residual.py:1426`) silently skips recursive call sites.

  **Plan**: Add a "Limitations" subsection to this document describing: (1) recursive definitions are unfolded at most once per traversal path via `seen_defs`, (2) callee calls reachable only through a second recursive unfolding are not discovered, (3) this is correct for the current pipeline because generated `_rel_lib.v` definitions are non-recursive (loops use `repeat_break`, not recursion). No code change needed — documentation only.
