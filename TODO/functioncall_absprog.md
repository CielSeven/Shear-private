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

- [ ] **Tail-position callee call produces `None` body**: When the callee is in tail position (no continuation after it), the residual body is the literal string `"None"`, which is not valid Coq. Should emit `return` (identity continuation) or be flagged as a trivial/degenerate residual. See `_build_residual_segment` when `cont is None` (`gen_func_residual.py:1092`).

- [ ] **`append_func_residual_definitions` is not idempotent**: Running the CLI or API twice on the same file appends duplicate residual definitions. There is no check for whether residual definitions already exist before appending. Should detect and skip or replace existing residual definitions with the same name.

- [ ] **Tuple-destructuring bind patterns not supported**: `_split_top_level_bind` (`gen_func_residual.py:854`) rejects any binder that is not a simple identifier (e.g., `'(x, y) <- m ;; k` is not parsed as a bind). If a caller uses tuple-destructuring binds, the traversal will miss callee calls inside.

- [ ] **`_render_polished_residual_definition` is a dead wrapper**: This function (`gen_func_residual.py:1120`) just delegates to `_render_residual_definition` with the same arguments and adds no logic. It should either be removed or extended with actual polishing of the definition header.

- [ ] **`_strip_leading_fun` in `_collect_residuals` discards all `fun` layers without recording binders**: At `gen_func_residual.py:1211`, `_strip_leading_fun` strips every leading `fun ... =>` without propagating the binder names or their types into the type environment. This means type inference is lost for inner parameters of curried definitions when traversal enters them directly (as opposed to via named definition unfolding which handles this separately).

- [ ] **`_parse_parameter_signatures` only matches single-line Parameter declarations**: The regex at `gen_func_residual.py:137` requires the entire `Parameter ... : ... .` on one line. Multi-line Parameter declarations (which Coq allows) will not be parsed, causing missing callee return types and incorrect residual headers.

- [ ] **`_collect_locally_bound_identifiers` uses a fragile regex for match patterns**: The regex `\|\s*(.*?)=>` (`gen_func_residual.py:994`) is non-greedy and single-line. Multi-token patterns or patterns on separate lines from `=>` may not be captured correctly, leading to incorrect captured-identifier sets.

- [ ] **Type environment not propagated through `choice` branches**: When descending into `choice b1 b2` (`gen_func_residual.py:1361`), the type environment is passed through unchanged, but the result type of the choice expression is not inferred for surrounding bind contexts. This can cause missing type annotations on captured identifiers when the callee appears inside a choice branch nested within a bind.

- [ ] **Only one callee supported per invocation**: The API takes a single `callee_M` name. If a caller invokes multiple different callees, the tool must be run once per callee. The document does not mention this limitation, and the CLI provides no batch mode for multiple callees.

- [ ] **Document does not describe behavior for recursive callers**: If the caller definition is (mutually) recursive, the `seen_defs` guard (`gen_func_residual.py:1426`) prevents infinite unfolding but silently skips recursive call sites. The document should describe this behavior and its implications for residual completeness.
