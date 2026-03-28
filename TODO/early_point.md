# Early Return Point Plan

## Summary

Adjust abstract-program generation so the scaffold matches C control flow when early `return` points exist, instead of always forcing the shape:

```coq
s0 <- M_loop_before ...;;
r <- M_loop ...;;
M_loop_end r
```

Use an `early_result` wrapper only when needed:

```coq
Inductive early_result (S Ret: Type) :=
| Continue : S -> early_result S Ret
| ReturnNow : Ret -> early_result S Ret.
```

Support four template cases per function:

1. No early returns: keep the current template unchanged.
2. Early return before loop only:
   - `M_loop_before : ReqArgs -> MONAD (early_result S Ret)`
   - top-level `M` matches on `M_loop_before`
3. Early return inside loop body only:
   - `M_loop_body : S -> MONAD (CntOrBrk S (early_result MretTy Ret))`
   - `M_loop : InvArgs -> MONAD (early_result MretTy Ret)`
   - top-level `M` matches after `M_loop`
4. Early returns both before loop and inside loop:
   - combine both adjustments

Keep `M_loop_end : MretTy -> MONAD Ret` as the normal post-loop component. When loop-body early returns exist, add a concrete helper `{func}_M_after_loop : early_result MretTy Ret -> MONAD Ret` and use:

```coq
match re with
| Continue r => {func}_M_after_loop r
| ReturnNow r => return r
end
```

### Full templates for the four cases

Let:
- `ReqArgs` be the curried Require-variable argument types
- `S` be the loop carrier type from invariant variables
- `Ret` be the final function return type from Ensure
- `R` be `MretTy`, the normal loop-exit result type

#### Case 1: no early returns

No type changes are needed.

```coq
Parameter {func}_M_loop_before : ReqArgs -> MONAD S.
Parameter {func}_M_loop_M1 : S -> MONAD R.
Parameter {func}_M_loop_M2 : S -> MONAD S.
Parameter {func}_M_loop_end : R -> MONAD Ret.

Definition {func}_M_loop_body : S -> MONAD (CntOrBrk S R) :=
  fun a =>
    choice (assume!! (~ ({func}_guardP a));; r <- {func}_M_loop_M1 a ;; break r)
           (assume!! ({func}_guardP a);; a' <- {func}_M_loop_M2 a ;; continue a').

Definition {func}_M_loop_aux :=
  repeat_break {func}_M_loop_body.

Definition {func}_M_loop : InvArgs -> MONAD R :=
  fun ... => {func}_M_loop_aux (...).

Definition {func}_M : ReqArgs -> MONAD Ret :=
  fun ... =>
    s0 <- {func}_M_loop_before ...;;
    r <- {func}_M_loop_aux s0;;
    {func}_M_loop_end r.
```

#### Case 2: early return before loop only

Only `M_loop_before` changes type. The loop and post-loop parts stay normal.

```coq
Parameter {func}_M_loop_before : ReqArgs -> MONAD (early_result S Ret).
Parameter {func}_M_loop_M1 : S -> MONAD R.
Parameter {func}_M_loop_M2 : S -> MONAD S.
Parameter {func}_M_loop_end : R -> MONAD Ret.

Definition {func}_M_loop_body : S -> MONAD (CntOrBrk S R) :=
  fun a =>
    choice (assume!! (~ ({func}_guardP a));; r <- {func}_M_loop_M1 a ;; break r)
           (assume!! ({func}_guardP a);; a' <- {func}_M_loop_M2 a ;; continue a').

Definition {func}_M_loop_aux :=
  repeat_break {func}_M_loop_body.

Definition {func}_M_loop : InvArgs -> MONAD R :=
  fun ... => {func}_M_loop_aux (...).

Definition {func}_M : ReqArgs -> MONAD Ret :=
  fun ... =>
    e <- {func}_M_loop_before ...;;
    match e with
    | Continue s =>
        r <- {func}_M_loop_aux s;;
        {func}_M_loop_end r
    | ReturnNow r =>
        return r
    end.
```

#### Case 3: early return inside loop body only

The loop now returns `early_result R Ret`, and a concrete helper resumes normal post-loop handling.

```coq
Parameter {func}_M_loop_before : ReqArgs -> MONAD S.
Parameter {func}_M_loop_M1 : S -> MONAD R.
Parameter {func}_M_loop_M2 : S -> MONAD (early_result S Ret).
Parameter {func}_M_loop_end : R -> MONAD Ret.

Definition {func}_M_after_loop : early_result R Ret -> MONAD Ret :=
  fun re =>
    match re with
    | Continue r => {func}_M_loop_end r
    | ReturnNow r => return r
    end.

Definition {func}_M_loop_body : S -> MONAD (CntOrBrk S (early_result R Ret)) :=
  fun a =>
    choice (assume!! (~ ({func}_guardP a));; r <- {func}_M_loop_M1 a ;; break (Continue r))
           (assume!! ({func}_guardP a);; 
           a' <- {func}_M_loop_M2 a ;; 
           match a' with 
           | Continue a'' => continue a''
           | ReturnNow r' => break (ReturnNow r') end).

Definition {func}_M_loop_aux :=
  repeat_break {func}_M_loop_body.

Definition {func}_M_loop : InvArgs -> MONAD (early_result R Ret) :=
  fun ... => {func}_M_loop_aux (...).

Definition {func}_M : ReqArgs -> MONAD Ret :=
  fun ... =>
    s0 <- {func}_M_loop_before ...;;
    re <- {func}_M_loop_aux s0;;
    {func}_M_after_loop re.
```

The LLM-generated `M_loop_M2` may still perform an early return internally by producing a loop-body result that ultimately causes `break (ReturnNow r)` in the concrete loop scaffold.

#### Case 4: early returns both before loop and inside loop

This combines Case 2 and Case 3.

```coq
Parameter {func}_M_loop_before : ReqArgs -> MONAD (early_result S Ret).
Parameter {func}_M_loop_M1 : S -> MONAD R.
Parameter {func}_M_loop_M2 : S -> MONAD (early_result S Ret).
Parameter {func}_M_loop_end : R -> MONAD Ret.

Definition {func}_M_after_loop : early_result R Ret -> MONAD Ret :=
  fun re =>
    match re with
    | Continue r => {func}_M_loop_end r
    | ReturnNow r => return r
    end.

Definition {func}_M_loop_body : S -> MONAD (CntOrBrk S (early_result R Ret)) :=
  fun a =>
    choice (assume!! (~ ({func}_guardP a));; r <- {func}_M_loop_M1 a ;; break (Continue r))
           (assume!! ({func}_guardP a);;
           a' <- {func}_M_loop_M2 a ;;
           match a' with
           | Continue a'' => continue a''
           | ReturnNow r' => break (ReturnNow r')
           end).

Definition {func}_M_loop_aux :=
  repeat_break {func}_M_loop_body.

Definition {func}_M_loop : InvArgs -> MONAD (early_result R Ret) :=
  fun ... => {func}_M_loop_aux (...).

Definition {func}_M : ReqArgs -> MONAD Ret :=
  fun ... =>
    e <- {func}_M_loop_before ...;;
    match e with
    | Continue s =>
        re <- {func}_M_loop_aux s;;
        {func}_M_after_loop re
    | ReturnNow r =>
        return r
    end.
```

## Implementation Changes

### Control-flow detection

Add a lightweight single-loop control-flow analysis shared by translation, rel-lib generation, and synthesis context:
- locate the first top-level loop in the target function source
- classify `return` statements into:
  - `has_pre_loop_early_return`
  - `has_loop_body_early_return`
- treat returns after normal loop exit as part of ordinary post-loop synthesis, not `early_result`

The detection only needs to support the project’s current one-loop target functions and should be brace/branch aware rather than line-based.

### Signature and scaffold generation

Update the function metadata produced for loop-bearing functions so it includes:
- `has_pre_loop_early_return`
- `has_loop_body_early_return`
- `return_type`
- `state_type`
- `loop_result_type`
- `needs_early_result`

Then change rel-lib skeleton generation and C `Extern Coq` signature generation to select one of the four template cases above.

Required signature changes:
- No early returns:
  - unchanged
- Pre-loop early return:
  - `{func}_M_loop_before : ReqArgs -> MONAD (early_result S Ret)`
- Loop-body early return:
  - `{func}_M_loop_M1 : S -> MONAD R`
  - `{func}_M_loop_M2 : S -> MONAD (early_result S Ret)`
  - `{func}_M_loop_body : S -> MONAD (CntOrBrk S (early_result MretTy Ret))`
  - `{func}_M_loop : InvArgs -> MONAD (early_result MretTy Ret)`
  - add concrete `{func}_M_after_loop : early_result MretTy Ret -> MONAD Ret`
- Both:
  - combine both changes

Top-level `{func}_M` must be generated with the appropriate nested `match` structure, exactly following the detected case.

### Translation and synthesis-context alignment

Update the translated C/annotation side so the abstract-program references stay type-correct:
- Require path still references `{func}_M`
- Invariant path:
  - no loop-body early return: keep `bind({func}_M_loop(...), {func}_M_loop_end)`
  - loop-body early return: use `bind({func}_M_loop(...), {func}_M_after_loop)`

Update synthesis context and prompt generation so they expose the selected template explicitly:
- add the early-return flags to context JSON
- emit the actual chosen scaffold in the prompt, not the old unconditional scaffold
- update required signatures shown to the LLM so they match the selected case
- mention `{func}_M_after_loop` in the prompt only when loop-body early returns exist, and mark it as concrete scaffolding rather than an LLM target

Keep the LLM-generated targets unchanged in spirit:
- `MretTy`
- `{func}_M_loop_before`
- `{func}_M_loop_M1`
- `{func}_M_loop_M2`
- `{func}_M_loop_end`

Only the types and composition around them change based on early-return detection.

## Test Plan

Add focused coverage for these cases:

- No early return:
  - translated `_rel.c`, context JSON, prompt text, and `_rel_lib.v` remain unchanged
- Pre-loop early return only:
  - `{func}_M_loop_before` returns `early_result S Ret`
  - top-level `{func}_M` matches on `loop_before`
  - `{func}_M_loop` and invariant path remain normal
- Loop-body early return only:
  - `{func}_M_loop_M1` stays `S -> MONAD MretTy`
  - `{func}_M_loop_M2` becomes `S -> MONAD (early_result S Ret)`
  - `{func}_M_loop_body` returns `CntOrBrk S (early_result MretTy Ret)`
  - `{func}_M_loop` returns `early_result MretTy Ret`
  - `{func}_M_after_loop` is generated
  - invariant safeExec uses `{func}_M_after_loop`, not `{func}_M_loop_end`
- Both early-return locations:
  - both type adjustments appear together
  - top-level `{func}_M` has both matches
- Multi-function file with opaque callee:
  - helper `Parameter {callee}_M` is preserved
  - early-return-aware skeleton still assembles correctly
- Prompt/context tests:
  - selected template shown in prompt matches the detected control-flow case
  - required signatures in prompt match rel-lib signatures exactly

Use `sll_multi_merge` as the first end-to-end regression target because it has:
- early return before the loop
- early return inside the loop body
- same-file opaque callee calls

## Assumptions and Defaults

- Single-loop functions remain the only synthesis target for this change.
- Returns after normal loop exit are still modeled inside `{func}_M_loop_end`; they do not trigger `early_result`.
- `early_result` is defined once per generated `_rel_lib.v` file if any loop-bearing function in that file needs it.
- Constructor names are exactly `Continue` and `ReturnNow`.
- `{func}_M_loop_end` remains the normal post-loop component with type `MretTy -> MONAD Ret`.
- `{func}_M_after_loop` is introduced only for functions with loop-body early returns, and is concrete generated scaffolding, not an LLM-synthesized component.
