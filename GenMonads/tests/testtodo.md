# Test Coverage Checklist

## test_transshape_pipeline.py (existing)

### Preprocessor
- [x] `test_funcspec_extraction` — extract Require/Ensure from sll_copy.c
- [x] `test_inner_assertion_extraction` — extract Inv assertions from sll_copy.c
- [x] `test_command_guard_extraction` — extract while condition after Inv

### Translator
- [x] `test_predicate_name_mapping` — listrep->sll, lseg->sllseg
- [x] `test_continuous_variable_numbering` — ?l1,?l2 across Require/Ensure
- [x] `test_inv_exists_wrapping_no_existing` — Inv gets `exists l1 l2,`
- [x] `test_inv_exists_wrapping_with_existing` — merges with existing `exists u,`

### GuardGen
- [x] `test_null_pointer_handling` — guard generated for null checks
- [x] `test_basic_guard_generation` — guard generated for sll_copy

### Integrated Pipeline
- [x] `test_automatic_mode` — process_and_translate_file end-to-end
- [x] `test_two_step_mode` — extract then translate separately
- [x] `test_disabled_guards` — generate_guards=False
- [x] `test_consistency` — auto mode == manual mode

## test_addabstract.py (existing)

### Loop Invariant safeExec
- [x] `test_basic_safeexec` — safeExec wrapping with exists
- [x] `test_no_exists` — safeExec without exists clause
- [x] `test_no_variables` — safeExec with empty variable list
- [x] `test_custom_pre_post` — custom PRE/POST instead of ATrue/X
- [x] `test_question_mark_vars_stripped` — ?l1 stripped to l1 in bind args
- [x] `test_assertion_dict_integration` — add_safeexec_to_assertion helper

### Function Spec safeExec
- [x] `test_add_with_parameter_no_existing` — adds X to empty With
- [x] `test_add_with_parameter_existing` — appends X to existing With
- [x] `test_add_safeexec_to_require_basic` — safeExec prefix on Require
- [x] `test_add_safeexec_to_require_multiple_vars` — multiple vars in Require
- [x] `test_add_safeexec_to_ensure_basic` — safeExec prefix on Ensure
- [x] `test_add_safeexec_to_ensure_single_var` — single var in Ensure
- [x] `test_process_funcspec_complete` — full funcspec with With+Require+Ensure
- [x] `test_funcspec_with_existing_with` — funcspec with pre-existing With clause

### Integration with Real Files
- [x] `test_sll_copy` — safeExec on sll_copy.c invariants
- [x] `test_sll_append` — safeExec on sll_append.c invariants
- [x] `test_all_sll_files` — safeExec on all sll/*.c files
- [x] `test_real_file_funcspec` — funcspec processing on sll_copy.c

## test_translate_c_file.py (existing)

### Single File Translation
- [x] `test_sll_copy` — translate sll_copy.c, check safeExec in output
- [x] `test_sll_append` — translate sll_append.c, check program names

### Directory Translation
- [x] `test_sll_directory` — translate all sll/*.c
- [x] `test_dll_directory` — translate all dll/*.c

### Output Verification
- [x] `test_sll_copy_output_contents` — check predicates, exists, safeExec in output
- [x] `test_compare_original_and_translated` — shape predicates replaced with data predicates

## test_header_mapping.py (existing)
- [x] `test_default_mappings` — sll_shape_def.h -> sll_def.h
- [x] `test_add_mapping` — add custom mapping
- [x] `test_remove_mapping` — remove mapping
- [x] `test_clear_mappings` — clear all
- [x] `test_reset_mappings` — reset to defaults
- [x] `test_translate_headers_quoted` — #include "..." translation
- [x] `test_translate_headers_angle` — #include <...> translation
- [x] `test_translate_headers_mixed` — mixed includes
- [x] `test_translate_with_custom_mapping` — custom mapping dict

## test_multifunction.py (new)

### Multi-Function Preprocess
- [x] `test_multi_func_extraction` — process_file returns functions list with func1, func2
- [x] `test_multi_func_specs` — each function has correct Require/Ensure
- [x] `test_multi_func_inner_assertions` — func1 has 1 Inv, func2 has 2 Invs
- [x] `test_multi_func_command_guards` — each Inv has correct while condition
- [x] `test_keyword_filtering` — while/if/for not detected as functions
- [x] `test_parse_spec_content` — unit test for extracted helper
- [x] `test_parse_spec_content_with_clause` — unit test with With clause
- [x] `test_process_func_body` — unit test for extracted helper
- [x] `test_spec_before_function` — annotation before function header

### Translator Prefix Variables
- [x] `test_prefix_variable_naming` — reset_var_counter(prefix="1") produces ?l1_1
- [x] `test_prefix_multiple_vars` — prefix="2" produces ?l2_1, ?l2_2
- [x] `test_no_prefix_backward_compat` — no prefix gives ?l1, ?l2
- [x] `test_translate_assertion_with_prefix` — prefixed vars in translated output
- [x] `test_translate_with_exists_prefix` — exists l1_1 l1_2, ...

### Process & Translate Multi-Function
- [x] `test_single_inv_no_prefix` — single loop uses l1, l2 (no prefix)
- [x] `test_multiple_inv_uses_prefix` — multiple loops use l1_1, l2_1
- [x] `test_process_file_returns_functions` — result has functions key
- [x] `test_multi_func_funcspec_translated` — each function's funcspec is translated

### End-to-End Multi-Function
- [x] `test_multi_func_translate` — translate multi-func file, check program names
- [x] `test_multi_func_funcspec_replacement` — safeExec in each function's spec
- [x] `test_multi_func_inv_replacement` — prefixed exists + safeExec in each Inv
- [x] `test_replace_funcspec_before_pattern` — /*@ ... */ before func(...) pattern
- [x] `test_replace_inner_assertions_for_func` — only target function's Invs replaced
- [ ] Need fixture files for more complex structures
- [ ] `sll_two_loops.c` — one function with two loops, for prefix-variable coverage
- [ ] `sll_three_funcs.c` — one file with three annotated functions
- [ ] `mixed_sll_dll.c` — one file mixing SLL and DLL predicates
- [ ] Re-add explicit tests for those cases after fixture files are added

## test_parser.py (new)

### Parse
- [x] `test_parse_simple_predicate` — listrep(x) -> Predicate
- [x] `test_parse_predicate_multiple_args` — lseg(x, y) -> Predicate with 2 args
- [x] `test_parse_sep_conj` — listrep(x) * lseg(y, z) -> SepConj
- [x] `test_parse_and_conj` — t != 0 && listrep(x) -> AndConj
- [x] `test_parse_exists` — exists u, listrep(x) -> Exists
- [x] `test_parse_exists_with_body` — exists u, listrep(u) * listrep(v) -> Exists with SepConj body
- [x] `test_parse_field_access` — t -> next == 0 -> BinOp with FieldAccess
- [x] `test_parse_at_pre` — lseg(x@pre, p) handles @pre
- [x] `test_parse_emp` — emp -> Predicate("emp", [])
- [x] `test_parse_number_arg` — t != 0 -> BinOp with int right
- [x] `test_parse_complex` — complex mixed assertion

### Recover
- [x] `test_recover_predicate` — Predicate -> "name(args)"
- [x] `test_recover_emp` — emp -> "emp"
- [x] `test_recover_exists` — Exists -> "exists vars, body"
- [x] `test_recover_sep_conj` — SepConj -> "a * b"
- [x] `test_recover_roundtrip` — recover(parse(s)) preserves structure (6 parametrized cases)
