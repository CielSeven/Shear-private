"""
Test suite for addabstract module.

Tests the safeExec predicate addition to translated assertions:
- Loop invariants (Inv)
- Function specifications (Require/Ensure with With clause)
"""

import pytest

from GenMonads.addabstract import (
    add_safeexec_predicate,
    add_safeexec_to_assertion,
    add_with_parameter,
    add_safeexec_to_require,
    add_safeexec_to_ensure,
    process_funcspec_with_safeexec,
)
from GenMonads.transshape.process_and_translate import process_and_translate_file


_SLL_COPY_SRC = (
    '#include "verification_list.h"\n'
    '#include "sll_shape_def.h"\n'
    '\n'
    'struct list *sll_copy(struct list *x)\n'
    '/*@ Require listrep(x)\n'
    '    Ensure  listrep(x) * listrep(__return)\n'
    ' */\n'
    '{\n'
    '    struct list *p, *q, *t, *y;\n'
    '    p = x; y = (struct list *) 0; t = (struct list *) 0;\n'
    '    /*@ Inv lseg(x@pre, p) * listrep(p) * lseg(y, t) */\n'
    '    while (p != 0) {\n'
    '        q = (struct list *) 0;\n'
    '        q->next = y; y = q; p = p->next;\n'
    '    }\n'
    '    return y;\n'
    '}\n'
)


_SLL_APPEND_SRC = (
    '#include "verification_list.h"\n'
    '#include "sll_shape_def.h"\n'
    '\n'
    'struct list *sll_append(struct list *x, struct list *y)\n'
    '/*@ Require listrep(x) * listrep(y)\n'
    '    Ensure  listrep(__return)\n'
    ' */\n'
    '{\n'
    '    struct list *t, *u;\n'
    '    if (x == 0) { return y; }\n'
    '    t = x; u = t->next;\n'
    '    /*@ Inv lseg(x@pre, t) * listrep(u) * listrep(y) */\n'
    '    while (u) { t = u; u = t->next; }\n'
    '    t->next = y;\n'
    '    return x;\n'
    '}\n'
)


def _write_sll_copy(tmp_path):
    p = tmp_path / "sll_copy.c"
    p.write_text(_SLL_COPY_SRC, encoding="utf-8")
    return str(p)


def _write_sll_append(tmp_path):
    p = tmp_path / "sll_append.c"
    p.write_text(_SLL_APPEND_SRC, encoding="utf-8")
    return str(p)


# ============================================================================
# Loop Invariant Tests
# ============================================================================

class TestLoopInvariantSafeExec:
    def test_basic_safeexec(self):
        translated_inv = "exists l1 l2 l3, t != 0 && t -> next == 0 && t -> data == 0 && sllseg(x@pre,p, l1) * sll(p, l2) * sllseg(y, t, l3)"
        result = add_safeexec_predicate(
            translated_inv, ['l1', 'l2', 'l3'],
            "sll_copy_M_loop", "sll_copy_M_loop_end"
        )
        assert "safeExec(ATrue, bind(sll_copy_M_loop(l1,l2,l3), sll_copy_M_loop_end), X)" in result

    def test_no_exists(self):
        result = add_safeexec_predicate(
            "sll(p, l1) * sll(y, l2)", ['l1', 'l2'],
            "test_M_loop", "test_M_loop_end"
        )
        assert "safeExec(ATrue, bind(test_M_loop(l1,l2), test_M_loop_end), X)" in result
        assert not result.startswith("exists")

    def test_no_variables(self):
        result = add_safeexec_predicate(
            "exists l1, x != null && y != null", [],
            "test_M_loop", "test_M_loop_end"
        )
        assert "safeExec(ATrue, bind(test_M_loop, test_M_loop_end), X)" in result

    def test_custom_pre_post(self):
        result = add_safeexec_predicate(
            "exists l1, sll(p, l1)", ['l1'],
            "test_M_loop", "test_M_loop_end",
            "PRE", "POST"
        )
        assert "safeExec(PRE, bind(test_M_loop(l1), test_M_loop_end), POST)" in result

    def test_question_mark_vars_stripped(self):
        result = add_safeexec_predicate(
            "exists l1 l2, sll(p, l1) * sll(y, l2)", ['?l1', '?l2'],
            "test_M_loop", "test_M_loop_end"
        )
        assert "safeExec(ATrue, bind(test_M_loop(l1,l2), test_M_loop_end), X)" in result

    def test_assertion_dict_integration(self):
        assertion_dict = {
            'type': 'Inv',
            'original': 'listrep(p) * listrep(y)',
            'translated': 'exists l1 l2, sll(p, l1) * sll(y, l2)',
            'variables': ['l1', 'l2']
        }
        result = add_safeexec_to_assertion(assertion_dict, "test_M_loop", "test_M_loop_end")
        assert 'with_safeexec' in result
        assert "safeExec(ATrue, bind(test_M_loop(l1,l2), test_M_loop_end), X)" in result['with_safeexec']


# ============================================================================
# Function Specification Tests
# ============================================================================

class TestFuncSpecSafeExec:
    def test_add_with_parameter_no_existing(self):
        funcspec = {
            'with': None,
            'require': {'translated': 'sll(x, ?l1)', 'variables': ['?l1']},
            'ensure': {'translated': 'sll(__return, ?l2) * sll(x, ?l3)', 'variables': ['?l2', '?l3']}
        }
        result = add_with_parameter(funcspec, "X")
        assert result['with']['original'] is None
        assert result['with']['translated'] == 'X'

    def test_add_with_parameter_existing(self):
        funcspec = {
            'with': {'original': 'l', 'translated': 'l'},
            'require': {'translated': 'sll(x, l)', 'variables': []},
            'ensure': {'translated': 'sll(__return, ?l1) * sll(x, l)', 'variables': ['?l1']}
        }
        result = add_with_parameter(funcspec, "X")
        assert result['with']['original'] == 'l'
        assert result['with']['translated'] == 'l X'

    def test_add_safeexec_to_require_basic(self):
        result = add_safeexec_to_require("sll(x, ?l1)", ['?l1'], "sll_copy_M")
        assert result == "exists l1, safeExec(ATrue, sll_copy_M(l1), X) && sll(x, l1)"

    def test_add_safeexec_to_require_multiple_vars(self):
        result = add_safeexec_to_require("sll(x, ?l1) * sll(y, ?l2)", ['?l1', '?l2'], "sll_append_M")
        assert "exists l1 l2, safeExec(ATrue, sll_append_M(l1, l2), X)" in result

    def test_add_safeexec_to_ensure_basic(self):
        result = add_safeexec_to_ensure("sll(__return, ?l2) * sll(x, ?l3)", ['?l2', '?l3'])
        assert result == "exists l2 l3, safeExec(ATrue, return(maketuple(l2, l3)), X) && sll(__return, l2) * sll(x, l3)"

    def test_add_safeexec_to_ensure_single_var(self):
        result = add_safeexec_to_ensure("sll(__return, ?l1)", ['?l1'])
        assert "exists l1, safeExec(ATrue, return(l1), X)" in result

    def test_add_safeexec_to_ensure_no_vars_uses_return_tt(self):
        # When there are no Ensure-only variables AND the return type is
        # void (or implicitly unit), the abstract program return type is
        # `unit`, so the call must be `return(tt)` (not bare `return`).
        result = add_safeexec_to_ensure("emp", [], return_type="void")
        assert result == "safeExec(ATrue, return(tt), X) && emp"

    def test_add_safeexec_to_ensure_synthesizes_return_witness_for_non_void(self):
        # Function has non-void return type but the original Ensure has no
        # __return predicate.  We synthesize a witness `r` so the abstract
        # program return value is observable.
        result = add_safeexec_to_ensure(
            "sll(x@pre, ?l2)", ['?l2'], return_type="long"
        )
        assert result == (
            "exists l2 r, safeExec(ATrue, return(maketuple(l2, r)), X) "
            "&& __return == r && sll(x@pre, l2)"
        )

    def test_add_safeexec_to_ensure_no_witness_when_return_already_used(self):
        # Existing __return predicate ⇒ no synthetic witness needed.
        result = add_safeexec_to_ensure(
            "sll(__return, ?l2)", ['?l2'], return_type="struct list *"
        )
        assert result == (
            "exists l2, safeExec(ATrue, return(l2), X) && sll(__return, l2)"
        )

    def test_add_safeexec_to_ensure_witness_with_no_other_vars(self):
        # No predicate variables, non-void return type, no __return.
        result = add_safeexec_to_ensure("emp", [], return_type="long")
        assert result == (
            "exists r, safeExec(ATrue, return(r), X) && __return == r && emp"
        )

    def test_add_safeexec_to_ensure_pointer_return_is_not_void(self):
        # `void *` returns are not void — they still produce a value.
        result = add_safeexec_to_ensure("emp", [], return_type="void *")
        assert "return(r)" in result
        assert "__return == r" in result

    def test_add_safeexec_to_ensure_lifts_data_witness_from_ensure(self):
        # The original Ensure has ``exists d, __return -> data == d``.  Since
        # ``data`` is a configured data field and ``d`` is a pre-existing
        # existential, ``d`` is a data witness: it must be lifted into the
        # outer ``exists``, threaded into ``return(maketuple(...))``, and the
        # inner ``exists d, ...`` stripped.
        translated = (
            "exists d, __return != 0 && __return -> next == 0 && "
            "__return -> data == d && sllseg(x, __return, ?l2)"
        )
        result = add_safeexec_to_ensure(
            translated,
            ['?l2'],
            return_type="struct list *",
            data_witnesses=['d'],
        )
        assert result == (
            "exists l2 d, safeExec(ATrue, return(maketuple(l2, d)), X) "
            "&& __return != 0 && __return -> next == 0 && "
            "__return -> data == d && sllseg(x, __return, l2)"
        )

    def test_process_funcspec_complete(self):
        funcspec = {
            'with': None,
            'require': {'translated': 'sll(x, ?l1)', 'variables': ['?l1']},
            'ensure': {'translated': 'sll(__return, ?l2) * sll(x, ?l3)', 'variables': ['?l2', '?l3']}
        }
        result = process_funcspec_with_safeexec(funcspec, "sll_copy_M")
        assert result['with']['original'] is None
        assert result['with']['translated'] == 'X l1'
        assert result['require']['with_safeexec'] == 'safeExec(ATrue, sll_copy_M(l1), X) && sll(x, l1)'
        assert 'exists l2 l3, safeExec(ATrue, return(maketuple(l2, l3)), X)' in result['ensure']['with_safeexec']

    def test_funcspec_with_existing_with(self):
        funcspec = {
            'with': {'original': 'l', 'translated': 'l'},
            'require': {'translated': 'sll(x, l)', 'variables': []},
            'ensure': {'translated': 'sll(__return, ?l1) * sll(x, l)', 'variables': ['?l1']}
        }
        result = process_funcspec_with_safeexec(funcspec, "test_M")
        assert result['with']['original'] == 'l'
        assert result['with']['translated'] == 'l X'


# ============================================================================
# Integration Tests with Real Files
# ============================================================================

class TestRealFileIntegration:
    def test_sll_copy(self, tmp_path):
        file_path = _write_sll_copy(tmp_path)
        result = process_and_translate_file(file_path, generate_guards=False)
        for assertion in result['inner_assertions']:
            if assertion['type'] == 'Inv':
                with_safeexec = add_safeexec_predicate(
                    assertion['translated'], assertion['variables'],
                    f"{result['function']}_M_loop", f"{result['function']}_M_loop_end"
                )
                assert "safeExec" in with_safeexec
                assert "bind" in with_safeexec

    def test_sll_append(self, tmp_path):
        file_path = _write_sll_append(tmp_path)
        result = process_and_translate_file(file_path, generate_guards=False)
        for assertion in result['inner_assertions']:
            if assertion['type'] == 'Inv':
                with_safeexec = add_safeexec_predicate(
                    assertion['translated'], assertion['variables'],
                    f"{result['function']}_M_loop", f"{result['function']}_M_loop_end"
                )
                assert "safeExec" in with_safeexec

    def test_multiple_synthetic_files(self, tmp_path):
        for writer in (_write_sll_copy, _write_sll_append):
            file_path = writer(tmp_path)
            result = process_and_translate_file(file_path, generate_guards=False)
            for assertion in result['inner_assertions']:
                if assertion['type'] == 'Inv':
                    with_safeexec = add_safeexec_predicate(
                        assertion['translated'], assertion['variables'],
                        f"{result['function']}_M_loop", f"{result['function']}_M_loop_end"
                    )
                    assert "safeExec" in with_safeexec and "bind" in with_safeexec, \
                        f"Failed for {file_path}"

    def test_real_file_funcspec(self, tmp_path):
        file_path = _write_sll_copy(tmp_path)
        result = process_and_translate_file(file_path, generate_guards=False)
        assert result.get('funcspec') is not None

        processed = process_funcspec_with_safeexec(result['funcspec'], f"{result['function']}_M")
        assert 'safeExec' in str(processed)
