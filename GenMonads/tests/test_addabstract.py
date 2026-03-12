"""
Test suite for addabstract module.

Tests the safeExec predicate addition to translated assertions:
- Loop invariants (Inv)
- Function specifications (Require/Ensure with With clause)
"""

import os
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

BASE_DIR = os.path.dirname(os.path.dirname(os.path.dirname(__file__)))
SLL_DIR = os.path.join(BASE_DIR, 'shape_invdataset', 'sll')


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
        assert result == "safeExec(ATrue, sll_copy_M(?l1), X) && sll(x, ?l1)"

    def test_add_safeexec_to_require_multiple_vars(self):
        result = add_safeexec_to_require("sll(x, ?l1) * sll(y, ?l2)", ['?l1', '?l2'], "sll_append_M")
        assert "safeExec(ATrue, sll_append_M(?l1, ?l2), X)" in result

    def test_add_safeexec_to_ensure_basic(self):
        result = add_safeexec_to_ensure("sll(__return, ?l2) * sll(x, ?l3)", ['?l2', '?l3'])
        assert result == "safeExec(ATrue, return(?l2, ?l3), X) && sll(__return, ?l2) * sll(x, ?l3)"

    def test_add_safeexec_to_ensure_single_var(self):
        result = add_safeexec_to_ensure("sll(__return, ?l1)", ['?l1'])
        assert "safeExec(ATrue, return(?l1), X)" in result

    def test_process_funcspec_complete(self):
        funcspec = {
            'with': None,
            'require': {'translated': 'sll(x, ?l1)', 'variables': ['?l1']},
            'ensure': {'translated': 'sll(__return, ?l2) * sll(x, ?l3)', 'variables': ['?l2', '?l3']}
        }
        result = process_funcspec_with_safeexec(funcspec, "sll_copy_M")
        assert result['with']['original'] is None
        assert result['with']['translated'] == 'X'
        assert 'safeExec(ATrue, sll_copy_M(?l1), X)' in result['require']['with_safeexec']
        assert 'safeExec(ATrue, return(?l2, ?l3), X)' in result['ensure']['with_safeexec']

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
    def test_sll_copy(self):
        file_path = os.path.join(SLL_DIR, 'sll_copy.c')
        if not os.path.exists(file_path):
            pytest.skip("sll_copy.c not found")

        result = process_and_translate_file(file_path, generate_guards=False)
        for assertion in result['inner_assertions']:
            if assertion['type'] == 'Inv':
                with_safeexec = add_safeexec_predicate(
                    assertion['translated'], assertion['variables'],
                    f"{result['function']}_M_loop", f"{result['function']}_M_loop_end"
                )
                assert "safeExec" in with_safeexec
                assert "bind" in with_safeexec

    def test_sll_append(self):
        file_path = os.path.join(SLL_DIR, 'sll_append.c')
        if not os.path.exists(file_path):
            pytest.skip("sll_append.c not found")

        result = process_and_translate_file(file_path, generate_guards=False)
        for assertion in result['inner_assertions']:
            if assertion['type'] == 'Inv':
                with_safeexec = add_safeexec_predicate(
                    assertion['translated'], assertion['variables'],
                    f"{result['function']}_M_loop", f"{result['function']}_M_loop_end"
                )
                assert "safeExec" in with_safeexec

    def test_all_sll_files(self):
        if not os.path.exists(SLL_DIR):
            pytest.skip("sll directory not found")

        c_files = [f for f in os.listdir(SLL_DIR) if f.endswith('.c')]
        assert len(c_files) > 0

        for filename in sorted(c_files):
            file_path = os.path.join(SLL_DIR, filename)
            result = process_and_translate_file(file_path, generate_guards=False)
            for assertion in result['inner_assertions']:
                if assertion['type'] == 'Inv':
                    with_safeexec = add_safeexec_predicate(
                        assertion['translated'], assertion['variables'],
                        f"{result['function']}_M_loop", f"{result['function']}_M_loop_end"
                    )
                    assert "safeExec" in with_safeexec and "bind" in with_safeexec, \
                        f"Failed for {filename}"

    def test_real_file_funcspec(self):
        file_path = os.path.join(SLL_DIR, 'sll_copy.c')
        if not os.path.exists(file_path):
            pytest.skip("sll_copy.c not found")

        result = process_and_translate_file(file_path, generate_guards=False)
        assert result.get('funcspec') is not None

        processed = process_funcspec_with_safeexec(result['funcspec'], f"{result['function']}_M")
        assert 'safeExec' in str(processed)
