"""
Test suite for C file translation.

Tests translating C files from shape_invdataset to rel files.
"""

import os
import re
import pytest

from GenMonads.translate_c_file import (
    translate_c_file, translate_directory,
    insert_safeexec_include, generate_coq_blocks, collect_func_extern_info,
)

BASE_DIR = os.path.dirname(os.path.dirname(os.path.dirname(__file__)))
SLL_DIR = os.path.join(BASE_DIR, 'shape_invdataset', 'sll')
DLL_DIR = os.path.join(BASE_DIR, 'shape_invdataset', 'dll')
OUTPUT_SLL_DIR = os.path.join(BASE_DIR, 'output', 'shape', 'rel', 'sll')
OUTPUT_DLL_DIR = os.path.join(BASE_DIR, 'output', 'shape', 'rel', 'dll')


# ============================================================================
# Single File Tests
# ============================================================================

class TestSingleFile:
    def test_sll_copy(self):
        input_path = os.path.join(SLL_DIR, 'sll_copy.c')
        output_path = os.path.join(OUTPUT_SLL_DIR, 'sll_copy_rel.c')
        if not os.path.exists(input_path):
            pytest.skip("sll_copy.c not found")

        assert translate_c_file(input_path, output_path)
        assert os.path.exists(output_path)

        with open(output_path, 'r') as f:
            content = f.read()

        inv_match = re.search(r'/\*@\s*Inv\s+(.*?)\s*\*/', content, re.DOTALL)
        assert inv_match is not None
        assert 'safeExec' in inv_match.group(1)

        spec_match = re.search(r'sll_copy\s*\([^)]*\)\s*/\*@(.*?)\*/', content, re.DOTALL)
        assert spec_match is not None
        assert 'sll(' in spec_match.group(1)

    def test_sll_append(self):
        input_path = os.path.join(SLL_DIR, 'sll_append.c')
        output_path = os.path.join(OUTPUT_SLL_DIR, 'sll_append_rel.c')
        if not os.path.exists(input_path):
            pytest.skip("sll_append.c not found")

        assert translate_c_file(input_path, output_path)

        with open(output_path, 'r') as f:
            content = f.read()

        assert 'safeExec' in content
        assert 'sll_append_M_loop' in content


# ============================================================================
# Directory Tests
# ============================================================================

class TestDirectory:
    def test_sll_directory(self):
        if not os.path.exists(SLL_DIR):
            pytest.skip("sll directory not found")

        results = translate_directory(SLL_DIR, OUTPUT_SLL_DIR)
        total = len(results)
        success = sum(1 for v in results.values() if v)
        assert success == total, f"{total - success} files failed: {[k for k, v in results.items() if not v]}"

    def test_dll_directory(self):
        if not os.path.exists(DLL_DIR):
            pytest.skip("dll directory not found")

        results = translate_directory(DLL_DIR, OUTPUT_DLL_DIR)
        total = len(results)
        success = sum(1 for v in results.values() if v)
        assert success == total, f"{total - success} files failed: {[k for k, v in results.items() if not v]}"


# ============================================================================
# Verification Tests
# ============================================================================

class TestOutputVerification:
    def test_sll_copy_output_contents(self):
        output_path = os.path.join(OUTPUT_SLL_DIR, 'sll_copy_rel.c')
        if not os.path.exists(output_path):
            pytest.skip("sll_copy_rel.c not found (run translation first)")

        with open(output_path, 'r') as f:
            content = f.read()

        assert 'sll(x, l' in content, "Function spec should use sll predicate with exists-quantified vars"
        assert 'safeExec(ATrue, bind(sll_copy_M_loop' in content, "safeExec with correct program"
        assert 'exists l1 l2 l3,' in content, "Exists quantifier in invariant"
        assert 'sllseg(' in content, "sllseg predicate used"

    def test_compare_original_and_translated(self):
        input_path = os.path.join(SLL_DIR, 'sll_copy.c')
        output_path = os.path.join(OUTPUT_SLL_DIR, 'sll_copy_rel.c')
        if not os.path.exists(input_path) or not os.path.exists(output_path):
            pytest.skip("Input or output file not found")

        with open(input_path, 'r') as f:
            original = f.read()
        with open(output_path, 'r') as f:
            translated = f.read()

        # Original should have shape predicates
        assert 'listrep(' in original
        # Translated should not have shape predicates in specs
        assert 'sll(' in translated
        assert 'sllseg(' in translated


# ============================================================================
# safeexec_def.h Include Tests
# ============================================================================

class TestSafeexecInclude:
    def test_inserts_after_last_include(self):
        content = '#include "a.h"\n#include "b.h"\n\nint main() {}'
        result = insert_safeexec_include(content)
        lines = result.split('\n')
        assert lines[2] == '#include "safeexec_def.h"'

    def test_idempotent(self):
        content = '#include "a.h"\n#include "safeexec_def.h"\n\nint main() {}'
        result = insert_safeexec_include(content)
        assert result == content

    def test_present_in_sll_copy_output(self):
        output_path = os.path.join(OUTPUT_SLL_DIR, 'sll_copy_rel.c')
        if not os.path.exists(output_path):
            pytest.skip("sll_copy_rel.c not found")
        with open(output_path, 'r') as f:
            content = f.read()
        assert '#include "safeexec_def.h"' in content


# ============================================================================
# Coq Block Generation Tests
# ============================================================================

class TestCoqBlocks:
    def test_generate_single_function(self):
        infos = [{'func_name': 'sll_copy', 'require_var_count': 1, 'inv_var_count': 3, 'ensure_var_count': 2}]
        result = generate_coq_blocks('sll_copy', infos)
        assert '/*@ Import Coq Require Import sll_copy_rel_lib */' in result
        assert '/*@ Extern Coq (MretTy :: *) */' in result
        assert '(sll_copy_M: list Z -> program unit (list Z * list Z))' in result
        assert '(sll_copy_M_loop: list Z -> list Z -> list Z -> program unit MretTy)' in result
        assert '(sll_copy_M_loop_end: MretTy -> program unit (list Z * list Z))' in result

    def test_generate_two_require_vars(self):
        infos = [{'func_name': 'sll_append', 'require_var_count': 2, 'inv_var_count': 3}]
        result = generate_coq_blocks('sll_append', infos)
        assert '(sll_append_M: list Z -> list Z -> program unit (list Z))' in result

    def test_generate_maketuple_when_needed(self):
        infos = [{'func_name': 'sll_copy', 'require_var_count': 1, 'inv_var_count': 3, 'ensure_var_count': 2}]
        result = generate_coq_blocks('sll_copy', infos, needs_maketuple=True)
        assert '(maketuple: {A} {B} -> A -> B -> (A * B))' in result
        assert '(sll_copy_M: list Z -> program unit (list Z * list Z))' in result

    def test_empty_func_infos(self):
        assert generate_coq_blocks('foo', []) == ''

    def test_import_coq_in_sll_copy_output(self):
        output_path = os.path.join(OUTPUT_SLL_DIR, 'sll_copy_rel.c')
        if not os.path.exists(output_path):
            pytest.skip("sll_copy_rel.c not found")
        with open(output_path, 'r') as f:
            content = f.read()
        assert '/*@ Import Coq Require Import sll_copy_rel_lib */' in content

    def test_extern_coq_in_sll_copy_output(self):
        output_path = os.path.join(OUTPUT_SLL_DIR, 'sll_copy_rel.c')
        if not os.path.exists(output_path):
            pytest.skip("sll_copy_rel.c not found")
        with open(output_path, 'r') as f:
            content = f.read()
        assert '/*@ Extern Coq (MretTy :: *) */' in content
        assert 'sll_copy_M: list Z -> program unit (list Z * list Z)' in content
        assert 'sll_copy_M_loop: list Z -> list Z -> list Z -> program unit MretTy' in content
        assert 'sll_copy_M_loop_end: MretTy -> program unit (list Z * list Z)' in content

    def test_extern_coq_in_sll_append_output(self):
        output_path = os.path.join(OUTPUT_SLL_DIR, 'sll_append_rel.c')
        if not os.path.exists(output_path):
            pytest.skip("sll_append_rel.c not found")
        with open(output_path, 'r') as f:
            content = f.read()
        assert '/*@ Import Coq Require Import sll_append_rel_lib */' in content
        assert 'sll_append_M: list Z -> list Z -> program unit (list Z)' in content


# ============================================================================
# collect_func_extern_info Tests
# ============================================================================

class TestCollectFuncExternInfo:
    def test_no_inner_assertions(self):
        func_data = {'function': 'foo', 'funcspec': None, 'inner_assertions': []}
        assert collect_func_extern_info(func_data) is None

    def test_with_inner_assertions(self):
        func_data = {
            'function': 'sll_copy',
            'funcspec': {'require': {'translated': 'sll(x, ?l1)'}, 'ensure': {'translated': 'sll(__return, ?l2)'}},
            'inner_assertions': [
                {'type': 'Inv', 'translated': 'exists l1 l2 l3, ...', 'variables': ['l1', 'l2', 'l3']}
            ]
        }
        info = collect_func_extern_info(func_data)
        assert info is not None
        assert info['func_name'] == 'sll_copy'
        assert info['require_var_count'] == 1
        assert info['inv_var_count'] == 3
