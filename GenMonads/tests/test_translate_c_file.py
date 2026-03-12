"""
Test suite for C file translation.

Tests translating C files from shape_invdataset to rel files.
"""

import os
import re
import pytest

from GenMonads.translate_c_file import translate_c_file, translate_directory

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

        assert 'sll(x, ?l' in content, "Function spec should use sll predicate"
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
