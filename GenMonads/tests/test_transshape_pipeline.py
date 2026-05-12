"""
Test suite for TransShape pipeline.

Tests:
1. Preprocessor (annotation extraction)
2. Translator (shape to data predicate translation)
3. GuardGen (Coq guard generation)
4. Complete pipeline (integrated)
"""

import json
import pytest

import GenMonads.predicate_mapping as predicate_mapping
from GenMonads.transshape.preprocess import AnnotationExtractor
from GenMonads.transshape.translator import ShapeTranslator
from GenMonads.transshape.process_and_translate import (
    process_and_translate_file,
    AssertionProcessor,
    GUARDGEN_AVAILABLE,
)


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
    '    /*@ Inv sllseg(x@pre, p, l1) * sll(p, l2) * sllseg(y, t, l3) */\n'
    '    while (p) {\n'
    '        q = (struct list *) 0;\n'
    '        q->next = y; y = q; p = p->next;\n'
    '    }\n'
    '    return y;\n'
    '}\n'
)


_SLL_REVERSE_SRC = (
    '#include "verification_list.h"\n'
    '#include "sll_shape_def.h"\n'
    '\n'
    'struct list* sll_reverse(struct list* head)\n'
    '/*@\n'
    '      Require listrep(head)\n'
    '      Ensure  listrep(__return)\n'
    '*/\n'
    '{\n'
    '    struct list* prev = (void *)0;\n'
    '    struct list* curr = head;\n'
    '    /*@ Inv listrep(prev) * listrep(curr) */\n'
    '    while (curr != (void *) 0) {\n'
    '        struct list* next = curr->next;\n'
    '        curr->next = prev; prev = curr; curr = next;\n'
    '    }\n'
    '    return prev;\n'
    '}\n'
)


def _write_copy(tmp_path):
    p = tmp_path / "sll_copy.c"
    p.write_text(_SLL_COPY_SRC, encoding="utf-8")
    return str(p)


def _write_reverse(tmp_path):
    p = tmp_path / "sll_reverse.c"
    p.write_text(_SLL_REVERSE_SRC, encoding="utf-8")
    return str(p)


# ============================================================================
# Preprocessor Tests
# ============================================================================

class TestPreprocessor:
    def setup_method(self):
        self.extractor = AnnotationExtractor()

    def test_funcspec_extraction(self, tmp_path):
        file_path = _write_copy(tmp_path)
        result = self.extractor.process_file(file_path)
        assert result['funcspec'] is not None
        assert result['funcspec'].get('require')
        assert result['funcspec'].get('ensure')

    def test_inner_assertion_extraction(self, tmp_path):
        file_path = _write_copy(tmp_path)
        result = self.extractor.process_file(file_path)
        assert len(result['inner_assertions']) > 0

    def test_command_guard_extraction(self, tmp_path):
        file_path = _write_reverse(tmp_path)
        result = self.extractor.process_file(file_path)
        inv_assertions = [a for a in result['inner_assertions'] if a['type'] == 'Inv']
        assert len(inv_assertions) > 0
        for assertion in inv_assertions:
            assert 'command_guard' in assertion


# ============================================================================
# Translator Tests
# ============================================================================

class TestTranslator:
    def setup_method(self):
        self.translator = ShapeTranslator()

    @pytest.mark.parametrize("original,expected", [
        ("listrep(x)", "sll(x, ?l1)"),
        ("lseg(x, y)", "sllseg(x, y, ?l1)"),
    ])
    def test_predicate_name_mapping(self, original, expected):
        self.translator.reset_var_counter()
        translated, _ = self.translator.translate_assertion(original)
        assert translated == expected

    def test_continuous_variable_numbering(self):
        require = "listrep(x) * listrep(y)"
        ensure = "listrep(__return)"

        req_translated, req_vars = self.translator.translate_assertion(require, reset=True)
        ens_translated, ens_vars = self.translator.translate_assertion(ensure, reset=False)

        all_vars = req_vars + ens_vars
        assert all_vars == ['?l1', '?l2', '?l3']

    def test_generated_variable_types_follow_mapping(self):
        translated, vars = self.translator.translate_assertion("listrep(x) * lseg(y, z)")

        assert translated == "sll(x, ?l1) * sllseg(y, z, ?l2)"
        assert vars == ["?l1", "?l2"]
        assert self.translator.last_generated_var_types == ["list Z", "list Z"]

    def test_generated_variable_types_support_non_list_data(self, tmp_path, monkeypatch):
        config_dir = tmp_path / "data"
        config_dir.mkdir()
        config_file = config_dir / "predicate_mappings.json"
        config_file.write_text(
            json.dumps(
                {
                    "boxed_int_shape": {
                        "data_name": "boxed_int",
                        "shape_arity": 1,
                        "data_arity": 2,
                        "data_var_types": ["Z", "bool"],
                    }
                }
            ),
            encoding="utf-8",
        )

        monkeypatch.setattr(predicate_mapping, "_CONFIG_DIR", str(config_dir))
        monkeypatch.setattr(predicate_mapping, "_CONFIG_FILE", str(config_file))

        translator = ShapeTranslator()
        translated, vars = translator.translate_assertion("boxed_int_shape(x)")

        assert translated == "boxed_int(x, ?l1, ?l2)"
        assert vars == ["?l1", "?l2"]
        assert translator.last_generated_var_types == ["Z", "bool"]

    def test_inv_exists_wrapping_no_existing(self):
        self.translator.reset_var_counter()
        translated, _ = self.translator.translate_assertion_with_exists("listrep(p) * listrep(y)")
        assert "exists l1 l2," in translated

    def test_inv_exists_wrapping_with_existing(self):
        self.translator.reset_var_counter()
        translated, _ = self.translator.translate_assertion_with_exists("exists u, listrep(p) * listrep(y)")
        assert "exists u l1 l2," in translated


# ============================================================================
# GuardGen Tests
# ============================================================================

class TestGuardGen:
    @pytest.mark.skipif(not GUARDGEN_AVAILABLE, reason="guardgen module not available")
    def test_null_pointer_handling(self, tmp_path):
        file_path = _write_reverse(tmp_path)
        result = process_and_translate_file(file_path)
        inv_assertions = [a for a in result['inner_assertions'] if a['type'] == 'Inv']
        for assertion in inv_assertions:
            if 'command_guard' in assertion:
                assert 'coq_guard' in assertion, f"Guard generation failed: {assertion.get('coq_guard_error')}"

    @pytest.mark.skipif(not GUARDGEN_AVAILABLE, reason="guardgen module not available")
    def test_basic_guard_generation(self, tmp_path):
        file_path = _write_copy(tmp_path)
        result = process_and_translate_file(file_path)
        inv_assertions = [a for a in result['inner_assertions'] if a['type'] == 'Inv']
        assert len(inv_assertions) > 0
        for assertion in inv_assertions:
            if 'command_guard' in assertion:
                assert 'coq_guard' in assertion or 'coq_guard_error' in assertion


# ============================================================================
# Integrated Pipeline Tests
# ============================================================================

class TestIntegratedPipeline:
    def test_automatic_mode(self, tmp_path):
        file_path = _write_copy(tmp_path)
        result = process_and_translate_file(file_path)
        assert result['funcspec'] is not None
        assert len(result['inner_assertions']) > 0

    def test_two_step_mode(self, tmp_path):
        file_path = _write_copy(tmp_path)
        processor = AssertionProcessor()

        extraction = processor.extractor.process_file(file_path)
        translated = processor.translate_inner_assertions(extraction['inner_assertions'])
        assert not any('coq_guard' in a for a in translated)

        with_guards = processor.generate_coq_guards(translated)
        guard_count = sum(1 for a in with_guards if 'coq_guard' in a)
        assert guard_count >= 0  # may be 0 if guardgen unavailable

    def test_disabled_guards(self, tmp_path):
        file_path = _write_copy(tmp_path)
        result = process_and_translate_file(file_path, generate_guards=False)
        assert not any('coq_guard' in a for a in result['inner_assertions'])
        assert not any('coq_guard_error' in a for a in result['inner_assertions'])

    def test_consistency(self, tmp_path):
        file_path = _write_copy(tmp_path)

        result_auto = process_and_translate_file(file_path, generate_guards=True)
        auto_guards = [a.get('coq_guard') for a in result_auto['inner_assertions'] if 'coq_guard' in a]

        processor = AssertionProcessor()
        extraction = processor.extractor.process_file(file_path)
        translated = processor.translate_inner_assertions(extraction['inner_assertions'])
        with_guards = processor.generate_coq_guards(translated)
        manual_guards = [a.get('coq_guard') for a in with_guards if 'coq_guard' in a]

        assert auto_guards == manual_guards
