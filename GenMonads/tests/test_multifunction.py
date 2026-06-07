"""
Test suite for multi-function pipeline support.

Tests:
1. Multi-function extraction from C files
2. Variable prefix naming for multiple loops
3. Per-function assertion replacement
4. End-to-end multi-function file translation
"""

import os
import re
import tempfile
import pytest

from GenMonads.transshape.preprocess import AnnotationExtractor
from GenMonads.transshape.translator import ShapeTranslator
from GenMonads.transshape.process_and_translate import (
    process_and_translate_file,
    AssertionProcessor,
)
from GenMonads.translate_c_file import (
    translate_c_file,
    replace_funcspec,
    replace_inner_assertions_for_func,
)

FIXTURES_DIR = os.path.join(os.path.dirname(__file__), 'fixtures')
MULTI_FUNC_INPUT = os.path.join(FIXTURES_DIR, 'test_complex_structure.c')
MULTI_FUNC_EXPECTED = os.path.join(FIXTURES_DIR, 'test_complex_structure_rel.c')


# Synthetic single-function sources (one Require/Ensure spec + at least one Inv).
_SINGLE_FUNC_SOURCES = {
    "sll_reverse.c": (
        '#include "verification_list.h"\n'
        '#include "sll_shape_def.h"\n'
        '\n'
        'struct list *sll_reverse(struct list *head)\n'
        '/*@ Require listrep(head)\n'
        '    Ensure  listrep(__return)\n'
        ' */\n'
        '{\n'
        '    struct list *prev = (void *) 0;\n'
        '    struct list *curr = head;\n'
        '    /*@ Inv listrep(prev) * listrep(curr) */\n'
        '    while (curr != (void *) 0) { curr = curr->next; prev = curr; }\n'
        '    return prev;\n'
        '}\n'
    ),
    "sll_free_all.c": (
        '#include "verification_list.h"\n'
        '#include "sll_shape_def.h"\n'
        '\n'
        'void sll_free_all(struct list *x)\n'
        '/*@ Require listrep(x)\n'
        '    Ensure  emp\n'
        ' */\n'
        '{\n'
        '    /*@ Inv listrep(x) */\n'
        '    while (x != (void *) 0) { x = x->next; }\n'
        '}\n'
    ),
}


# Synthetic multi-function sources (two or more annotated functions).
_MULTI_FUNC_SOURCES = {
    "two_simple_loops.c": (
        '#include "verification_list.h"\n'
        '#include "sll_shape_def.h"\n'
        '\n'
        'struct list *f1(struct list *x)\n'
        '/*@ Require listrep(x)\n'
        '    Ensure  listrep(__return)\n'
        ' */\n'
        '{\n'
        '    /*@ Inv listrep(x) */\n'
        '    while (x != 0) { x = x->next; }\n'
        '    return x;\n'
        '}\n'
        '\n'
        'struct list *f2(struct list *y)\n'
        '/*@ Require listrep(y)\n'
        '    Ensure  listrep(__return)\n'
        ' */\n'
        '{\n'
        '    /*@ Inv listrep(y) */\n'
        '    while (y != 0) { y = y->next; }\n'
        '    return y;\n'
        '}\n'
    ),
    "sll_rotate.c": (
        '#include "verification_list.h"\n'
        '#include "sll_shape_def.h"\n'
        '\n'
        'struct list *sll_rotate_left(struct list *x)\n'
        '/*@ Require listrep(x)\n'
        '    Ensure  listrep(__return)\n'
        ' */\n'
        '{\n'
        '    /*@ Inv listrep(x) */\n'
        '    while (x != 0) { x = x->next; }\n'
        '    return x;\n'
        '}\n'
        '\n'
        'struct list *sll_rotate_right(struct list *x)\n'
        '/*@ Require listrep(x)\n'
        '    Ensure  listrep(__return)\n'
        ' */\n'
        '{\n'
        '    /*@ Inv listrep(x) */\n'
        '    while (x != 0) { x = x->next; }\n'
        '    return x;\n'
        '}\n'
    ),
}

_SINGLE_FUNC_FILENAMES = sorted(_SINGLE_FUNC_SOURCES)
_MULTI_FUNC_FILENAMES = sorted(_MULTI_FUNC_SOURCES)


def _write_synthetic(tmp_path, filename, sources):
    p = tmp_path / filename
    p.write_text(sources[filename], encoding="utf-8")
    return str(p)


# ============================================================================
# Multi-Function Preprocess Tests
# ============================================================================

class TestMultiFuncPreprocess:
    def setup_method(self):
        self.extractor = AnnotationExtractor()

    def test_multi_func_extraction(self):
        if not os.path.exists(MULTI_FUNC_INPUT):
            pytest.skip("test_complex_structure.c not found")
        result = self.extractor.process_file(MULTI_FUNC_INPUT)
        funcs = [f for f in result['functions']
                 if f['function'] in ('func1', 'func2')]
        assert len(funcs) == 2
        func_names = [f['function'] for f in funcs]
        assert 'func1' in func_names
        assert 'func2' in func_names

    def test_multi_func_specs(self):
        if not os.path.exists(MULTI_FUNC_INPUT):
            pytest.skip("test_complex_structure.c not found")
        result = self.extractor.process_file(MULTI_FUNC_INPUT)
        funcs = {f['function']: f for f in result['functions']
                 if f['function'] in ('func1', 'func2')}

        # func1: Require listrep(x), Ensure listrep(__return)
        assert funcs['func1']['funcspec'] is not None
        assert 'listrep(x)' in funcs['func1']['funcspec']['require']
        assert 'listrep(__return)' in funcs['func1']['funcspec']['ensure']

        # func2: Require listrep(x) * listrep(y), Ensure listrep(__return)
        assert funcs['func2']['funcspec'] is not None
        assert 'listrep(x)' in funcs['func2']['funcspec']['require']
        assert 'listrep(y)' in funcs['func2']['funcspec']['require']

    def test_multi_func_inner_assertions(self):
        if not os.path.exists(MULTI_FUNC_INPUT):
            pytest.skip("test_complex_structure.c not found")
        result = self.extractor.process_file(MULTI_FUNC_INPUT)
        funcs = {f['function']: f for f in result['functions']
                 if f['function'] in ('func1', 'func2')}

        func1_invs = [a for a in funcs['func1']['inner_assertions'] if a['type'] == 'Inv']
        func2_invs = [a for a in funcs['func2']['inner_assertions'] if a['type'] == 'Inv']
        assert len(func1_invs) == 1
        assert len(func2_invs) == 2

    def test_multi_func_command_guards(self):
        if not os.path.exists(MULTI_FUNC_INPUT):
            pytest.skip("test_complex_structure.c not found")
        result = self.extractor.process_file(MULTI_FUNC_INPUT)
        funcs = {f['function']: f for f in result['functions']
                 if f['function'] in ('func1', 'func2')}

        func2_invs = [a for a in funcs['func2']['inner_assertions'] if a['type'] == 'Inv']
        # First loop: while (p->next)
        assert 'command_guard' in func2_invs[0]
        assert 'next' in func2_invs[0]['command_guard']
        # Second loop: while (curr)
        assert 'command_guard' in func2_invs[1]
        assert 'curr' in func2_invs[1]['command_guard']

    def test_keyword_filtering(self):
        """while, if, for should not be detected as function names."""
        text = """
void myfunc(int x) {
    while (x > 0) { x--; }
    if (x == 0) { return; }
    for (int i = 0; i < 10; i++) { }
}
"""
        # Use parse on synthetic text via process_func_body
        extractor = AnnotationExtractor()
        # We just check that process_file doesn't crash and doesn't include keywords
        with tempfile.NamedTemporaryFile(mode='w', suffix='.c', prefix='myfunc', delete=False) as f:
            f.write(text)
            f.flush()
            try:
                result = extractor.process_file(f.name)
                func_names = [fn['function'] for fn in result.get('functions', [])]
                assert 'while' not in func_names
                assert 'if' not in func_names
                assert 'for' not in func_names
            finally:
                os.unlink(f.name)

    def test_parse_spec_content(self):
        extractor = AnnotationExtractor()
        spec = extractor.parse_spec_content("Require listrep(x)\n    Ensure listrep(__return)")
        assert spec['require'] == 'listrep(x)'
        assert spec['ensure'] == 'listrep(__return)'
        assert spec['with'] is None

    def test_parse_spec_content_with_clause(self):
        extractor = AnnotationExtractor()
        spec = extractor.parse_spec_content("With l\n    Require listrep(x)\n    Ensure listrep(__return)")
        assert spec['with'] == 'l'
        assert spec['require'] == 'listrep(x)'

    def test_process_func_body(self):
        extractor = AnnotationExtractor()
        body = """
    /*@ Inv lseg(x, p) * listrep(p) */
    while (p) {
        p = p->next;
    }
"""
        assertions = extractor.process_func_body(body, 0)
        assert len(assertions) == 1
        assert assertions[0]['type'] == 'Inv'
        assert 'lseg(x, p)' in assertions[0]['content']

    def test_spec_before_function(self):
        """Annotation appearing before function header should be assigned to it."""
        if not os.path.exists(MULTI_FUNC_INPUT):
            pytest.skip("test_complex_structure.c not found")
        result = self.extractor.process_file(MULTI_FUNC_INPUT)
        funcs = {f['function']: f for f in result['functions']
                 if f['function'] in ('func1', 'func2')}
        # Both functions in the test file have specs before the header
        assert funcs['func1']['funcspec'] is not None
        assert funcs['func2']['funcspec'] is not None

    def test_spec_after_header_before_brace(self, tmp_path):
        """A function header followed by /*@ ... */ then { should still be detected."""
        file_path = _write_synthetic(tmp_path, "sll_rotate.c", _MULTI_FUNC_SOURCES)
        result = self.extractor.process_file(file_path)
        funcs = {f['function']: f for f in result['functions']
                 if f['function'] in ('sll_rotate_left', 'sll_rotate_right')}

        assert set(funcs) == {'sll_rotate_left', 'sll_rotate_right'}
        assert funcs['sll_rotate_left']['funcspec'] is not None
        assert funcs['sll_rotate_right']['funcspec'] is not None
        assert len([a for a in funcs['sll_rotate_left']['inner_assertions'] if a['type'] == 'Inv']) == 1
        assert len([a for a in funcs['sll_rotate_right']['inner_assertions'] if a['type'] == 'Inv']) == 1


# ============================================================================
# Translator Prefix Tests
# ============================================================================

class TestTranslatorPrefix:
    def setup_method(self):
        self.translator = ShapeTranslator()

    def test_prefix_variable_naming(self):
        self.translator.reset_var_counter(prefix="1")
        var = self.translator.generate_list_var()
        assert var == "?l1_1"

    def test_prefix_multiple_vars(self):
        self.translator.reset_var_counter(prefix="2")
        v1 = self.translator.generate_list_var()
        v2 = self.translator.generate_list_var()
        assert v1 == "?l2_1"
        assert v2 == "?l2_2"

    def test_no_prefix_backward_compat(self):
        self.translator.reset_var_counter()
        v1 = self.translator.generate_list_var()
        v2 = self.translator.generate_list_var()
        assert v1 == "?l1"
        assert v2 == "?l2"

    def test_translate_assertion_with_prefix(self):
        translated, vars = self.translator.translate_assertion("listrep(x)", prefix="1")
        assert "?l1_1" in translated
        assert vars == ["?l1_1"]

    def test_translate_with_exists_prefix(self):
        translated, vars = self.translator.translate_assertion_with_exists(
            "listrep(x) * listrep(y)", prefix="1"
        )
        assert "exists l1_1 l1_2," in translated
        assert vars == ["l1_1", "l1_2"]


# ============================================================================
# Process & Translate Multi-Function Tests
# ============================================================================

class TestProcessTranslateMultiFunc:
    def test_single_inv_no_prefix(self):
        """Single Inv assertion should use l1, l2 without prefix."""
        processor = AssertionProcessor()
        inner = [{'type': 'Inv', 'content': 'listrep(x) * listrep(y)', 'position': 0, 'command_guard': 'x'}]
        result = processor.translate_inner_assertions(inner)
        assert len(result) == 1
        assert 'l1' in result[0]['translated']
        assert 'l2' in result[0]['translated']
        # Should NOT have prefix separator
        assert 'l1_' not in result[0]['translated']

    def test_multiple_inv_uses_prefix(self):
        """Multiple Inv assertions should use prefixed variables."""
        processor = AssertionProcessor()
        inner = [
            {'type': 'Inv', 'content': 'listrep(x)', 'position': 0, 'command_guard': 'x'},
            {'type': 'Inv', 'content': 'listrep(y)', 'position': 100, 'command_guard': 'y'},
        ]
        result = processor.translate_inner_assertions(inner)
        assert len(result) == 2
        # First Inv gets prefix "1"
        assert 'l1_1' in result[0]['translated']
        # Second Inv gets prefix "2"
        assert 'l2_1' in result[1]['translated']

    def test_process_file_returns_functions(self):
        if not os.path.exists(MULTI_FUNC_INPUT):
            pytest.skip("test_complex_structure.c not found")
        result = process_and_translate_file(MULTI_FUNC_INPUT, generate_guards=False)
        assert 'functions' in result
        assert len(result['functions']) >= 2

        func_names = [f['function'] for f in result['functions']]
        assert 'func1' in func_names
        assert 'func2' in func_names

    def test_multi_func_funcspec_translated(self):
        if not os.path.exists(MULTI_FUNC_INPUT):
            pytest.skip("test_complex_structure.c not found")
        result = process_and_translate_file(MULTI_FUNC_INPUT, generate_guards=False)
        funcs = {f['function']: f for f in result['functions']
                 if f['function'] in ('func1', 'func2')}

        # func1 funcspec should be translated
        assert funcs['func1']['funcspec'] is not None
        assert 'sll' in funcs['func1']['funcspec']['require']['translated']

        # func2 funcspec should be translated
        assert funcs['func2']['funcspec'] is not None
        assert 'sll' in funcs['func2']['funcspec']['require']['translated']


# ============================================================================
# End-to-End Multi-Function Translation Tests
# ============================================================================

class TestMultiFuncEndToEnd:
    def test_multi_func_translate(self):
        if not os.path.exists(MULTI_FUNC_INPUT):
            pytest.skip("test_complex_structure.c not found")
        if not os.path.exists(MULTI_FUNC_EXPECTED):
            pytest.skip("test_complex_structure_rel.c not found")

        with tempfile.NamedTemporaryFile(mode='w', suffix='_rel.c', delete=False) as f:
            output_path = f.name

        try:
            assert translate_c_file(MULTI_FUNC_INPUT, output_path)

            with open(output_path, 'r') as f:
                output = f.read()

            # Check func1 has safeExec in spec and invariant
            assert 'func1_M' in output
            assert 'func1_M_loop' in output

            # Check func2 has safeExec in spec and invariant
            assert 'func2_M' in output
            assert 'func2_M_loop' in output
        finally:
            os.unlink(output_path)

    def test_multi_func_funcspec_replacement(self):
        if not os.path.exists(MULTI_FUNC_INPUT):
            pytest.skip("test_complex_structure.c not found")

        with tempfile.NamedTemporaryFile(mode='w', suffix='_rel.c', delete=False) as f:
            output_path = f.name

        try:
            assert translate_c_file(MULTI_FUNC_INPUT, output_path)

            with open(output_path, 'r') as f:
                output = f.read()

            # Both functions should have safeExec in their specs
            assert 'safeExec(ATrue, func1_M(' in output
            assert 'safeExec(ATrue, func2_M(' in output
            # Both should have return(...) in Ensure
            assert 'return(' in output
        finally:
            os.unlink(output_path)

    def test_multi_func_inv_replacement(self):
        if not os.path.exists(MULTI_FUNC_INPUT):
            pytest.skip("test_complex_structure.c not found")

        with tempfile.NamedTemporaryFile(mode='w', suffix='_rel.c', delete=False) as f:
            output_path = f.name

        try:
            assert translate_c_file(MULTI_FUNC_INPUT, output_path)

            with open(output_path, 'r') as f:
                output = f.read()

            # func1 has 1 loop - no prefix needed
            assert 'exists l1 l2 l3,' in output

            # func2 has 2 loops - prefixed variables
            assert 'l1_1' in output  # first loop vars
            assert 'l2_1' in output  # second loop vars
        finally:
            os.unlink(output_path)

    def test_replace_funcspec_before_pattern(self):
        """Test replacement when /*@ ... */ appears before the function header."""
        content = """/*@ Require listrep(x)
    Ensure listrep(__return)
 */
struct list * myfunc(struct list * x) {
    return x;
}
"""
        processed = {
            'with': {'translated': 'X'},
            'require': {'with_safeexec': 'safeExec(ATrue, myfunc_M(?l1), X) && sll(x, ?l1)'},
            'ensure': {'with_safeexec': 'safeExec(ATrue, return(?l2), X) && sll(__return, ?l2)'},
        }
        result = replace_funcspec(content, "myfunc", processed, "myfunc_M")
        assert 'safeExec' in result
        assert 'myfunc_M' in result

    def test_replace_funcspec_emits_helper_low_level_specs(self):
        content = """struct list * sll_merge(struct list * x, struct list * y)
/*@ Require listrep(x) * listrep(y)
    Ensure listrep(__return)
 */;
"""
        funcspec = {
            'require': {
                'translated': 'sll(x, ?l1) * sll(y, ?l2)',
                'variables': ['?l1', '?l2'],
                'variable_types': ['list Z', 'list Z'],
            },
            'ensure': {
                'translated': 'sll(__return, ?l3)',
                'variables': ['?l3'],
                'variable_types': ['list Z'],
            },
        }
        result = replace_funcspec(
            content,
            "sll_merge",
            funcspec,
            "sll_merge_M",
            is_callee_funcspec=True,
        )
        assert result.count('struct list * sll_merge(struct list * x, struct list * y)') == 2
        assert '/*@ low_level_spec' in result
        assert '/*@ low_level_spec_aux <= low_level_spec' in result
        assert 'With {B} (cont: (list Z) -> program unit B) X l1 l2' in result
        assert 'Require safeExec(ATrue, bind(sll_merge_M(l1, l2), cont), X)' in result
        assert 'Ensure exists l3, safeExec(ATrue, bind(return(l3), cont), X)' in result

    def test_helper_aux_spec_precedes_primary_and_uses_witness_in_cont_type(self):
        """For a scalar-return function with body, the aux declaration must
        come FIRST (with ``;``) and the primary definition SECOND.  The
        aux's cont type must include the synthetic ``r`` witness type, and
        the Ensure's ``return(...)`` form must be the real one (with
        ``maketuple``), wrapped in ``bind(..., cont)``.  Regression for
        ``glibc_slist_iter_back`` where order was reversed, cont was
        ``(list Z)`` instead of ``(list Z * Z)``, and the bind wrap was
        missing.
        """
        content = (
            "long demo(struct list *x)\n"
            "/*@ Require listrep(x)\n"
            "    Ensure listrep(x@pre)\n"
            " */\n"
            "{\n"
            "    if (x == 0) { return 0; }\n"
            "    return demo(x->next) + x->data;\n"
            "}\n"
        )
        funcspec = {
            "require": {
                "translated": "sll(x, ?l1)",
                "variables": ["?l1"],
                "variable_types": ["list Z"],
            },
            "ensure": {
                "translated": "sll(x@pre, ?l2)",
                "variables": ["?l2"],
                "variable_types": ["list Z"],
            },
        }
        result = replace_funcspec(
            content,
            "demo",
            funcspec,
            "demo_M",
            is_callee_funcspec=True,
            return_type="long",
        )

        # Order: aux declaration first (terminated with ';'), primary on body.
        aux_pos = result.index("low_level_spec_aux <= low_level_spec")
        primary_pos = result.index("low_level_spec\n")
        assert aux_pos < primary_pos, "aux spec must precede primary spec"

        # Cont arg type includes the synthetic witness ``r : Z``.
        assert "(cont: (list Z * Z) -> program unit B)" in result
        # Ensure wraps the real return form (with maketuple) in bind(...).
        assert "bind(return(maketuple(l2, r)), cont)" in result


    def test_replace_inner_assertions_for_func(self):
        """Only the target function's Inv should be replaced."""
        content = """void func_a(int x) {
    /*@ Inv listrep(x) */
    while (x) { x--; }
}

void func_b(int y) {
    /*@ Inv listrep(y) */
    while (y) { y--; }
}
"""
        inner_assertions = [{
            'type': 'Inv',
            'translated': 'exists l1, sll(x, l1)',
            'variables': ['l1'],
        }]
        from GenMonads.addabstract import add_safeexec_predicate
        inner_assertions[0]['translated'] = add_safeexec_predicate(
            inner_assertions[0]['translated'],
            inner_assertions[0]['variables'],
            "func_a_M_loop", "func_a_M_loop_end"
        )
        result = replace_inner_assertions_for_func(
            content, "func_a", inner_assertions,
            "func_a_M_loop", "func_a_M_loop_end"
        )
        # func_a's Inv should be replaced
        assert 'func_a_M_loop' in result
        # func_b's Inv should be untouched
        assert '/*@ Inv listrep(y) */' in result

    def test_header_then_spec_translation(self, tmp_path):
        """Multi-function files with spec after the header should translate
        both functions.  Uses a synthetic two-function source so the test
        doesn't depend on any file in ``shape_invdataset/``.
        """
        c_src = tmp_path / "two_funcs.c"
        c_src.write_text(
            '#include "verification_list.h"\n'
            '#include "sll_shape_def.h"\n'
            '\n'
            'struct list *func_a(struct list *x)\n'
            '/*@ Require listrep(x)\n'
            '    Ensure  listrep(__return)\n'
            ' */\n'
            '{\n'
            '    /*@ Inv listrep(x) */\n'
            '    while (x != 0) { x = x->next; }\n'
            '    return x;\n'
            '}\n'
            '\n'
            'struct list *func_b(struct list *y)\n'
            '/*@ Require listrep(y)\n'
            '    Ensure  listrep(__return)\n'
            ' */\n'
            '{\n'
            '    /*@ Inv listrep(y) */\n'
            '    while (y != 0) { y = y->next; }\n'
            '    return y;\n'
            '}\n'
        )
        output_path = tmp_path / "two_funcs_rel.c"

        assert translate_c_file(str(c_src), str(output_path))
        output = output_path.read_text()

        assert 'func_a_M' in output
        assert 'func_b_M' in output
        assert 'safeExec(ATrue, func_a_M(' in output
        assert 'safeExec(ATrue, func_b_M(' in output
        assert 'bind(func_a_M_loop' in output
        assert 'bind(func_b_M_loop' in output


# ============================================================================
# Generated Single-Function Fixture Tests
# ============================================================================

class TestSingleFuncFixtures:
    """Test the pipeline against generated single-function C files."""

    @pytest.mark.parametrize("filename", _SINGLE_FUNC_FILENAMES, ids=_SINGLE_FUNC_FILENAMES)
    def test_extraction(self, tmp_path, filename):
        """Each single-function file should extract a funcspec and inner assertions."""
        file_path = _write_synthetic(tmp_path, filename, _SINGLE_FUNC_SOURCES)
        extractor = AnnotationExtractor()
        result = extractor.process_file(file_path)

        assert 'error' not in result, f"{filename}: {result.get('error')}"
        assert result['funcspec'] is not None, f"{filename}: no funcspec found"
        assert result['funcspec']['require'] is not None, f"{filename}: no Require"
        assert result['funcspec']['ensure'] is not None, f"{filename}: no Ensure"
        assert len(result['inner_assertions']) > 0, f"{filename}: no inner assertions"

    @pytest.mark.parametrize("filename", _SINGLE_FUNC_FILENAMES, ids=_SINGLE_FUNC_FILENAMES)
    def test_translation(self, tmp_path, filename):
        """Each single-function file should translate without errors."""
        file_path = _write_synthetic(tmp_path, filename, _SINGLE_FUNC_SOURCES)
        result = process_and_translate_file(file_path, generate_guards=False)

        assert 'error' not in result, f"{filename}: {result.get('error')}"
        assert result['funcspec'] is not None, f"{filename}: no translated funcspec"

        # Check that translation produced data predicates
        # Note: dlistrep_shape -> dlistrep (contains 'listrep' substring), so only check
        # for exact 'listrep(' which is the SLL shape predicate
        spec = result['funcspec']
        if 'require' in spec and 'translated' in spec['require']:
            translated = spec['require']['translated']
            import re as _re
            bare_listrep = _re.findall(r'(?<!d)listrep\(', translated)
            assert len(bare_listrep) == 0, \
                f"{filename}: shape predicate listrep() not translated in Require"

        # All Inv assertions should be translated
        for i, a in enumerate(result['inner_assertions']):
            if a['type'] == 'Inv':
                assert 'translated' in a, f"{filename}: Inv {i} not translated"
                assert 'error' not in a, f"{filename}: Inv {i} error: {a.get('error')}"

    @pytest.mark.parametrize("filename", _SINGLE_FUNC_FILENAMES, ids=_SINGLE_FUNC_FILENAMES)
    def test_end_to_end(self, tmp_path, filename):
        """Each single-function file should translate end-to-end."""
        file_path = _write_synthetic(tmp_path, filename, _SINGLE_FUNC_SOURCES)
        output_path = str(tmp_path / f"{filename}_rel.c")
        success = translate_c_file(file_path, output_path)
        assert success, f"{filename}: translate_c_file returned False"

        with open(output_path, 'r') as f:
            output = f.read()

        assert 'safeExec' in output, f"{filename}: no safeExec in output"
        assert 'bind(' in output, f"{filename}: no bind() in output"


# ============================================================================
# Generated Multi-Function Fixture Tests
# ============================================================================

class TestMultiFuncFixtures:
    """Test the pipeline against generated multi-function C files."""

    @pytest.mark.parametrize("filename", _MULTI_FUNC_FILENAMES, ids=_MULTI_FUNC_FILENAMES)
    def test_extraction_multiple_functions(self, tmp_path, filename):
        """Each multi-function file should extract functions."""
        file_path = _write_synthetic(tmp_path, filename, _MULTI_FUNC_SOURCES)
        extractor = AnnotationExtractor()
        result = extractor.process_file(file_path)

        assert 'error' not in result, f"{filename}: {result.get('error')}"
        assert 'functions' in result

        # Filter out non-real functions (struct, keywords, etc.)
        real_funcs = [f for f in result['functions']
                      if f['function'] not in ('while', 'if', 'for', 'switch', 'return')]

        # Should have at least 1 function with spec
        funcs_with_specs = [f for f in real_funcs if f['funcspec'] is not None]
        assert len(funcs_with_specs) >= 1, \
            f"{filename}: expected >=1 functions with specs, got {len(funcs_with_specs)}: " \
            f"{[f['function'] for f in funcs_with_specs]}"

    # Synthetic multi-function fixtures, parameterized so we get one test
    # per shape variation.  Each entry is (id, c_source); the test writes the
    # source to a temp file and runs the pipeline.  Avoids depending on any
    # checked-in dataset file that might be edited outside the test scope.
    _MULTI_FUNC_SYNTHETIC_FIXTURES = [
        (
            "two_simple_loops",
            '#include "verification_list.h"\n'
            '#include "sll_shape_def.h"\n'
            '\n'
            'struct list *f1(struct list *x)\n'
            '/*@ Require listrep(x)\n'
            '    Ensure  listrep(__return)\n'
            ' */\n'
            '{\n'
            '    /*@ Inv listrep(x) */\n'
            '    while (x != 0) { x = x->next; }\n'
            '    return x;\n'
            '}\n'
            '\n'
            'struct list *f2(struct list *y)\n'
            '/*@ Require listrep(y)\n'
            '    Ensure  listrep(__return)\n'
            ' */\n'
            '{\n'
            '    /*@ Inv listrep(y) */\n'
            '    while (y != 0) { y = y->next; }\n'
            '    return y;\n'
            '}\n',
        ),
        (
            "loops_with_data_witness",
            '#include "verification_list.h"\n'
            '#include "sll_shape_def.h"\n'
            '\n'
            'struct list *g1(struct list *t)\n'
            '/*@ Require listrep(t)\n'
            '    Ensure  listrep(__return)\n'
            ' */\n'
            '{\n'
            '    /*@ Inv exists w, t != 0 && t -> data == w && listrep(t) */\n'
            '    while (t != 0) { t = t->next; }\n'
            '    return t;\n'
            '}\n'
            '\n'
            'struct list *g2(struct list *u)\n'
            '/*@ Require listrep(u)\n'
            '    Ensure  listrep(__return)\n'
            ' */\n'
            '{\n'
            '    /*@ Inv listrep(u) */\n'
            '    while (u != 0) { u = u->next; }\n'
            '    return u;\n'
            '}\n',
        ),
    ]

    @pytest.mark.parametrize(
        "fixture_id,c_source",
        _MULTI_FUNC_SYNTHETIC_FIXTURES,
        ids=[fid for fid, _ in _MULTI_FUNC_SYNTHETIC_FIXTURES],
    )
    def test_translation_multiple_functions(self, tmp_path, fixture_id, c_source):
        """Multi-function pipeline translates every annotated function in a
        file.  Uses synthetic in-test C sources so the test does not depend
        on any file in ``shape_invdataset/``.
        """
        c_file = tmp_path / f"{fixture_id}.c"
        c_file.write_text(c_source)
        result = process_and_translate_file(str(c_file), generate_guards=False)

        assert 'error' not in result, f"{fixture_id}: {result.get('error')}"
        assert 'functions' in result

        translated_any = False
        for func in result['functions']:
            if func['funcspec'] is None:
                continue
            translated_any = True
            spec = func['funcspec']
            if 'require' in spec:
                assert 'translated' in spec['require'], \
                    f"{fixture_id}/{func['function']}: Require not translated"
            for i, a in enumerate(func['inner_assertions']):
                if a['type'] == 'Inv':
                    assert 'translated' in a, \
                        f"{fixture_id}/{func['function']}: Inv {i} not translated"
        assert translated_any, f"{fixture_id}: no function spec was translated"

    @pytest.mark.parametrize("filename", _MULTI_FUNC_FILENAMES, ids=_MULTI_FUNC_FILENAMES)
    def test_end_to_end_multiple_functions(self, tmp_path, filename):
        """Each multi-function file should translate end-to-end."""
        file_path = _write_synthetic(tmp_path, filename, _MULTI_FUNC_SOURCES)
        output_path = str(tmp_path / f"{filename}_rel.c")
        success = translate_c_file(file_path, output_path)
        assert success, f"{filename}: translate_c_file returned False"

        with open(output_path, 'r') as f:
            output = f.read()

        assert 'safeExec' in output, f"{filename}: no safeExec in output"

