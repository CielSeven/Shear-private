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

BASE_DIR = os.path.dirname(os.path.dirname(os.path.dirname(__file__)))
FIXTURES_DIR = os.path.join(os.path.dirname(__file__), 'fixtures')
SLL_DIR = os.path.join(BASE_DIR, 'shape_invdataset', 'sll')
DLL_DIR = os.path.join(BASE_DIR, 'shape_invdataset', 'dll')
MULTI_FUNC_INPUT = os.path.join(FIXTURES_DIR, 'test_complex_structure.c')
MULTI_FUNC_EXPECTED = os.path.join(FIXTURES_DIR, 'test_complex_structure_rel.c')
SLL_ROTATE_INPUT = os.path.join(SLL_DIR, 'sll_rotate.c')



def _discover_c_files(*dirs):
    """Find all .c files in the given directories."""
    paths = []
    for d in dirs:
        if not os.path.exists(d):
            continue
        for f in sorted(os.listdir(d)):
            if f.endswith('.c'):
                paths.append((os.path.join(d, f), f))
    return paths


def _classify_files():
    """Auto-discover and classify C files into single-function and multi-function.

    Single-function: backward-compatible funcspec found (spec after function header).
    Multi-function: multiple annotated functions in the functions list.
    Files with no annotations are skipped.
    """
    all_files = _discover_c_files(SLL_DIR, DLL_DIR)
    single, multi = [], []
    for file_path, filename in all_files:
        extractor = AnnotationExtractor()
        result = extractor.process_file(file_path)
        if 'error' in result:
            continue
        real_funcs = [f for f in result.get('functions', [])
                      if f['funcspec'] is not None
                      and f['function'] not in ('while', 'if', 'for', 'switch', 'return')]
        if len(real_funcs) >= 2:
            multi.append((file_path, filename))
        elif result.get('funcspec') is not None:
            single.append((file_path, filename))
        elif len(real_funcs) == 1:
            # Single function but spec-before-header (not backward-compatible)
            multi.append((file_path, filename))
    return single, multi


_SINGLE_FUNC_PATHS, _MULTI_FUNC_PATHS = _classify_files()


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

    def test_spec_after_header_before_brace(self):
        """A function header followed by /*@ ... */ then { should still be detected."""
        if not os.path.exists(SLL_ROTATE_INPUT):
            pytest.skip("sll_rotate.c not found")
        result = self.extractor.process_file(SLL_ROTATE_INPUT)
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

    def test_header_then_spec_translation(self):
        """Multi-function files with spec after the header should translate both functions."""
        if not os.path.exists(SLL_ROTATE_INPUT):
            pytest.skip("sll_rotate.c not found")

        with tempfile.NamedTemporaryFile(mode='w', suffix='_rel.c', delete=False) as f:
            output_path = f.name

        try:
            assert translate_c_file(SLL_ROTATE_INPUT, output_path)

            with open(output_path, 'r') as f:
                output = f.read()

            assert 'sll_rotate_left_M' in output
            assert 'sll_rotate_right_M' in output
            assert 'safeExec(ATrue, sll_rotate_left_M(' in output
            assert 'safeExec(ATrue, sll_rotate_right_M(' in output
            assert 'bind(sll_rotate_left_M_loop' in output
            assert 'bind(sll_rotate_right_M_loop' in output
        finally:
            os.unlink(output_path)


# ============================================================================
# Generated Single-Function Fixture Tests
# ============================================================================

class TestSingleFuncFixtures:
    """Test the pipeline against generated single-function C files."""

    @pytest.mark.parametrize("file_path,filename", _SINGLE_FUNC_PATHS,
                             ids=[p[1] for p in _SINGLE_FUNC_PATHS])
    def test_extraction(self, file_path, filename):
        """Each single-function file should extract a funcspec and inner assertions."""
        if not os.path.exists(file_path):
            pytest.skip(f"{filename} not found")
        extractor = AnnotationExtractor()
        result = extractor.process_file(file_path)

        assert 'error' not in result, f"{filename}: {result.get('error')}"
        assert result['funcspec'] is not None, f"{filename}: no funcspec found"
        assert result['funcspec']['require'] is not None, f"{filename}: no Require"
        assert result['funcspec']['ensure'] is not None, f"{filename}: no Ensure"
        assert len(result['inner_assertions']) > 0, f"{filename}: no inner assertions"

    @pytest.mark.parametrize("file_path,filename", _SINGLE_FUNC_PATHS,
                             ids=[p[1] for p in _SINGLE_FUNC_PATHS])
    def test_translation(self, file_path, filename):
        """Each single-function file should translate without errors."""
        if not os.path.exists(file_path):
            pytest.skip(f"{filename} not found")
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

    @pytest.mark.parametrize("file_path,filename", _SINGLE_FUNC_PATHS,
                             ids=[p[1] for p in _SINGLE_FUNC_PATHS])
    def test_end_to_end(self, file_path, filename):
        """Each single-function file should translate end-to-end."""
        if not os.path.exists(file_path):
            pytest.skip(f"{filename} not found")
        with tempfile.NamedTemporaryFile(mode='w', suffix='_rel.c', delete=False) as f:
            output_path = f.name
        try:
            success = translate_c_file(file_path, output_path)
            assert success, f"{filename}: translate_c_file returned False"

            with open(output_path, 'r') as f:
                output = f.read()

            assert 'safeExec' in output, f"{filename}: no safeExec in output"
            assert 'bind(' in output, f"{filename}: no bind() in output"
        finally:
            os.unlink(output_path)


# ============================================================================
# Generated Multi-Function Fixture Tests
# ============================================================================

class TestMultiFuncFixtures:
    """Test the pipeline against generated multi-function C files."""

    @pytest.mark.parametrize("file_path,filename", _MULTI_FUNC_PATHS,
                             ids=[p[1] for p in _MULTI_FUNC_PATHS])
    def test_extraction_multiple_functions(self, file_path, filename):
        """Each multi-function file should extract functions."""
        if not os.path.exists(file_path):
            pytest.skip(f"{filename} not found")
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

    @pytest.mark.parametrize("file_path,filename", _MULTI_FUNC_PATHS,
                             ids=[p[1] for p in _MULTI_FUNC_PATHS])
    def test_translation_multiple_functions(self, file_path, filename):
        """Each multi-function file should translate all functions."""
        if not os.path.exists(file_path):
            pytest.skip(f"{filename} not found")
        result = process_and_translate_file(file_path, generate_guards=False)

        assert 'error' not in result, f"{filename}: {result.get('error')}"
        assert 'functions' in result

        for func in result['functions']:
            if func['funcspec'] is None:
                continue
            spec = func['funcspec']
            if 'require' in spec:
                assert 'translated' in spec['require'], \
                    f"{filename}/{func['function']}: Require not translated"
            for i, a in enumerate(func['inner_assertions']):
                if a['type'] == 'Inv':
                    assert 'translated' in a, \
                        f"{filename}/{func['function']}: Inv {i} not translated"

    @pytest.mark.parametrize("file_path,filename", _MULTI_FUNC_PATHS,
                             ids=[p[1] for p in _MULTI_FUNC_PATHS])
    def test_end_to_end_multiple_functions(self, file_path, filename):
        """Each multi-function file should translate end-to-end."""
        if not os.path.exists(file_path):
            pytest.skip(f"{filename} not found")
        with tempfile.NamedTemporaryFile(mode='w', suffix='_rel.c', delete=False) as f:
            output_path = f.name
        try:
            success = translate_c_file(file_path, output_path)
            assert success, f"{filename}: translate_c_file returned False"

            with open(output_path, 'r') as f:
                output = f.read()

            assert 'safeExec' in output, f"{filename}: no safeExec in output"
        finally:
            os.unlink(output_path)

