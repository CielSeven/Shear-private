"""
Test suite for C file translation.

Tests translating synthetic C source fixtures (written to tmp_path) into
rel files.  No checked-in dataset files are read.
"""

import os
import re
import pytest

from GenMonads.translate_c_file import (
    translate_c_file, translate_c_file_data_only, translate_directory,
    insert_safeexec_include, generate_coq_blocks, collect_func_extern_info,
    collect_callee_functions,
)


# ---------------------------------------------------------------------------
# Synthetic C source fixtures
# ---------------------------------------------------------------------------

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


_SLL_MULTI_MERGE_SRC = (
    '#include "verification_list.h"\n'
    '#include "sll_shape_def.h"\n'
    '\n'
    'struct list { int data; struct list *next; };\n'
    '\n'
    'struct list * sll_merge(struct list * x, struct list * y)\n'
    '/*@ Require listrep(x) * listrep(y)\n'
    '    Ensure  listrep(__return)\n'
    ' */;\n'
    '\n'
    'struct list * sll_multi_merge(struct list * x, struct list * y, struct list * z)\n'
    '/*@ Require listrep(x) * listrep(y) * listrep(z)\n'
    '    Ensure  listrep(__return)\n'
    ' */\n'
    '{\n'
    '    struct list *t, *u;\n'
    '    if (x == (struct list *) 0) { t = sll_merge(y, z); return t; }\n'
    '    t = x; u = t->next;\n'
    '    /*@ Inv exists v, v == t -> data && u == t -> next && t != 0 &&\n'
    '            listrep(y) * listrep(z) * listrep(u) * lseg(x@pre, t) */\n'
    '    while (u) {\n'
    '        if (y) { t->next = y; t = y; y = y->next; }\n'
    '        else { u = sll_merge(u, z); t->next = u; return x; }\n'
    '        if (z) { t->next = z; t = z; z = z->next; }\n'
    '        else { u = sll_merge(u, y); t->next = u; return x; }\n'
    '        t->next = u; t = u; u = u->next;\n'
    '    }\n'
    '    u = sll_merge(y, z); t->next = u;\n'
    '    return x;\n'
    '}\n'
)


def _write_src(tmp_path, name, src):
    p = tmp_path / name
    p.write_text(src, encoding="utf-8")
    return str(p)


# ============================================================================
# Single File Tests
# ============================================================================

class TestSingleFile:
    def test_sll_copy(self, tmp_path):
        input_path = _write_src(tmp_path, 'sll_copy.c', _SLL_COPY_SRC)
        output_path = str(tmp_path / 'sll_copy_rel.c')

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

    def test_sll_append(self, tmp_path):
        input_path = _write_src(tmp_path, 'sll_append.c', _SLL_APPEND_SRC)
        output_path = str(tmp_path / 'sll_append_rel.c')

        assert translate_c_file(input_path, output_path)

        with open(output_path, 'r') as f:
            content = f.read()

        assert 'safeExec' in content
        assert 'sll_append_M_loop' in content

    def test_data_only_translates_invariant_with_pure_implication(self, tmp_path):
        src = (
            '#include "glibc_slist_clean.h"\n'
            '\n'
            'long glibc_slist_clean_iter_back_2(struct list *x)\n'
            '/*@ Require listrep(x)\n'
            '    Ensure  exists v, __return == v && listrep(x@pre)\n'
            ' */\n'
            '{\n'
            '    struct list *stop;\n'
            '    struct list *prev;\n'
            '    struct list *node;\n'
            '    long sum;\n'
            '    /*@ Inv exists p s nxt v,\n'
            '            x == x@pre && x != 0 && node != 0 &&\n'
            '            ((nxt == 0) => (stop == 0)) &&\n'
            '            node -> next == nxt && node -> data == v &&\n'
            '            store(&prev, struct list*, p) *\n'
            '            store(&sum, long, s) *\n'
            '            lseg(x, node) * lseg(nxt, stop) * listrep(stop)\n'
            '     */\n'
            '    while (node->next != stop && node->next != 0) {\n'
            '        prev = node;\n'
            '        node = node->next;\n'
            '    }\n'
            '    return sum;\n'
            '}\n'
        )
        input_path = _write_src(tmp_path, 'glibc_slist_iter_back_2.c', src)
        output_path = str(tmp_path / 'glibc_slist_iter_back_2_data.c')

        assert translate_c_file_data_only(input_path, output_path)
        content = (tmp_path / 'glibc_slist_iter_back_2_data.c').read_text()
        assert "=> (stop == 0)" in content
        assert "sllseg(x, node" in content
        assert "sllseg(nxt, stop" in content
        assert "sll(stop" in content
        assert re.search(r"\blseg\s*\(", content) is None
        assert re.search(r"\blistrep\s*\(", content) is None
        assert "safeExec" not in content


# ============================================================================
# Directory Tests
# ============================================================================

class TestDirectory:
    def test_directory_translation(self, tmp_path):
        """translate_directory should process every .c file in a directory."""
        in_dir = tmp_path / "inputs"
        out_dir = tmp_path / "outputs"
        in_dir.mkdir()
        (in_dir / "sll_copy.c").write_text(_SLL_COPY_SRC)
        (in_dir / "sll_append.c").write_text(_SLL_APPEND_SRC)

        results = translate_directory(str(in_dir), str(out_dir))
        total = len(results)
        success = sum(1 for v in results.values() if v)
        assert total == 2
        assert success == total, \
            f"{total - success} files failed: {[k for k, v in results.items() if not v]}"


# ============================================================================
# Verification Tests
# ============================================================================

class TestOutputVerification:
    def test_sll_copy_output_contents(self, tmp_path):
        input_path = _write_src(tmp_path, 'sll_copy.c', _SLL_COPY_SRC)
        output_path = str(tmp_path / 'sll_copy_rel.c')
        assert translate_c_file(input_path, output_path)

        with open(output_path, 'r') as f:
            content = f.read()

        assert 'sll(x, l' in content, "Function spec should use sll predicate with exists-quantified vars"
        assert 'safeExec(ATrue, bind(sll_copy_M_loop' in content, "safeExec with correct program"
        assert 'exists' in content, "Exists quantifier in invariant"
        assert 'sllseg(' in content, "sllseg predicate used"

    def test_compare_original_and_translated(self, tmp_path):
        input_path = _write_src(tmp_path, 'sll_copy.c', _SLL_COPY_SRC)
        output_path = str(tmp_path / 'sll_copy_rel.c')
        assert translate_c_file(input_path, output_path)

        with open(input_path, 'r') as f:
            original = f.read()
        with open(output_path, 'r') as f:
            translated = f.read()

        # Original should have shape predicates
        assert 'listrep(' in original
        # Translated should not have shape predicates in specs
        assert 'sll(' in translated
        assert 'sllseg(' in translated

    def test_multi_merge_output_declares_helper_program_signature(self, tmp_path):
        input_path = _write_src(tmp_path, 'sll_multi_merge.c', _SLL_MULTI_MERGE_SRC)
        output_path = str(tmp_path / 'sll_multi_merge_rel.c')
        assert translate_c_file(input_path, output_path)

        with open(output_path, 'r') as f:
            content = f.read()

        assert '/*@ Extern Coq (early_result :: * => * => *) */' in content
        assert '(sll_merge_M: list Z -> list Z -> program unit (list Z))' in content
        assert '(sll_multi_merge_M: list Z -> list Z -> list Z -> program unit (list Z))' in content
        assert '(sll_multi_merge_M_loop_before: list Z -> list Z -> list Z -> program unit (early_result (list Z * list Z * list Z * list Z * Z) (list Z)))' in content
        assert '(sll_multi_merge_M_loop: list Z -> list Z -> list Z -> list Z -> Z -> program unit (early_result MretTy (list Z)))' in content
        assert '(sll_multi_merge_M_after_loop: early_result MretTy (list Z) -> program unit (list Z))' in content
        assert 'sll_merge_M_loop' not in content
        assert content.count('struct list * sll_merge(struct list * x, struct list * y)') == 2
        assert '/*@ low_level_spec' in content
        assert '/*@ low_level_spec_aux <= low_level_spec' in content
        assert 'With {B} (cont: (list Z) -> program unit B) X l1 l2' in content
        assert 'Require safeExec(ATrue, bind(sll_merge_M(l1, l2), cont), X)' in content
        assert 'Ensure exists l3, safeExec(ATrue, bind(return(l3), cont), X)' in content
        assert 'bind(sll_multi_merge_M_loop(l1,l2,l3,l4,v), sll_multi_merge_M_after_loop)' in content


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

    def test_skipped_when_header_includes_safeexec_transitively(self, tmp_path):
        # The .c content does NOT mention safeexec_def.h directly, but its
        # included header does.
        (tmp_path / "x.h").write_text('#include "safeexec_def.h"\n')
        content = '#include "x.h"\n\nint main() {}'
        result = insert_safeexec_include(content, header_search_dirs=[str(tmp_path)])
        # Unchanged: don't insert a redundant include.
        assert result == content
        assert result.count("safeexec_def.h") == 0

    def test_skipped_when_nested_header_includes_safeexec(self, tmp_path):
        # x.h -> mid.h -> safeexec_def.h
        (tmp_path / "mid.h").write_text('#include "safeexec_def.h"\n')
        (tmp_path / "x.h").write_text('#include "mid.h"\n')
        content = '#include "x.h"\n\nint main() {}'
        result = insert_safeexec_include(content, header_search_dirs=[str(tmp_path)])
        assert result == content

    def test_inserts_when_header_does_not_include_safeexec(self, tmp_path):
        # The header exists but doesn't include safeexec_def.h, so the .c
        # still needs the explicit include.
        (tmp_path / "x.h").write_text('struct list { int data; struct list *next; };\n')
        content = '#include "x.h"\n\nint main() {}'
        result = insert_safeexec_include(content, header_search_dirs=[str(tmp_path)])
        assert '#include "safeexec_def.h"' in result

    def test_present_in_sll_copy_output(self, tmp_path):
        input_path = _write_src(tmp_path, 'sll_copy.c', _SLL_COPY_SRC)
        output_path = str(tmp_path / 'sll_copy_rel.c')
        assert translate_c_file(input_path, output_path)
        with open(output_path, 'r') as f:
            content = f.read()
        assert '#include "safeexec_def.h"' in content

    def test_skipped_when_mapped_data_header_in_output_dir_already_includes_safeexec(self, tmp_path, monkeypatch):
        """When the header mapping rewrites an input header to a data header
        that lives next to the generated _rel.c and already pulls in
        ``safeexec_def.h``, the translator must detect that transitively and
        skip the duplicate insertion.  Regression for the ``Glibc_slist_clean``
        dataset where ``glibc_slist_clean.h -> glibc_slist_clean_data.h`` and
        the data header sits in the output dir, not the input dir.
        """
        # Put the data header in the OUTPUT directory (not the input dir).
        out_dir = tmp_path / "out"
        out_dir.mkdir()
        (out_dir / "demo_data.h").write_text(
            'struct list { int data; struct list *next; };\n'
            '#include "safeexec_def.h"\n'
        )
        # Input C uses the original (unmapped) header.  Mapping rewrites it
        # to demo_data.h at translate time.
        in_dir = tmp_path / "in"
        in_dir.mkdir()
        c_file = in_dir / "demo.c"
        c_file.write_text(
            '#include "demo_shape.h"\n'
            '\n'
            'struct list *demo(struct list *x)\n'
            '/*@ Require listrep(x)\n'
            '    Ensure  listrep(__return)\n'
            ' */\n'
            '{ return x; }\n'
        )

        import GenMonads.header_mapping as header_mapping
        original_load = header_mapping._load_mappings
        monkeypatch.setattr(
            header_mapping,
            "_load_mappings",
            lambda: {**original_load(), "demo_shape.h": "demo_data.h"},
        )

        output_path = str(out_dir / "demo_rel.c")
        assert translate_c_file(str(c_file), output_path)
        content = open(output_path).read()
        # Mapped header is present, but safeexec_def.h must NOT be added —
        # it's already pulled in transitively via demo_data.h next to the
        # rel.c output.
        assert '#include "demo_data.h"' in content
        assert content.count('#include "safeexec_def.h"') == 0, \
            f"duplicate safeexec_def.h insertion: {content!r}"


# ============================================================================
# Coq Block Generation Tests
# ============================================================================

class TestCoqBlocks:
    def test_generate_single_function(self):
        infos = [{
            'func_name': 'sll_copy',
            'require_var_count': 1,
            'require_var_types': ['list Z'],
            'inv_var_count': 3,
            'inv_var_types': ['list Z', 'list Z', 'list Z'],
            'ensure_var_count': 2,
            'ensure_var_types': ['list Z', 'list Z'],
        }]
        result = generate_coq_blocks('sll_copy', infos)
        assert '/*@ Import Coq Require Import sll_copy_rel_lib */' in result
        assert '/*@ Extern Coq (MretTy :: *) */' in result
        assert '/*@ Extern Coq (early_result :: * => * => *) */' not in result
        assert '(sll_copy_M: list Z -> program unit (list Z * list Z))' in result
        assert '(sll_copy_M_loop: list Z -> list Z -> list Z -> program unit MretTy)' in result
        assert '(sll_copy_M_loop_end: MretTy -> program unit (list Z * list Z))' in result

    def test_generate_two_require_vars(self):
        infos = [{
            'func_name': 'sll_append',
            'require_var_count': 2,
            'require_var_types': ['list Z', 'list Z'],
            'inv_var_count': 3,
            'inv_var_types': ['list Z', 'list Z', 'list Z'],
            'ensure_var_count': 1,
            'ensure_var_types': ['list Z'],
        }]
        result = generate_coq_blocks('sll_append', infos)
        assert '(sll_append_M: list Z -> list Z -> program unit (list Z))' in result

    def test_generate_maketuple_when_needed(self):
        infos = [{
            'func_name': 'sll_copy',
            'require_var_count': 1,
            'require_var_types': ['list Z'],
            'inv_var_count': 3,
            'inv_var_types': ['list Z', 'list Z', 'list Z'],
            'ensure_var_count': 2,
            'ensure_var_types': ['list Z', 'list Z'],
        }]
        result = generate_coq_blocks('sll_copy', infos, needs_maketuple=True)
        assert '(maketuple: {A} {B} -> A -> B -> (A * B))' in result
        assert '(sll_copy_M: list Z -> program unit (list Z * list Z))' in result

    def test_generate_uses_explicit_variable_types(self):
        infos = [{
            'func_name': 'typed_demo',
            'require_var_count': 2,
            'require_var_types': ['list Z', 'Z'],
            'inv_var_count': 2,
            'inv_var_types': ['list Z', 'bool'],
            'ensure_var_count': 2,
            'ensure_var_types': ['nat', 'list Z'],
        }]
        result = generate_coq_blocks('typed_demo', infos)
        assert '(typed_demo_M: list Z -> Z -> program unit (nat * list Z))' in result
        assert '(typed_demo_M_loop: list Z -> bool -> program unit MretTy)' in result
        assert '(typed_demo_M_loop_end: MretTy -> program unit (nat * list Z))' in result

    def test_generate_uses_non_list_only_variable_types(self):
        infos = [{
            'func_name': 'scalar_demo',
            'require_var_count': 2,
            'require_var_types': ['Z', 'bool'],
            'inv_var_count': 2,
            'inv_var_types': ['nat', 'bool'],
            'ensure_var_count': 1,
            'ensure_var_types': ['Z'],
        }]
        result = generate_coq_blocks('scalar_demo', infos)
        assert '(scalar_demo_M: Z -> bool -> program unit (Z))' in result
        assert '(scalar_demo_M_loop: nat -> bool -> program unit MretTy)' in result
        assert '(scalar_demo_M_loop_end: MretTy -> program unit (Z))' in result

    def test_generate_uses_early_return_signatures_when_needed(self):
        infos = [{
            'func_name': 'early_demo',
            'require_var_count': 1,
            'require_var_types': ['list Z'],
            'inv_var_count': 2,
            'inv_var_types': ['list Z', 'list Z'],
            'ensure_var_count': 1,
            'ensure_var_types': ['list Z'],
            'has_loop_program': True,
            'has_pre_loop_early_return': True,
            'has_loop_body_early_return': True,
        }]
        result = generate_coq_blocks('early_demo', infos)
        assert '/*@ Extern Coq (early_result :: * => * => *) */' in result
        assert '(early_demo_M_loop_before: list Z -> program unit (early_result (list Z * list Z) (list Z)))' in result
        assert '(early_demo_M_loop: list Z -> list Z -> program unit (early_result MretTy (list Z)))' in result
        assert '(early_demo_M_after_loop: early_result MretTy (list Z) -> program unit (list Z))' in result
        assert '(early_demo_M_loop_end: MretTy -> program unit (list Z))' in result

    def test_generate_requires_explicit_variable_types(self):
        infos = [{'func_name': 'missing_types', 'require_var_count': 1, 'inv_var_count': 1, 'ensure_var_count': 1}]
        with pytest.raises(ValueError, match='Missing variable types'):
            generate_coq_blocks('missing_types', infos)

    def test_generate_uses_unit_for_no_ensure_variables(self):
        infos = [{
            'func_name': 'dll_free',
            'has_loop_program': True,
            'require_var_count': 1,
            'require_var_types': ['list Z'],
            'inv_var_count': 1,
            'inv_var_types': ['list Z'],
            'ensure_var_count': 0,
            'ensure_var_types': [],
        }]
        result = generate_coq_blocks('dll_free', infos)
        assert '(dll_free_M: list Z -> program unit unit)' in result
        assert '(dll_free_M_loop_end: MretTy -> program unit unit)' in result

    def test_generate_per_function_mretty_for_multi_loop_file(self):
        """When a file has two functions that both reference MretTy in their
        Extern Coq blocks, the codegen must emit per-function `{fn}_MretTy`
        names to match the merged rel_lib's convention."""
        infos = [
            {
                'func_name': 'f1',
                'has_loop_program': True,
                'require_var_count': 1,
                'require_var_types': ['list Z'],
                'inv_var_count': 1,
                'inv_var_types': ['list Z'],
                'ensure_var_count': 1,
                'ensure_var_types': ['list Z'],
            },
            {
                'func_name': 'f2',
                'has_loop_program': True,
                'require_var_count': 1,
                'require_var_types': ['list Z'],
                'inv_var_count': 1,
                'inv_var_types': ['list Z'],
                'ensure_var_count': 1,
                'ensure_var_types': ['list Z'],
            },
        ]
        result = generate_coq_blocks('two_loops', infos)
        assert '/*@ Extern Coq (f1_MretTy :: *) */' in result
        assert '/*@ Extern Coq (f2_MretTy :: *) */' in result
        assert '/*@ Extern Coq (MretTy :: *) */' not in result
        assert 'f1_M_loop: list Z -> program unit f1_MretTy' in result
        assert 'f2_M_loop: list Z -> program unit f2_MretTy' in result
        assert 'f1_M_loop_end: f1_MretTy -> program unit (list Z)' in result
        assert 'f2_M_loop_end: f2_MretTy -> program unit (list Z)' in result

    def test_generate_bare_mretty_for_single_loop_function(self):
        """A file with exactly one MretTy-using function keeps the bare
        `MretTy` form so single-function files (the common case) stay
        unchanged."""
        infos = [
            {
                'func_name': 'only_loop',
                'has_loop_program': True,
                'require_var_count': 1,
                'require_var_types': ['list Z'],
                'inv_var_count': 1,
                'inv_var_types': ['list Z'],
                'ensure_var_count': 1,
                'ensure_var_types': ['list Z'],
            },
            {
                # Helper without a loop — does not reference MretTy.
                'func_name': 'helper',
                'has_loop_program': False,
                'require_var_count': 1,
                'require_var_types': ['list Z'],
                'inv_var_count': 0,
                'inv_var_types': [],
                'ensure_var_count': 1,
                'ensure_var_types': ['list Z'],
            },
        ]
        result = generate_coq_blocks('one_loop_one_helper', infos)
        assert '/*@ Extern Coq (MretTy :: *) */' in result
        assert 'only_loop_MretTy' not in result
        assert 'only_loop_M_loop: list Z -> program unit MretTy' in result

    def test_generate_helper_function_without_loop_program(self):
        infos = [{
            'func_name': 'sll_merge',
            'has_loop_program': False,
            'require_var_count': 2,
            'require_var_types': ['list Z', 'list Z'],
            'inv_var_count': 0,
            'inv_var_types': [],
            'ensure_var_count': 1,
            'ensure_var_types': ['list Z'],
        }]
        result = generate_coq_blocks('sll_multi_merge', infos)
        assert '(sll_merge_M: list Z -> list Z -> program unit (list Z))' in result
        assert 'sll_merge_M_loop' not in result
        assert 'sll_merge_M_loop_end' not in result

    def test_empty_func_infos(self):
        assert generate_coq_blocks('foo', []) == ''

    def test_no_mretty_extern_when_no_function_uses_mretty(self):
        """When every function in the file is loop-less (e.g. a recursive
        helper), no declaration references ``MretTy``, so the shared
        ``Extern Coq (MretTy :: *)`` line must be suppressed — otherwise the
        emitted block carries a dangling, meaningless type declaration."""
        infos = [{
            'func_name': 'recursive_sum',
            'has_loop_program': False,
            'require_var_count': 1,
            'require_var_types': ['list Z'],
            'inv_var_count': 0,
            'inv_var_types': [],
            'ensure_var_count': 2,
            'ensure_var_types': ['list Z', 'Z'],
        }]
        result = generate_coq_blocks('recursive_sum', infos)
        assert 'MretTy' not in result
        # Sanity: the function's own M signature is still emitted.
        assert '(recursive_sum_M: list Z -> program unit (list Z * Z))' in result

    def test_import_coq_in_sll_copy_output(self, tmp_path):
        input_path = _write_src(tmp_path, 'sll_copy.c', _SLL_COPY_SRC)
        output_path = str(tmp_path / 'sll_copy_rel.c')
        assert translate_c_file(input_path, output_path)
        with open(output_path, 'r') as f:
            content = f.read()
        assert '/*@ Import Coq Require Import sll_copy_rel_lib */' in content

    def test_extern_coq_in_sll_copy_output(self, tmp_path):
        input_path = _write_src(tmp_path, 'sll_copy.c', _SLL_COPY_SRC)
        output_path = str(tmp_path / 'sll_copy_rel.c')
        assert translate_c_file(input_path, output_path)
        with open(output_path, 'r') as f:
            content = f.read()
        assert '/*@ Extern Coq (MretTy :: *) */' in content
        assert 'sll_copy_M: list Z -> program unit (list Z * list Z)' in content
        assert 'sll_copy_M_loop:' in content
        assert 'program unit MretTy' in content
        assert 'sll_copy_M_loop_end: MretTy -> program unit (list Z * list Z)' in content

    def test_extern_coq_in_sll_append_output(self, tmp_path):
        input_path = _write_src(tmp_path, 'sll_append.c', _SLL_APPEND_SRC)
        output_path = str(tmp_path / 'sll_append_rel.c')
        assert translate_c_file(input_path, output_path)
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
            'funcspec': {
                'require': {
                    'translated': 'sll(x, ?l1)',
                    'variables': ['?l1'],
                    'variable_types': ['list Z'],
                },
                'ensure': {
                    'translated': 'sll(__return, ?l2)',
                    'variables': ['?l2'],
                    'variable_types': ['list Z'],
                }
            },
            'inner_assertions': [
                {
                    'type': 'Inv',
                    'translated': 'exists l1 l2 l3, ...',
                    'variables': ['l1', 'l2', 'l3'],
                    'variable_types': ['list Z', 'list Z', 'list Z'],
                }
            ]
        }
        info = collect_func_extern_info(func_data)
        assert info is not None
        assert info['func_name'] == 'sll_copy'
        assert info['require_var_count'] == 1
        assert info['inv_var_count'] == 3
        assert info['require_var_types'] == ['list Z']
        assert info['inv_var_types'] == ['list Z', 'list Z', 'list Z']
        assert info['ensure_var_types'] == ['list Z']

    def test_helper_function_can_be_included_for_translation(self):
        func_data = {
            'function': 'sll_merge',
            'funcspec': {
                'require': {
                    'translated': 'sll(x, ?l1) * sll(y, ?l2)',
                    'variables': ['?l1', '?l2'],
                    'variable_types': ['list Z', 'list Z'],
                },
                'ensure': {
                    'translated': 'sll(__return, ?l3)',
                    'variables': ['?l3'],
                    'variable_types': ['list Z'],
                }
            },
            'inner_assertions': []
        }
        info = collect_func_extern_info(func_data, include_helpers=True)
        assert info is not None
        assert info['func_name'] == 'sll_merge'
        assert info['has_loop_program'] is False
        assert info['require_var_count'] == 2
        assert info['inv_var_count'] == 0
        assert info['ensure_var_types'] == ['list Z']

    def test_detects_early_return_shape_when_source_is_available(self):
        func_data = {
            'function': 'demo',
            'funcspec': {
                'require': {
                    'translated': 'sll(x, ?l1)',
                    'variables': ['?l1'],
                    'variable_types': ['list Z'],
                },
                'ensure': {
                    'translated': 'sll(__return, ?l2)',
                    'variables': ['?l2'],
                    'variable_types': ['list Z'],
                }
            },
            'inner_assertions': [
                {
                    'type': 'Inv',
                    'translated': 'exists l1, ...',
                    'variables': ['l1'],
                    'variable_types': ['list Z'],
                }
            ]
        }
        source = """struct list *demo(struct list *x) {
    if (x == 0) {
        return x;
    }
    while (x) {
        if (x->next == 0) {
            return x;
        }
        x = x->next;
    }
    return x;
}
"""
        info = collect_func_extern_info(func_data, function_source=source)
        assert info is not None
        assert info['has_top_level_loop'] is True
        assert info['has_pre_loop_early_return'] is True
        assert info['has_loop_body_early_return'] is True
        assert info['needs_early_result'] is True


class TestCollectCalleeFunctions:
    def test_collects_same_file_callees(self):
        content = """int helper(void);

int target(void) {
    return helper();
}
"""
        callees = collect_callee_functions(content, [
            {'function': 'helper'},
            {'function': 'target'},
        ])
        assert callees == {'helper'}

    def test_collects_recursive_functions(self):
        content = """int recur(int n) {
    if (n <= 0) return 0;
    return recur(n - 1);
}
"""
        callees = collect_callee_functions(content, [{'function': 'recur'}])
        assert callees == {'recur'}
