import re

import pytest


_SLL_MULTI_MERGE_SRC = (
    '#include "verification_list.h"\n'
    '#include "sll_shape_def.h"\n'
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
    '    if (x == (struct list *) 0) {\n'
    '        t = sll_merge(y, z);\n'
    '        return t;\n'
    '    }\n'
    '    t = x;\n'
    '    u = t->next;\n'
    '    /*@ Inv exists v, v == t -> data && u == t -> next && t != 0 &&\n'
    '            listrep(y) * listrep(z) * listrep(u) * lseg(x@pre, t) */\n'
    '    while (u) {\n'
    '        if (y) {\n'
    '            t->next = y;\n'
    '            t = y;\n'
    '            y = y->next;\n'
    '        } else {\n'
    '            u = sll_merge(u, z);\n'
    '            t->next = u;\n'
    '            return x;\n'
    '        }\n'
    '        if (z) {\n'
    '            t->next = z;\n'
    '            t = z;\n'
    '            z = z->next;\n'
    '        } else {\n'
    '            u = sll_merge(u, y);\n'
    '            t->next = u;\n'
    '            return x;\n'
    '        }\n'
    '        t->next = u;\n'
    '        t = u;\n'
    '        u = u->next;\n'
    '    }\n'
    '    u = sll_merge(y, z);\n'
    '    t->next = u;\n'
    '    return x;\n'
    '}\n'
)


def _write_sll_multi_merge_c(tmp_path):
    path = tmp_path / "sll_multi_merge.c"
    path.write_text(_SLL_MULTI_MERGE_SRC, encoding="utf-8")
    return str(path)


_LIST_APPEND_RAW_SRC = (
    '#include "verification_list.h"\n'
    '#include "sll_shape_def.h"\n'
    '\n'
    'struct list *list_append_raw(struct list *x, struct list *y)\n'
    '/*@ Require listrep(x) * listrep(y)\n'
    '    Ensure  listrep(__return)\n'
    ' */\n'
    '{\n'
    '    if (x == 0) {\n'
    '        return y;\n'
    '    }\n'
    '    return x;\n'
    '}\n'
)


def _write_list_append_raw_c(tmp_path):
    path = tmp_path / "list_append_raw.c"
    path.write_text(_LIST_APPEND_RAW_SRC, encoding="utf-8")
    return str(path)

from GenMonads.absprog.assemble import (
    assemble_rel_lib_from_blocks,
    merge_rel_libs_into_file,
    write_assembled_rel_lib,
)
from GenMonads.absprog.gen_rel_lib import generate_rel_lib, generate_rel_lib_for_file
from GenMonads.early_return import detect_early_return_shape


def test_generate_rel_lib_uses_function_scoped_guard_names():
    func_infos = [
        {
            "func_name": "sll_rotate_left",
            "require_var_count": 1,
            "require_var_types": ["list Z"],
            "inv_var_count": 2,
            "inv_var_types": ["list Z", "list Z"],
            "ensure_var_count": 1,
            "ensure_var_types": ["list Z"],
            "coq_guard": "fun a =>\n  let '(l1, l2) := a in\n  l1 <> [].",
        },
        {
            "func_name": "sll_rotate_right",
            "require_var_count": 1,
            "require_var_types": ["list Z"],
            "inv_var_count": 3,
            "inv_var_types": ["list Z", "list Z", "list Z"],
            "ensure_var_count": 1,
            "ensure_var_types": ["list Z"],
            "coq_guard": "fun a =>\n  let '(l1, l2, l3) := a in\n  l2 <> [].",
        },
    ]

    content = generate_rel_lib("sll_rotate", func_infos)

    assert "Definition sll_rotate_left_guardP : (list Z * list Z) -> Prop :=" in content
    assert "Definition sll_rotate_right_guardP : (list Z * list Z * list Z) -> Prop :=" in content
    assert "Definition guardP :" not in content
    assert "~ (sll_rotate_left_guardP a)" in content
    assert "(sll_rotate_right_guardP a)" in content


def test_generate_rel_lib_declares_maketuple_for_multi_return():
    func_infos = [
        {
            "func_name": "sll_copy",
            "require_var_count": 1,
            "require_var_types": ["list Z"],
            "inv_var_count": 3,
            "inv_var_types": ["list Z", "list Z", "list Z"],
            "ensure_var_count": 2,
            "ensure_var_types": ["list Z", "list Z"],
            "coq_guard": "fun a =>\n  let '(l1, l2, l3) := a in\n  l2 <> [].",
        }
    ]

    content = generate_rel_lib("sll_copy", func_infos)

    assert "Definition maketuple {A B} (a : A) (b : B) : (A * B) := (a, b)." in content
    assert "Parameter MretTy : Type." in content


def test_generate_rel_lib_uses_explicit_variable_types():
    func_infos = [
        {
            "func_name": "typed_demo",
            "require_var_count": 2,
            "require_var_types": ["list Z", "Z"],
            "inv_var_count": 2,
            "inv_var_types": ["list Z", "bool"],
            "ensure_var_count": 2,
            "ensure_var_types": ["nat", "list Z"],
            "coq_guard": "fun a =>\n  let '(l1, l2) := a in\n  l2 = true.",
        }
    ]

    content = generate_rel_lib("typed_demo", func_infos)

    assert "Definition typed_demo_guardP : (list Z * bool) -> Prop :=" in content
    assert "Parameter typed_demo_M_loop_M1 : (list Z * bool) -> MONAD MretTy." in content
    assert "Parameter typed_demo_M_loop_end : MretTy -> MONAD ((nat * list Z))." in content
    assert "Definition typed_demo_M_loop : list Z -> bool -> program unit MretTy :=" in content
    assert "Parameter typed_demo_M_loop_before : list Z -> Z -> MONAD (list Z * bool)." in content
    assert "Definition typed_demo_M : list Z -> Z -> MONAD ((nat * list Z)) :=" in content


def test_generate_rel_lib_requires_explicit_variable_types():
    func_infos = [
        {
            "func_name": "missing_types",
            "require_var_count": 1,
            "inv_var_count": 1,
            "ensure_var_count": 1,
        }
    ]

    import pytest

    with pytest.raises(ValueError, match="Missing variable types"):
        generate_rel_lib("missing_types", func_infos)


def test_generate_rel_lib_uses_unit_for_no_ensure_variables():
    func_infos = [
        {
            "func_name": "dll_free",
            "require_var_count": 1,
            "require_var_types": ["list Z"],
            "inv_var_count": 1,
            "inv_var_types": ["list Z"],
            "ensure_var_count": 0,
            "ensure_var_types": [],
            "coq_guard": "fun a =>\n  a <> [].",
        }
    ]

    content = generate_rel_lib("dll_free", func_infos)

    assert "Parameter dll_free_M_loop_end : MretTy -> MONAD (unit)." in content
    assert "Definition dll_free_M : list Z -> MONAD (unit) :=" in content


def test_generate_rel_lib_includes_callee_only_function_declarations():
    func_infos = [
        {
            "func_name": "sll_merge",
            "has_loop_program": False,
            "require_var_count": 2,
            "require_var_types": ["list Z", "list Z"],
            "inv_var_count": 0,
            "inv_var_types": [],
            "ensure_var_count": 1,
            "ensure_var_types": ["list Z"],
            "coq_guard": None,
        },
        {
            "func_name": "sll_multi_merge",
            "has_loop_program": True,
            "require_var_count": 3,
            "require_var_types": ["list Z", "list Z", "list Z"],
            "inv_var_count": 4,
            "inv_var_types": ["list Z", "list Z", "list Z", "list Z"],
            "ensure_var_count": 1,
            "ensure_var_types": ["list Z"],
            "coq_guard": "fun a =>\n  let '(l1, l2, l3, l4) := a in\n  l3 <> [].",
        },
    ]

    content = generate_rel_lib("sll_multi_merge", func_infos)

    assert "Parameter sll_merge_M : list Z -> list Z -> MONAD (list Z)." in content
    assert "Parameter sll_merge_M_loop_M1" not in content
    assert "Definition sll_multi_merge_M_loop :" in content


def test_generate_rel_lib_for_multifunction_file_includes_callee_specs(tmp_path):
    output_dir = tmp_path / "coq"
    c_file = _write_sll_multi_merge_c(tmp_path)
    path = generate_rel_lib_for_file(c_file, str(output_dir))
    assert path is not None

    content = (output_dir / "sll_multi_merge_rel_lib.v").read_text(encoding="utf-8")
    assert "Parameter sll_merge_M : list Z -> list Z -> MONAD (list Z)." in content
    assert "Definition sll_multi_merge_M_loop :" in content


def test_generate_rel_lib_for_early_return_function_includes_early_result_scaffold(tmp_path):
    output_dir = tmp_path / "coq"
    c_file = _write_sll_multi_merge_c(tmp_path)
    path = generate_rel_lib_for_file(c_file, str(output_dir))
    assert path is not None

    content = (output_dir / "sll_multi_merge_rel_lib.v").read_text(encoding="utf-8")
    assert "Inductive early_result (S Ret : Type) :=" in content
    assert "Arguments Continue {S Ret} _." in content
    assert "Arguments ReturnNow {S Ret} _." in content
    assert "Definition sll_multi_merge_M_after_loop" in content
    assert "Parameter sll_multi_merge_M_loop_before : list Z -> list Z -> list Z -> MONAD (early_result" in content
    assert "Parameter sll_multi_merge_M_loop_M1 : (list Z * list Z * list Z * list Z * Z) -> MONAD MretTy." in content
    assert "Parameter sll_multi_merge_M_loop_M2 : (list Z * list Z * list Z * list Z * Z) -> MONAD (early_result (list Z * list Z * list Z * list Z * Z) (list Z))." in content
    assert "choice (assume!! (~ (sll_multi_merge_guardP a));; r <- sll_multi_merge_M_loop_M1 a ;; break (Continue r))" in content
    assert "| Continue a'' => continue a''" in content
    assert "| ReturnNow r' => break (ReturnNow r')" in content
    assert "Definition sll_multi_merge_M_loop : list Z -> list Z -> list Z -> list Z -> Z -> program unit (early_result" in content


def test_assemble_rel_lib_from_blocks_preserves_early_return_scaffold(tmp_path):
    blocks = {
        "MretTy": "Definition MretTy : Type := list Z.",
        "M_loop_before": """Definition sll_multi_merge_M_loop_before
  : list Z -> list Z -> list Z -> MONAD (early_result (list Z * list Z * list Z * list Z) (list Z)) :=
  fun l1 l2 l3 => return (Continue (l1, l2, l3, nil)).""",
        "M_1": """Definition sll_multi_merge_M_loop_M1
  : (list Z * list Z * list Z * list Z) -> MONAD MretTy :=
  fun '(_, _, _, l4) => return l4.""",
        "M_2": """Definition sll_multi_merge_M_loop_M2
  : (list Z * list Z * list Z * list Z) -> MONAD (early_result (list Z * list Z * list Z * list Z) (list Z)) :=
  fun s => return (Continue s).""",
        "M_loop_end": """Definition sll_multi_merge_M_loop_end
  : MretTy -> MONAD (list Z) :=
  fun l => return l.""",
    }

    content = assemble_rel_lib_from_blocks(
        _write_sll_multi_merge_c(tmp_path),
        "sll_multi_merge",
        blocks,
    )

    assert "Inductive early_result (S Ret : Type) :=" in content
    assert "Arguments Continue {S Ret} _." in content
    assert "Arguments ReturnNow {S Ret} _." in content
    assert "Definition sll_multi_merge_M_after_loop" in content
    assert "Parameter sll_merge_M : list Z -> list Z -> MONAD (list Z)." in content
    assert "Definition sll_multi_merge_M_loop_before" in content


# ---------------------------------------------------------------------------
# merge_rel_libs_into_file
# ---------------------------------------------------------------------------


_TWO_FUNCTION_C_SOURCE = """\
#include "verification_stdlib.h"
#include "verification_list.h"
#include "sll_shape_def.h"

struct list * f1(struct list * x)
/*@ Require listrep(x)
    Ensure listrep(__return)
 */
{
    /*@ Inv listrep(x) */
    while (x) { x = x->next; }
    return x;
}

struct list * f2(struct list * y)
/*@ Require listrep(y)
    Ensure listrep(__return)
 */
{
    /*@ Inv listrep(y) */
    while (y) { y = y->next; }
    return y;
}
"""


def _write_two_function_c_file(tmp_path) -> str:
    path = tmp_path / "two_funcs.c"
    path.write_text(_TWO_FUNCTION_C_SOURCE)
    return str(path)


def _per_func_blocks(func_name: str) -> dict:
    return {
        "MretTy": "Definition MretTy : Type := list Z.",
        "M_loop_before": (
            f"Definition {func_name}_M_loop_before\n"
            f"  : list Z -> MONAD (list Z) :=\n"
            f"  fun l1 => return l1."
        ),
        "M_1": (
            f"Definition {func_name}_M_loop_M1\n"
            f"  : list Z -> MONAD MretTy :=\n"
            f"  fun s => return nil."
        ),
        "M_2": (
            f"Definition {func_name}_M_loop_M2\n"
            f"  : list Z -> MONAD (list Z) :=\n"
            f"  fun s => return s."
        ),
        "M_loop_end": (
            f"Definition {func_name}_M_loop_end\n"
            f"  : MretTy -> MONAD (list Z) :=\n"
            f"  fun l => return l."
        ),
    }


def test_merge_rel_libs_combines_two_functions_single_file(tmp_path):
    c_file = _write_two_function_c_file(tmp_path)

    f1_path = str(tmp_path / "f1_rel_lib.v")
    f2_path = str(tmp_path / "f2_rel_lib.v")
    write_assembled_rel_lib(c_file, "f1", _per_func_blocks("f1"), f1_path)
    write_assembled_rel_lib(c_file, "f2", _per_func_blocks("f2"), f2_path)

    merged = str(tmp_path / "two_funcs_rel_lib.v")
    merge_rel_libs_into_file(c_file, [f1_path, f2_path], merged)

    with open(merged) as f:
        content = f.read()

    # All four LLM-replaceable entries for BOTH functions must be Definitions.
    for func in ("f1", "f2"):
        for suffix in ("M_loop_before", "M_loop_M1", "M_loop_M2", "M_loop_end"):
            assert f"Definition {func}_{suffix}" in content, \
                f"missing Definition {func}_{suffix} in merged output"

    # No leftover Parameter declarations for M_loop_* of either function.
    leftover = re.findall(
        r"^Parameter (?:f1|f2)_M_loop_\w+",
        content,
        flags=re.MULTILINE,
    )
    assert leftover == [], f"unexpected Parameter leftovers: {leftover}"

    # MretTy is scoped per-function; no shared Parameter/Definition MretTy.
    assert "Definition f1_MretTy : Type := list Z." in content
    assert "Definition f2_MretTy : Type := list Z." in content
    assert re.search(r"^Parameter MretTy\s*:", content, re.MULTILINE) is None
    assert re.search(r"^Definition MretTy\s*:", content, re.MULTILINE) is None


def test_merge_rel_libs_raises_on_empty_input(tmp_path):
    c_file = _write_two_function_c_file(tmp_path)
    with pytest.raises(ValueError):
        merge_rel_libs_into_file(c_file, [], str(tmp_path / "ignored.v"))


def test_merge_rel_libs_skips_missing_files(tmp_path):
    c_file = _write_two_function_c_file(tmp_path)

    f2_path = str(tmp_path / "f2_rel_lib.v")
    write_assembled_rel_lib(c_file, "f2", _per_func_blocks("f2"), f2_path)

    merged = str(tmp_path / "merged.v")
    merge_rel_libs_into_file(
        c_file,
        [str(tmp_path / "does_not_exist.v"), f2_path],
        merged,
    )

    with open(merged) as f:
        content = f.read()

    # f2 is filled in; f1 remains as Parameters.
    for suffix in ("M_loop_before", "M_loop_M1", "M_loop_M2", "M_loop_end"):
        assert f"Definition f2_{suffix}" in content
    assert "Parameter f1_M_loop_M1" in content


def test_merge_handles_back_to_back_definitions_without_blank_line(tmp_path):
    """A single per-function file may pack two Definitions without a blank line
    between them (e.g. M_loop_M1 immediately followed by M_loop_M2).  The
    merger must recognize both as separate top-level blocks.
    """
    c_file = _write_two_function_c_file(tmp_path)

    # Hand-craft a per-function file where M_loop_M1 and M_loop_M2 are adjacent
    # with no blank line between them (an observed LLM-output layout).
    f2_path = tmp_path / "f2_rel_lib.v"
    f2_path.write_text(
        "Definition MretTy : Type := list Z.\n"
        "\n"
        "Definition f2_M_loop_before\n"
        "  : list Z -> MONAD (list Z) :=\n"
        "  fun l1 => return l1.\n"
        "\n"
        "Definition f2_M_loop_M1\n"
        "  : list Z -> MONAD MretTy :=\n"
        "  fun s => return nil.\n"
        "Definition f2_M_loop_M2\n"
        "  : list Z -> MONAD (list Z) :=\n"
        "  fun s => return s.\n"
        "\n"
        "Definition f2_M_loop_end\n"
        "  : MretTy -> MONAD (list Z) :=\n"
        "  fun l => return l.\n"
    )

    merged = str(tmp_path / "merged.v")
    merge_rel_libs_into_file(c_file, [str(f2_path)], merged)

    with open(merged) as f:
        content = f.read()

    # Both Definitions must be recognized and substituted.
    assert "Definition f2_M_loop_M1" in content
    assert "Definition f2_M_loop_M2" in content
    assert "Parameter f2_M_loop_M2" not in content


# ---------------------------------------------------------------------------
# No-loop function scaffolds (Option C dispatch)
# ---------------------------------------------------------------------------


def test_detect_early_return_in_no_loop_function():
    src = """\
int f(int x) {
    if (x == 0) {
        return 1;
    }
    return 0;
}
"""
    shape = detect_early_return_shape(src)
    assert shape["has_top_level_loop"] is False
    assert shape["has_no_loop_early_return"] is True
    assert shape["needs_early_result"] is True


def test_no_early_return_in_no_loop_function():
    src = """\
int f(int x) {
    return x + 1;
}
"""
    shape = detect_early_return_shape(src)
    assert shape["has_top_level_loop"] is False
    assert shape["has_no_loop_early_return"] is False
    assert shape["needs_early_result"] is False


def test_generate_rel_lib_emits_split_scaffold_for_no_loop_early_return(tmp_path):
    src = (
        '#include "verification_list.h"\n'
        '#include "sll_shape_def.h"\n'
        '\n'
        'struct list *list_append_raw(struct list *x, struct list *y)\n'
        '/*@ Require listrep(x) * listrep(y)\n'
        '    Ensure  listrep(__return)\n'
        ' */\n'
        '{\n'
        '    if (x == 0) {\n'
        '        return y;\n'
        '    }\n'
        '    return x;\n'
        '}\n'
    )
    c_file = tmp_path / "list_append_raw.c"
    c_file.write_text(src)
    out_dir = tmp_path / "libs"

    path = generate_rel_lib_for_file(str(c_file), str(out_dir))
    assert path is not None
    content = (out_dir / "list_append_raw_rel_lib.v").read_text()

    # Split scaffold present.
    assert "Parameter list_append_raw_M_before : list Z -> list Z -> MONAD (early_result MretTy (list Z))." in content
    assert "Parameter list_append_raw_M_normal : MretTy -> MONAD (list Z)." in content
    assert "Definition list_append_raw_M : list Z -> list Z -> MONAD (list Z) :=" in content
    assert "match e with" in content
    assert "| Continue s => list_append_raw_M_normal s" in content
    assert "| ReturnNow r => return r" in content
    # No loop scaffolding for this no-loop function.
    assert "list_append_raw_M_loop" not in content


def test_synthetic_return_witness_widens_abstract_return_type(tmp_path):
    """When the Ensure has no __return predicate on a non-void function,
    the witness `r` is added to the abstract program's return type so it
    matches the emitted `return(maketuple(...))` call.
    """
    src = (
        '#include "verification_list.h"\n'
        '#include "sll_shape_def.h"\n'
        '\n'
        'long sum_list(struct list *x)\n'
        '/*@ Require listrep(x)\n'
        '    Ensure  listrep(x@pre)\n'
        ' */\n'
        '{\n'
        '    long s;\n'
        '    s = 0;\n'
        '    /*@ Inv lseg(x@pre, x) * listrep(x) */\n'
        '    while (x != 0) { s += x->data; x = x->next; }\n'
        '    return s;\n'
        '}\n'
    )
    c_file = tmp_path / "sum_list.c"
    c_file.write_text(src)
    out_dir = tmp_path / "libs"
    path = generate_rel_lib_for_file(str(c_file), str(out_dir))
    assert path is not None
    content = (out_dir / "sum_list_rel_lib.v").read_text()

    # M's return type and M_loop_end's return type both include the witness.
    assert "Definition sum_list_M : list Z -> MONAD ((list Z * Z)) :=" in content
    assert "Parameter sum_list_M_loop_end : MretTy -> MONAD ((list Z * Z))." in content


def test_synth_skeleton_imports_cross_file_callee_rel_libs(tmp_path):
    """The synthesis skeleton (used to assemble the LLM output) must include
    ``Require Import {callee}_rel_lib.`` for every callee defined in a
    sibling C file, otherwise the assembled lib references undefined names.
    """
    from GenMonads.absprog.assemble import generate_rel_lib_skeleton_for_file

    # Caller and callee live in the same directory but in different .c files.
    callee_src = (
        '#include "x.h"\n'
        '\n'
        'struct list *helper(struct list *x)\n'
        '/*@ Require listrep(x)\n'
        '    Ensure  listrep(__return)\n'
        ' */\n'
        '{\n'
        '    return x;\n'
        '}\n'
    )
    caller_src = (
        '#include "x.h"\n'
        '\n'
        'struct list *caller(struct list *x)\n'
        '/*@ Require listrep(x)\n'
        '    Ensure  listrep(__return)\n'
        ' */\n'
        '{\n'
        '    struct list *r;\n'
        '    if (x == 0) { return x; }\n'
        '    r = helper(x);\n'
        '    return r;\n'
        '}\n'
    )
    (tmp_path / "helper.c").write_text(callee_src)
    caller = tmp_path / "caller.c"
    caller.write_text(caller_src)

    content = generate_rel_lib_skeleton_for_file(str(caller))
    assert "Require Import helper_rel_lib." in content


def test_assemble_rel_lib_for_no_loop_early_return_function(tmp_path):
    """End-to-end: a loop-less, branching function (Option C scaffold) takes
    LLM-supplied ``MretTy`` / ``M_before`` / ``M_normal`` and substitutes them
    into the skeleton's matching ``Parameter`` declarations.
    """
    src = (
        '#include "verification_list.h"\n'
        '#include "sll_shape_def.h"\n'
        '\n'
        'struct list *list_append_raw(struct list *x, struct list *y)\n'
        '/*@ Require listrep(x) * listrep(y)\n'
        '    Ensure  listrep(__return)\n'
        ' */\n'
        '{\n'
        '    if (x == 0) { return y; }\n'
        '    return x;\n'
        '}\n'
    )
    c_file = tmp_path / "list_append_raw.c"
    c_file.write_text(src)

    blocks = {
        "MretTy": "Definition MretTy : Type := list Z.",
        "M_before": (
            "Definition list_append_raw_M_before\n"
            "  : list Z -> list Z -> MONAD (early_result MretTy (list Z)) :=\n"
            "  fun l1 l2 => return (ReturnNow l2)."
        ),
        "M_normal": (
            "Definition list_append_raw_M_normal\n"
            "  : MretTy -> MONAD (list Z) :=\n"
            "  fun l => return l."
        ),
    }
    content = assemble_rel_lib_from_blocks(str(c_file), "list_append_raw", blocks)

    # All three LLM-provided Parameters become Definitions.
    assert "Definition MretTy : Type := list Z." in content
    assert "Parameter MretTy : Type." not in content
    assert "Definition list_append_raw_M_before" in content
    assert "Parameter list_append_raw_M_before" not in content
    assert "Definition list_append_raw_M_normal" in content
    assert "Parameter list_append_raw_M_normal" not in content
    # The composing ``M`` definition is from the skeleton and is preserved.
    assert "Definition list_append_raw_M : list Z -> list Z -> MONAD (list Z) :=" in content


def test_collect_synthesis_context_for_no_loop_function(tmp_path):
    """Context builder produces ``no_loop_early_return`` template_case and
    the matching ``required_components`` / ``must_define`` for an Option-C
    function.
    """
    from GenMonads.absprog.context import collect_synthesis_context

    c_file = _write_list_append_raw_c(tmp_path)

    ctx = collect_synthesis_context(c_file)
    cf = ctx["control_flow"]
    assert cf["template_case"] == "no_loop_early_return"
    assert cf["required_components"] == ["MretTy", "M_before", "M_normal"]
    assert ctx["generation_policy"]["must_define"] == [
        "MretTy",
        "list_append_raw_M_before",
        "list_append_raw_M_normal",
    ]
    sigs = cf["prompt_signatures"]
    assert "M_before" in sigs
    assert "M_normal" in sigs


def test_single_element_state_type_is_parenthesized_in_type_applications(tmp_path):
    """A function whose invariant has a single ``list Z`` produces state
    type ``list Z`` (without enclosing parens).  When the state type is
    used as an argument to ``MONAD`` or ``CntOrBrk`` it must be parenthesized
    or Coq parses ``MONAD list Z`` as ``(MONAD list) Z``.
    """
    src = (
        '#include "verification_list.h"\n'
        '#include "sll_shape_def.h"\n'
        '\n'
        'void free_all(struct list *x)\n'
        '/*@ Require listrep(x)\n'
        '    Ensure  emp\n'
        ' */\n'
        '{\n'
        '    /*@ Inv listrep(x) */\n'
        '    while (x != 0) { x = x->next; }\n'
        '}\n'
    )
    c_file = tmp_path / "free_all.c"
    c_file.write_text(src)
    out_dir = tmp_path / "libs"

    path = generate_rel_lib_for_file(str(c_file), str(out_dir))
    assert path is not None
    content = (out_dir / "free_all_rel_lib.v").read_text()

    # No bare ``MONAD list Z`` or ``CntOrBrk list Z ...`` — single-element
    # list state must be wrapped when used as a type-application argument.
    assert "MONAD list Z" not in content
    assert "CntOrBrk list Z" not in content
    assert "MONAD (list Z)" in content
    assert "CntOrBrk (list Z)" in content


def test_generate_rel_lib_emits_simple_parameter_for_no_branch_function(tmp_path):
    src = (
        '#include "sll_shape_def.h"\n'
        '\n'
        'struct list *f(struct list *x)\n'
        '/*@ Require listrep(x)\n'
        '    Ensure  listrep(__return)\n'
        ' */\n'
        '{\n'
        '    return x;\n'
        '}\n'
    )
    c_file = tmp_path / "f.c"
    c_file.write_text(src)
    out_dir = tmp_path / "libs"

    path = generate_rel_lib_for_file(str(c_file), str(out_dir))
    assert path is not None
    content = (out_dir / "f_rel_lib.v").read_text()

    assert "(* ---- Abstract program declaration for f ---- *)" in content
    assert re.search(r"^Parameter f_M : list Z -> MONAD \(list Z\)\.$", content, re.MULTILINE)
    assert "f_M_before" not in content
    assert "f_M_normal" not in content
    assert "f_M_loop" not in content


def test_generate_rel_lib_imports_sibling_rel_lib_for_cross_file_callee(tmp_path):
    helper_c = tmp_path / "list_tail.c"
    helper_c.write_text(
        '#include "h.h"\n'
        'struct list *list_tail(struct list *x)\n'
        '/*@ Require listrep(x)\n'
        '    Ensure  listrep(__return)\n'
        ' */\n'
        '{\n'
        '    return x;\n'
        '}\n'
    )

    caller_c = tmp_path / "list_append_raw.c"
    caller_c.write_text(
        '#include "h.h"\n'
        'struct list *list_append_raw(struct list *x, struct list *y)\n'
        '/*@ Require listrep(x) * listrep(y)\n'
        '    Ensure  listrep(__return)\n'
        ' */\n'
        '{\n'
        '    struct list *tail;\n'
        '    if (x == 0) { return y; }\n'
        '    tail = list_tail(x);\n'
        '    tail->next = y;\n'
        '    return x;\n'
        '}\n'
    )

    out_dir = tmp_path / "libs"
    path = generate_rel_lib_for_file(str(caller_c), str(out_dir))
    assert path is not None
    content = (out_dir / "list_append_raw_rel_lib.v").read_text()

    assert "Require Import list_tail_rel_lib." in content
    assert "Parameter list_tail_M" not in content


def test_generate_rel_lib_skips_callees_without_sibling_c_file(tmp_path):
    caller_c = tmp_path / "list_append_raw.c"
    caller_c.write_text(
        '#include "h.h"\n'
        'struct list *list_append_raw(struct list *x, struct list *y)\n'
        '/*@ Require listrep(x) * listrep(y)\n'
        '    Ensure  listrep(__return)\n'
        ' */\n'
        '{\n'
        '    struct list *tail;\n'
        '    tail = list_tail(x);\n'
        '    return tail;\n'
        '}\n'
    )

    out_dir = tmp_path / "libs"
    path = generate_rel_lib_for_file(str(caller_c), str(out_dir))
    assert path is not None
    content = (out_dir / "list_append_raw_rel_lib.v").read_text()

    assert "Require Import list_tail_rel_lib" not in content
    assert "Parameter list_tail_M" not in content
