import re

import pytest


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


def test_generate_rel_lib_staterr_changes_only_the_header():
    """The staterr backend swaps the monad header but leaves the body identical."""
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
    ]

    rel = generate_rel_lib("sll_rotate", func_infos, monad="staterel")
    err = generate_rel_lib("sll_rotate", func_infos, monad="staterr")

    # staterel header (default) vs staterr header.
    assert "From MonadLib Require Import MonadLib." in rel
    assert "Export StateRelMonad." in rel
    assert "From FP Require Import" not in rel

    # staterr imports ONLY MonadErr.StateRelMonadErr (not the aggregated MonadLib,
    # which would make program/bind/MONAD ambiguous between the two monads).
    assert "From FP Require Import PartialOrder_Setoid BourbakiWitt." in err
    assert "From MonadLib.MonadErr Require Import StateRelMonadErr." in err
    assert "Import MonadNotation." in err
    assert "From MonadLib Require Export MonadLib." not in err
    assert "Export StateRelMonadErr." not in err
    assert "Export StateRelMonad." not in err  # not the relational module

    # Everything below the monad header must be byte-identical.
    body_rel = rel.split("Local Open Scope monad.", 1)[1]
    body_err = err.split("Local Open Scope monad.", 1)[1]
    assert body_rel == body_err


def test_generate_rel_lib_rejects_unknown_monad():
    func_infos = [
        {
            "func_name": "f",
            "require_var_count": 1,
            "require_var_types": ["list Z"],
            "inv_var_count": 1,
            "inv_var_types": ["list Z"],
            "ensure_var_count": 1,
            "ensure_var_types": ["list Z"],
            "coq_guard": "fun a => True.",
        },
    ]
    with pytest.raises(ValueError):
        generate_rel_lib("f", func_infos, monad="bogus")


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


def test_generate_rel_lib_topologically_orders_callees_before_callers():
    """Coq is top-down: any block that references `<name>_M` must come after
    the block that introduces it.  ``generate_rel_lib`` takes an optional
    in-file ``call_graph`` and topologically sorts ``func_infos`` so callees
    precede callers, regardless of source order.
    """
    # Caller appears first in source order; without a call_graph, source
    # order would put the caller's Definition before the callee's Parameter.
    func_infos = [
        {
            "func_name": "caller",
            "has_loop_program": False,
            "has_no_loop_early_return": True,
            "require_var_count": 2,
            "require_var_types": ["list Z", "list Z"],
            "inv_var_count": 0,
            "inv_var_types": [],
            "ensure_var_count": 1,
            "ensure_var_types": ["list Z"],
            "coq_guard": None,
        },
        {
            "func_name": "helper",
            "has_loop_program": False,
            "has_no_loop_early_return": False,
            "require_var_count": 1,
            "require_var_types": ["list Z"],
            "inv_var_count": 0,
            "inv_var_types": [],
            "ensure_var_count": 1,
            "ensure_var_types": ["list Z"],
            "coq_guard": None,
        },
    ]
    call_graph = {"caller": {"helper"}, "helper": set()}
    content = generate_rel_lib("demo", func_infos, call_graph=call_graph)
    helper_pos = content.index("Parameter helper_M")
    caller_pos = content.index("Definition caller_M :")
    assert helper_pos < caller_pos, (
        "helper Parameter must precede caller Definition; "
        f"got helper at {helper_pos}, caller at {caller_pos}"
    )


def test_generate_rel_lib_orders_same_file_target_callee_before_caller(tmp_path):
    """When two same-file targets call each other (`caller -> callee` with
    callee being a loop-bearing helper), the callee must be emitted before
    the caller in the synthesized lib.  Regression for the
    ``glibc_slist_multi_rev.c`` failure where ``rev_append_local`` (loop)
    was emitted after ``glibc_slist_clean_multi_rev`` (straight-line)
    causing an unresolved-reference error at Coq check time.
    """
    src = (
        '#include "sll_shape_def.h"\n'
        '\n'
        'static struct list *callee_loop(struct list *src)\n'
        '/*@ Require listrep(src)\n'
        '    Ensure  listrep(__return)\n'
        ' */\n'
        '{\n'
        '    /*@ Inv listrep(src) */\n'
        '    while (src != 0) { src = src->next; }\n'
        '    return src;\n'
        '}\n'
        '\n'
        'struct list *caller_straight(struct list *x)\n'
        '/*@ Require listrep(x)\n'
        '    Ensure  listrep(__return)\n'
        ' */\n'
        '{\n'
        '    return callee_loop(x);\n'
        '}\n'
    )
    c_file = tmp_path / "demo.c"
    c_file.write_text(src, encoding="utf-8")
    out_dir = tmp_path / "libs"
    path = generate_rel_lib_for_file(str(c_file), str(out_dir))
    content = (out_dir / "demo_rel_lib.v").read_text()
    callee_pos = content.find("callee_loop")
    caller_pos = content.find("caller_straight")
    assert callee_pos != -1 and caller_pos != -1
    assert callee_pos < caller_pos, \
        f"callee must precede caller; callee at {callee_pos}, caller at {caller_pos}"


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


def test_merge_rel_libs_keeps_bare_mretty_when_skeleton_uses_bare(tmp_path):
    """When the file has only one MretTy-using function (e.g. one loop + one
    straight-line target), the skeleton emits bare ``Parameter MretTy :
    Type.``  The merger must not rename per-function definitions to
    ``{func}_MretTy`` in that case — doing so leaves the merged file
    referencing an undeclared scoped name alongside the skeleton's bare
    ``MretTy`` references.  Regression for ``glibc_slist_multi_rev.c``.
    """
    src = (
        '#include "sll_shape_def.h"\n'
        '\n'
        'static struct list *callee_loop(struct list *src)\n'
        '/*@ Require listrep(src)\n'
        '    Ensure  listrep(__return)\n'
        ' */\n'
        '{\n'
        '    /*@ Inv listrep(src) */\n'
        '    while (src != 0) { src = src->next; }\n'
        '    return src;\n'
        '}\n'
        '\n'
        'struct list *caller_straight(struct list *x)\n'
        '/*@ Require listrep(x)\n'
        '    Ensure  listrep(__return)\n'
        ' */\n'
        '{\n'
        '    return callee_loop(x);\n'
        '}\n'
    )
    c_file = str(tmp_path / "demo.c")
    with open(c_file, "w", encoding="utf-8") as f:
        f.write(src)

    callee_blocks = {
        "MretTy": "Definition MretTy : Type := list Z.",
        "M_loop_before": (
            "Definition callee_loop_M_loop_before\n"
            "  : list Z -> MONAD (list Z) :=\n"
            "  fun l1 => return l1."
        ),
        "M_1": (
            "Definition callee_loop_M_loop_M1\n"
            "  : list Z -> MONAD MretTy :=\n"
            "  fun s => return s."
        ),
        "M_2": (
            "Definition callee_loop_M_loop_M2\n"
            "  : list Z -> MONAD (list Z) :=\n"
            "  fun s => return s."
        ),
        "M_loop_end": (
            "Definition callee_loop_M_loop_end\n"
            "  : MretTy -> MONAD (list Z) :=\n"
            "  fun l => return l."
        ),
    }
    callee_path = str(tmp_path / "callee_loop_rel_lib.v")
    write_assembled_rel_lib(c_file, "callee_loop", callee_blocks, callee_path)

    merged_path = str(tmp_path / "demo_rel_lib.v")
    merge_rel_libs_into_file(c_file, [callee_path], merged_path)
    with open(merged_path) as f:
        content = f.read()

    # No scoped `callee_loop_MretTy` should appear anywhere — the skeleton
    # uses bare `MretTy` here, so renaming would dangle the scoped name.
    assert "callee_loop_MretTy" not in content, \
        f"merger created undeclared scoped MretTy:\n{content}"
    # The skeleton's `Parameter MretTy : Type.` should be replaced by the
    # callee's `Definition MretTy : Type := list Z.`
    assert "Definition MretTy : Type := list Z." in content
    assert re.search(r"^Parameter MretTy\s*:", content, re.MULTILINE) is None


def test_merge_rel_libs_substitutes_straight_line_target_M(tmp_path):
    """Straight-line targets emit a single ``Parameter {fn}_M : ...`` in the
    skeleton.  The merger must extract the LLM-supplied
    ``Definition {fn}_M := ...`` and substitute it — not skip it for missing
    ``_M_loop_*`` suffixes.  Regression for the ``glibc_slist_multi_rev.c``
    case where ``glibc_slist_clean_multi_rev_M`` stayed as a Parameter even
    though synthesis had passed.
    """
    src = (
        '#include "sll_shape_def.h"\n'
        '\n'
        'static struct list *callee_loop(struct list *src)\n'
        '/*@ Require listrep(src)\n'
        '    Ensure  listrep(__return)\n'
        ' */\n'
        '{\n'
        '    /*@ Inv listrep(src) */\n'
        '    while (src != 0) { src = src->next; }\n'
        '    return src;\n'
        '}\n'
        '\n'
        'struct list *caller_straight(struct list *x)\n'
        '/*@ Require listrep(x)\n'
        '    Ensure  listrep(__return)\n'
        ' */\n'
        '{\n'
        '    return callee_loop(x);\n'
        '}\n'
    )
    c_file = str(tmp_path / "demo.c")
    with open(c_file, "w", encoding="utf-8") as f:
        f.write(src)

    callee_blocks = {
        "MretTy": "Definition MretTy : Type := list Z.",
        "M_loop_before": (
            "Definition callee_loop_M_loop_before\n"
            "  : list Z -> MONAD (list Z) :=\n"
            "  fun l1 => return l1."
        ),
        "M_1": (
            "Definition callee_loop_M_loop_M1\n"
            "  : list Z -> MONAD MretTy :=\n"
            "  fun s => return s."
        ),
        "M_2": (
            "Definition callee_loop_M_loop_M2\n"
            "  : list Z -> MONAD (list Z) :=\n"
            "  fun s => return s."
        ),
        "M_loop_end": (
            "Definition callee_loop_M_loop_end\n"
            "  : MretTy -> MONAD (list Z) :=\n"
            "  fun l => return l."
        ),
    }
    callee_path = str(tmp_path / "callee_loop_rel_lib.v")
    write_assembled_rel_lib(c_file, "callee_loop", callee_blocks, callee_path)

    # The caller's per-function lib comes straight from the skeleton with
    # the LLM's `_M` Definition substituted in.
    caller_skeleton_substituted = (
        # Stand-in for the merged synthesizer output: include the LLM
        # Definition with its `_M` suffix so the merger extracts it.
        "Require Import Coq.Lists.List.\n"
        "From MonadLib Require Import MonadLib.\n\n"
        "Definition caller_straight_M : list Z -> MONAD (list Z) :=\n"
        "  fun l1 => callee_loop_M l1 nil.\n"
    )
    caller_path = str(tmp_path / "caller_straight_rel_lib.v")
    with open(caller_path, "w", encoding="utf-8") as f:
        f.write(caller_skeleton_substituted)

    merged_path = str(tmp_path / "demo_rel_lib.v")
    merge_rel_libs_into_file(c_file, [callee_path, caller_path], merged_path)
    with open(merged_path) as f:
        content = f.read()

    assert re.search(
        r"^Definition caller_straight_M\b", content, re.MULTILINE
    ), "straight-line `_M` Definition was not substituted into the merged lib"
    assert re.search(
        r"^Parameter caller_straight_M\b", content, re.MULTILINE
    ) is None, "stale Parameter still present after merge"


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


# ---------------------------------------------------------------------------
# Forest scaffold (task #20) — multi-loop codegen with mechanical nesting.
# ---------------------------------------------------------------------------


from GenMonads.absprog.gen_rel_lib import (
    generate_forest_func_block,
    generate_rel_lib_for_file,
)


def _leaf(idx, parent=None, state="(list Z * Z)", guard=None):
    return {
        "loop_index": idx,
        "parent": parent,
        "children": [],
        "inv_index": idx,
        "inv_var_types": ["list Z", "Z"],
        "state_type": state,
        "coq_guard": guard or "",
        "guard_available": bool(guard),
        "keyword": "while",
    }


def _parent(idx, children, state="(list Z * Z)", guard=None, parent=None):
    return {
        "loop_index": idx,
        "parent": parent,
        "children": list(children),
        "inv_index": idx,
        "inv_var_types": ["list Z", "Z"],
        "state_type": state,
        "coq_guard": guard or "",
        "guard_available": bool(guard),
        "keyword": "while",
    }


class TestForestFuncBlock:
    def test_two_level_nest_emits_per_loop_scaffolds(self):
        templates = [
            _parent(0, children=[1]),
            _leaf(1, parent=0),
        ]
        block = generate_forest_func_block(
            "f", ["list Z"], "(list Z * Z)", templates,
        )
        # Inner loop (loop2) emitted first.
        i_loop2_M1 = block.find("f_M_loop2_M1")
        i_loop1_M1 = block.find("f_M_loop1_M1")
        assert 0 <= i_loop2_M1 < i_loop1_M1
        # Leaf has Parameter M2.
        assert "Parameter f_M_loop2_M2 :" in block
        # Parent emits boundary holes + mechanical M2.
        assert "Parameter f_M_loop1_to_inner_2 : (list Z * Z) -> MONAD (list Z * Z)." in block
        assert "Parameter f_M_loop1_after_inner_2 : (list Z * Z) -> MretTy -> MONAD (list Z * Z)." in block
        assert "Definition f_M_loop1_M2 : (list Z * Z) -> MONAD (list Z * Z) :=" in block
        # Mechanical sequencing: to_inner ;; inner_aux ;; after_inner.
        assert "s' <- f_M_loop1_to_inner_2 a;;" in block
        assert "r  <- f_M_loop2_aux s';;" in block
        assert "f_M_loop1_after_inner_2 a r." in block
        # Per-loop guard + body + aux.
        assert "Definition f_loop1_guardP : (list Z * Z) -> Prop." not in block  # no semi
        assert "Parameter f_loop1_guardP : (list Z * Z) -> Prop." in block
        assert "Parameter f_loop2_guardP : (list Z * Z) -> Prop." in block
        assert "Definition f_M_loop1_body" in block
        assert "Definition f_M_loop2_body" in block
        assert "repeat_break f_M_loop1_body" in block
        assert "repeat_break f_M_loop2_body" in block
        # Top-level composition: only loop1 has before/end.
        assert "Parameter f_M_loop1_before : list Z -> MONAD (list Z * Z)." in block
        assert "Parameter f_M_loop1_end : MretTy -> MONAD ((list Z * Z))." in block
        assert "Parameter f_M_loop2_before" not in block
        assert "Parameter f_M_loop2_end" not in block
        # Definition f_M composes the outermost loop only.
        assert "s1 <- f_M_loop1_before l1;;" in block
        assert "r1 <- f_M_loop1_aux s1;;" in block
        assert "f_M_loop1_end r1." in block
        # No ResTy for single-top-level case.
        assert "ResTy" not in block

    def test_guard_definition_inlined_when_available(self):
        templates = [
            _parent(0, children=[1], guard="fun a => let '(l, s) := a in l <> []"),
            _leaf(1, parent=0, guard="fun a => let '(l, s) := a in l <> []"),
        ]
        block = generate_forest_func_block(
            "f", ["list Z"], "(list Z * Z)", templates,
        )
        assert "Definition f_loop1_guardP : (list Z * Z) -> Prop :=" in block
        assert "Definition f_loop2_guardP : (list Z * Z) -> Prop :=" in block
        assert "Guard could not be generated" not in block

    def test_sequential_top_level_loops_emit_restty_and_mid(self):
        templates = [
            _leaf(0),  # top-level loop 1
            _leaf(1),  # top-level loop 2 — sibling
        ]
        block = generate_forest_func_block(
            "f", ["list Z"], "(list Z * Z)", templates,
        )
        # An intermediate ResTy Parameter is declared for loop1 only (the
        # non-last top-level).
        assert "Parameter f_loop1_ResTy : Type." in block
        assert "Parameter f_loop2_ResTy" not in block
        # loop1_end returns the intermediate ResTy; loop2_end returns T.
        assert "Parameter f_M_loop1_end : MretTy -> MONAD f_loop1_ResTy." in block
        assert "Parameter f_M_loop2_end : MretTy -> MONAD ((list Z * Z))." in block
        # loop2_before takes the previous loop's ResTy.
        assert "Parameter f_M_loop2_before : f_loop1_ResTy -> MONAD (list Z * Z)." in block
        # Composition threads t1 through.
        assert "t1 <- f_M_loop1_end r1;;" in block
        assert "s2 <- f_M_loop2_before t1;;" in block
        assert "r2 <- f_M_loop2_aux s2;;" in block
        assert "f_M_loop2_end r2." in block

    def test_three_level_nest_emits_children_before_parents(self):
        templates = [
            _parent(0, children=[1]),
            _parent(1, children=[2], parent=0),
            _leaf(2, parent=1),
        ]
        block = generate_forest_func_block(
            "f", ["list Z"], "(list Z * Z)", templates,
        )
        # All three loops appear, in bottom-up order.
        p3 = block.find("f_M_loop3_M1")
        p2 = block.find("f_M_loop2_M1")
        p1 = block.find("f_M_loop1_M1")
        assert 0 <= p3 < p2 < p1
        # Innermost is a leaf.
        assert "Parameter f_M_loop3_M2 :" in block
        # Middle loop has mechanical M2 calling loop3.
        assert "Definition f_M_loop2_M2 :" in block
        assert "r  <- f_M_loop3_aux s';;" in block
        # Outermost has mechanical M2 calling loop2.
        assert "Definition f_M_loop1_M2 :" in block
        assert "r  <- f_M_loop2_aux s';;" in block

    def test_declare_mretty_emits_parameter_when_requested(self):
        templates = [_parent(0, children=[1]), _leaf(1, parent=0)]
        block = generate_forest_func_block(
            "f", ["list Z"], "(list Z * Z)", templates,
            mretty_name="f_MretTy", declare_mretty=True,
        )
        assert "Parameter f_MretTy : Type." in block
        # All references use the scoped name.
        assert "MONAD f_MretTy" in block
        assert "f_M_loop2_M1 : (list Z * Z) -> MONAD f_MretTy." in block

    def test_empty_loop_templates_returns_empty(self):
        assert generate_forest_func_block("f", ["list Z"], "list Z", []) == ""


class TestForestEndToEnd:
    def test_generate_rel_lib_for_nested_real_file(self, tmp_path):
        """End-to-end: the real nested file produces a forest scaffold with
        the expected structural markers (per-loop scaffolds + mechanical M2)."""
        out_dir = tmp_path / "lib"
        out_path = generate_rel_lib_for_file(
            "shape_invdataset/Glibc_slist_clean_iter/glibc_slist_iter_back_2.c",
            str(out_dir),
        )
        assert out_path is not None
        content = (out_dir / "glibc_slist_iter_back_2_rel_lib.v").read_text()
        # Forest banner is emitted.
        assert "(loop forest: 2 loops, 1 top-level)" in content
        # Per-loop M1 + mechanical outer M2.
        fn = "glibc_slist_clean_iter_back_2"
        assert f"Parameter {fn}_M_loop2_M1 :" in content
        assert f"Parameter {fn}_M_loop2_M2 :" in content  # leaf
        assert f"Parameter {fn}_M_loop1_M1 :" in content
        assert f"Parameter {fn}_M_loop1_to_inner_2 :" in content
        assert f"Parameter {fn}_M_loop1_after_inner_2 :" in content
        assert f"Definition {fn}_M_loop1_M2 :" in content
        assert f"r  <- {fn}_M_loop2_aux s';;" in content
        # Top-level composition.
        assert f"Definition {fn}_M :" in content
        assert f"r1 <- {fn}_M_loop1_aux s1;;" in content
        assert f"{fn}_M_loop1_end r1." in content


# ---------------------------------------------------------------------------
# Forest assemble (task #21) — loop-indexed Parameter replacement.
# ---------------------------------------------------------------------------


from GenMonads.absprog.assemble import (
    _is_llm_parameter_name,
    assemble_rel_lib_from_blocks,
)
from GenMonads.absprog.parse_coq import (
    _component_parameter_name,
    parse_synthesized_components,
)


class TestForestComponentNaming:
    def test_loop_indexed_components_pass_through_as_suffix(self):
        # Unknown components fall through to the verbatim suffix path.
        assert _component_parameter_name("M_loop1_M1", "f") == "f_M_loop1_M1"
        assert _component_parameter_name("M_loop2_M2", "f") == "f_M_loop2_M2"
        assert _component_parameter_name("M_loop1_to_inner_2", "f") == "f_M_loop1_to_inner_2"
        assert _component_parameter_name(
            "M_loop1_after_inner_2", "f"
        ) == "f_M_loop1_after_inner_2"
        assert _component_parameter_name("M_loop1_before", "f") == "f_M_loop1_before"
        assert _component_parameter_name("M_loop1_end", "f") == "f_M_loop1_end"
        assert _component_parameter_name("loop1_guardP", "f") == "f_loop1_guardP"
        assert _component_parameter_name("loop1_ResTy", "f") == "f_loop1_ResTy"
        # Known single-loop components still mapped to their canonical suffix.
        assert _component_parameter_name("M_1", "f") == "f_M_loop_M1"
        assert _component_parameter_name("M_loop_before", "f") == "f_M_loop_before"


class TestLLMParameterDetector:
    def test_recognises_forest_indexed_names(self):
        assert _is_llm_parameter_name("f_M_loop1_M1")
        assert _is_llm_parameter_name("f_M_loop10_M2")
        assert _is_llm_parameter_name("f_M_loop1_before")
        assert _is_llm_parameter_name("f_M_loop2_end")
        assert _is_llm_parameter_name("f_M_loop1_to_inner_2")
        assert _is_llm_parameter_name("f_M_loop3_after_inner_5")
        assert _is_llm_parameter_name("f_loop1_guardP")
        assert _is_llm_parameter_name("f_loop2_ResTy")
        # Still accepts the existing literal suffixes.
        assert _is_llm_parameter_name("f_M_loop_M1")
        assert _is_llm_parameter_name("f_M_loop_end")
        assert _is_llm_parameter_name("f_M_normal")
        assert _is_llm_parameter_name("f_guardP")
        assert _is_llm_parameter_name("f_M")

    def test_rejects_non_llm_names(self):
        assert not _is_llm_parameter_name("f_M_loop_aux")
        assert not _is_llm_parameter_name("f_M_loop1_aux")
        assert not _is_llm_parameter_name("f_M_loop_body")
        assert not _is_llm_parameter_name("MretTy")
        assert not _is_llm_parameter_name("maketuple")


class TestForestAssembler:
    def test_assembler_replaces_forest_parameters(self, tmp_path):
        """End-to-end: feed synthesized Definitions for every forest component
        of glibc_slist_iter_back_2 and verify the assembler replaces each
        Parameter line with the supplied Definition."""
        fn = "glibc_slist_clean_iter_back_2"
        response = "\n".join([
            "Definition MretTy : Type := (list Z * list Z * Z).",
            f"Definition {fn}_loop1_guardP : (list Z * Z) -> Prop := fun a => let '(l, s) := a in l <> nil.",
            f"Definition {fn}_loop2_guardP : (list Z * Z) -> Prop := fun a => let '(l, s) := a in l <> nil.",
            f"Definition {fn}_M_loop1_M1 : (list Z * Z) -> MONAD MretTy := fun a => let '(l, s) := a in return (nil, l, s).",
            f"Definition {fn}_M_loop2_M1 : (list Z * Z) -> MONAD MretTy := fun a => let '(l, s) := a in return (nil, l, s).",
            f"Definition {fn}_M_loop2_M2 : (list Z * Z) -> MONAD (list Z * Z) := fun a => return a.",
            f"Definition {fn}_M_loop1_to_inner_2 : (list Z * Z) -> MONAD (list Z * Z) := fun a => return a.",
            f"Definition {fn}_M_loop1_after_inner_2 : (list Z * Z) -> MretTy -> MONAD (list Z * Z) := fun a r => return a.",
            f"Definition {fn}_M_loop1_before : list Z -> MONAD (list Z * Z) := fun l1 => return (l1, 0).",
            f"Definition {fn}_M_loop1_end : MretTy -> MONAD ((list Z * Z)) := fun r => let '(processed, _, s) := r in return (processed, s).",
        ])
        required = [
            "MretTy",
            "loop1_guardP", "loop2_guardP",
            "M_loop1_M1", "M_loop2_M1", "M_loop2_M2",
            "M_loop1_to_inner_2", "M_loop1_after_inner_2",
            "M_loop1_before", "M_loop1_end",
        ]
        blocks = parse_synthesized_components(response, fn, required=required)
        assert sorted(blocks.keys()) == sorted(required)

        content = assemble_rel_lib_from_blocks(
            "shape_invdataset/Glibc_slist_clean_iter/glibc_slist_iter_back_2.c",
            fn, blocks,
            sibling_dirs=["shape_invdataset/Glibc_slist_clean_iter"],
        )
        # Every targeted Parameter line is gone.
        for name in [
            f"{fn}_M_loop1_M1", f"{fn}_M_loop2_M1", f"{fn}_M_loop2_M2",
            f"{fn}_M_loop1_to_inner_2", f"{fn}_M_loop1_after_inner_2",
            f"{fn}_loop1_guardP", f"{fn}_loop2_guardP",
            f"{fn}_M_loop1_before", f"{fn}_M_loop1_end",
        ]:
            assert re.search(rf"^Parameter {re.escape(name)}\b", content, re.MULTILINE) is None, \
                f"Parameter {name} still present"
            assert re.search(rf"Definition {re.escape(name)}\b", content), \
                f"Definition {name} missing"


class TestForestRelCAndLibAgree:
    """End-to-end coherence: every ``{fn}_M*`` symbol the generated ``_rel.c``
    references must be declared (Parameter or Definition) in the matching
    forest ``_rel_lib.v``.  Catches drift between
    ``translate_c_file.replace_inner_assertions_*`` /
    ``generate_coq_blocks`` and ``gen_rel_lib.generate_forest_func_block``."""

    def test_nested_file_rel_c_symbols_resolve_in_forest_lib(self, tmp_path):
        from GenMonads.translate_c_file import translate_c_file
        from GenMonads.absprog.gen_rel_lib import generate_rel_lib_for_file

        c_file = "shape_invdataset/Glibc_slist_clean_iter/glibc_slist_iter_back_2.c"
        rel_c_path = tmp_path / "rel.c"
        lib_dir = tmp_path / "lib"
        assert translate_c_file(c_file, str(rel_c_path))
        assert generate_rel_lib_for_file(c_file, str(lib_dir)) is not None

        rel_c = rel_c_path.read_text()
        lib_text = (lib_dir / "glibc_slist_iter_back_2_rel_lib.v").read_text()

        fn = "glibc_slist_clean_iter_back_2"
        # Symbols the rel.c references — those starting with the function
        # prefix and ending after an ``_M*`` segment (M_loop1, M_loop1_end,
        # M itself).  Filter out the ``_M`` of helper names we don't model.
        refs = set(re.findall(rf"\b{fn}_M(?:_loop\d+(?:_end)?)?\b", rel_c))
        assert refs, "expected to find at least one abstract-program reference"

        # Each ref must be declared as a top-level Parameter or Definition.
        declared = set(re.findall(
            rf"^(?:Parameter|Definition)\s+({fn}_M(?:_loop\d+(?:_end)?)?)\b",
            lib_text, re.MULTILINE,
        ))
        missing = refs - declared
        assert not missing, (
            f"_rel.c references symbols not in forest lib: {sorted(missing)}\n"
            f"  declared = {sorted(declared)}"
        )

    def test_nested_file_extern_coq_block_lists_per_loop_programs(self, tmp_path):
        """The Extern Coq block in the ``_rel.c`` must mention per-loop
        ``_M_loop{k}`` declarations (one per loop) and an ``_M_loop{k}_end``
        for the root loop — not the single-loop ``_M_loop`` / ``_M_loop_end``
        which don't exist in the forest lib."""
        from GenMonads.translate_c_file import translate_c_file

        c_file = "shape_invdataset/Glibc_slist_clean_iter/glibc_slist_iter_back_2.c"
        out = tmp_path / "rel.c"
        assert translate_c_file(c_file, str(out))
        text = out.read_text()
        fn = "glibc_slist_clean_iter_back_2"
        extern = text.split("/*@ Extern Coq", 2)[2].split("*/", 1)[0]

        # Per-loop declarations are present.
        assert f"{fn}_M_loop1:" in extern
        assert f"{fn}_M_loop2:" in extern
        assert f"{fn}_M_loop1_end:" in extern
        # The single-loop names that used to appear unconditionally are gone.
        assert f"{fn}_M_loop:" not in extern
        assert f"{fn}_M_loop_end:" not in extern

    def test_per_inv_programs_thread_loop_indices_into_invariants(self, tmp_path):
        """Each ``Inv`` in the ``_rel.c`` must reference its own loop's
        ``_M_loop{k}`` (not all the same name)."""
        from GenMonads.translate_c_file import translate_c_file

        c_file = "shape_invdataset/Glibc_slist_clean_iter/glibc_slist_iter_back_2.c"
        out = tmp_path / "rel.c"
        assert translate_c_file(c_file, str(out))
        text = out.read_text()
        invs = re.findall(r"/\*@\s*Inv .*?\*/", text, re.DOTALL)
        assert len(invs) == 2, f"expected 2 Inv blocks, got {len(invs)}"
        # Outer Inv references loop1; inner references loop2.
        assert "_M_loop1(" in invs[0] and "_M_loop2(" not in invs[0]
        assert "_M_loop2(" in invs[1] and "_M_loop1(" not in invs[1]
        # Both reference the root loop's _M_loop1_end.
        assert all("_M_loop1_end" in iv for iv in invs)


class TestForestNoArgsEdge:
    def test_forest_func_with_no_require_args_emits_no_lambda(self):
        templates = [_parent(0, children=[1]), _leaf(1, parent=0)]
        block = generate_forest_func_block(
            "f", [], "(list Z * Z)", templates,
        )
        # No "fun tt =>" smell.
        assert "fun tt =>" not in block
        # No-args function applies M_loop1_before with no arguments.
        assert "Definition f_M : MONAD ((list Z * Z))" in block
        assert "s1 <- f_M_loop1_before;;" in block
        # ``Parameter f_M_loop1_before`` is bare ``MONAD ...`` for 0 args.
        assert "Parameter f_M_loop1_before : MONAD (list Z * Z)." in block


class TestForestScaffoldSketch:
    def test_selected_scaffold_points_at_skeleton_file_in_forest_mode(self):
        """In workdir-mode the Selected Scaffold section no longer embeds
        per-loop sketches (the agent reads the actual ``skeleton/X.v``
        instead).  Stale single-loop names must not leak into the section."""
        from GenMonads.absprog.context import collect_synthesis_context
        from GenMonads.absprog.templates import render_prompt

        ctx = collect_synthesis_context(
            "shape_invdataset/Glibc_slist_clean_iter/glibc_slist_iter_back_2.c",
            sibling_dirs=["shape_invdataset/Glibc_slist_clean_iter"],
        )
        prompt = render_prompt(ctx)
        scaffold = prompt.split("## Selected Scaffold", 1)[1].split("## Loop Forest", 1)[0]
        # The skeleton-pointer line is present.
        assert "skeleton/<basename>_rel_lib.v" in scaffold
        # No stale single-loop names embedded in the prompt.
        fn = "glibc_slist_clean_iter_back_2"
        for bad in (
            f"{fn}_M_loop_M1", f"{fn}_M_loop_M2",
            f"{fn}_M_loop_before", f"{fn}_M_loop_end",
            f"{fn}_M_loop_body", f"{fn}_M_loop_aux",
        ):
            assert bad not in scaffold, \
                f"stale single-loop name {bad!r} leaked into Selected Scaffold"
        # The Selected Scaffold no longer carries the verbose forest sketch
        # — those names belong to the actual lib file, not the prompt.
        assert f"{fn}_M_loop1_M2" not in scaffold
        assert f"{fn}_M_loop1_to_inner_2" not in scaffold


class TestForestPerLoopSafeexec:
    def test_loop_forest_section_shows_each_loops_safeexec_invariant(self):
        """Each loop in the Loop Forest section carries its own safeExec
        invariant referencing its own ``_M_loop{k}`` and the root's ``_end``."""
        from GenMonads.absprog.context import collect_synthesis_context
        from GenMonads.absprog.templates import render_prompt

        ctx = collect_synthesis_context(
            "shape_invdataset/Glibc_slist_clean_iter/glibc_slist_iter_back_2.c",
            sibling_dirs=["shape_invdataset/Glibc_slist_clean_iter"],
        )
        prompt = render_prompt(ctx)
        forest = prompt.split("## Loop Forest", 1)[1].split("## Required Holes", 1)[0]
        fn = "glibc_slist_clean_iter_back_2"
        # Outer (loop1) invariant uses loop1's M and the root's _end.
        assert (
            f"bind({fn}_M_loop1(l1_1,s), {fn}_M_loop1_end)" in forest
        ), "loop1 invariant missing per-loop safeExec"
        # Inner (loop2) invariant uses loop2's M but still the root's _end.
        assert (
            f"bind({fn}_M_loop2(l2_1,s), {fn}_M_loop1_end)" in forest
        ), "loop2 invariant missing per-loop safeExec"


class TestPerLoopEarlyReturnDetection:
    def test_loop_template_records_break_as_no_early_return(self):
        """``break`` exits only its own loop and is already modeled by M1 —
        it must NOT be flagged as early-return."""
        from GenMonads.absprog.loop_forest import build_loop_templates

        src = (
            'long f(int x) {\n'
            '    /*@ Inv listrep(x) */\n'
            '    while (x) { if (x == 5) break; x--; }\n'
            '    return 0;\n'
            '}\n'
        )
        invs = [{
            "type": "Inv", "content": "listrep(x)", "translated": "sll(x, l)",
            "variables": ["l"], "variable_types": ["list Z"],
            "command_guard": "x",
        }]
        ts = build_loop_templates("f", src, invs)
        assert len(ts) == 1
        assert ts[0]["has_early_return"] is False

    def test_loop_template_flags_top_level_return_in_body(self):
        from GenMonads.absprog.loop_forest import build_loop_templates

        src = (
            'long f(int x) {\n'
            '    /*@ Inv listrep(x) */\n'
            '    while (x) { if (x == 5) return 99; x--; }\n'
            '    return 0;\n'
            '}\n'
        )
        invs = [{
            "type": "Inv", "content": "listrep(x)", "translated": "sll(x, l)",
            "variables": ["l"], "variable_types": ["list Z"],
            "command_guard": "x",
        }]
        ts = build_loop_templates("f", src, invs)
        assert ts[0]["has_early_return"] is True

    def test_nested_return_attributes_to_inner_loop_only(self):
        """A ``return`` inside a nested loop's body belongs to the inner
        loop, not the outer.  Mirrors the C control flow."""
        from GenMonads.absprog.loop_forest import build_loop_templates

        src = (
            'long f(int x) {\n'
            '    /*@ Inv listrep(x) */\n'
            '    while (x) {\n'
            '        /*@ Inv listrep(x) */\n'
            '        while (x) { if (x == 5) return 99; x--; }\n'
            '        x--;\n'
            '    }\n'
            '    return 0;\n'
            '}\n'
        )
        invs = [
            {"type": "Inv", "content": "listrep(x)", "translated": "sll(x, l)",
             "variables": ["l1"], "variable_types": ["list Z"], "command_guard": "x"},
            {"type": "Inv", "content": "listrep(x)", "translated": "sll(x, l)",
             "variables": ["l2"], "variable_types": ["list Z"], "command_guard": "x"},
        ]
        ts = build_loop_templates("f", src, invs)
        outer = next(t for t in ts if t["parent"] is None)
        inner = next(t for t in ts if t["parent"] == outer["loop_index"])
        assert outer["has_early_return"] is False
        assert inner["has_early_return"] is True


# ---------------------------------------------------------------------------
# Option C — skeleton emits qualified Require Import for cross-file callees
# when the project's _CoqProject covers the lib dir.


class TestQualifiedRequireImport:
    def _setup(self, tmp_path, *, prefix):
        """Build a minimal C source tree with one callee and one caller,
        plus a _CoqProject binding the lib dir to ``prefix``."""
        src_dir = tmp_path / "src"
        lib_dir = tmp_path / "libs"
        src_dir.mkdir()
        lib_dir.mkdir()
        # Project _CoqProject lives at tmp_path; walks up from lib_dir.
        if prefix is None:
            (tmp_path / "_CoqProject").write_text("")  # no relevant -R/-Q
        else:
            (tmp_path / "_CoqProject").write_text(
                f"-R {lib_dir} {prefix}\n", encoding="utf-8",
            )

        callee = src_dir / "list_tail.c"
        callee.write_text(
            '#include "verification_list.h"\n'
            '#include "sll_shape_def.h"\n'
            '\n'
            'struct list { int data; struct list *next; };\n'
            '\n'
            'struct list *list_tail(struct list *x)\n'
            '/*@ Require listrep(x)\n'
            '    Ensure  listrep(__return) */\n'
            '{\n'
            '    /*@ Inv listrep(x) */\n'
            '    while (x) { x = x->next; }\n'
            '    return x;\n'
            '}\n'
        )
        caller = src_dir / "demo.c"
        caller.write_text(
            '#include "verification_list.h"\n'
            '#include "sll_shape_def.h"\n'
            '\n'
            'struct list { int data; struct list *next; };\n'
            '\n'
            'struct list *list_tail(struct list *x);\n'
            '\n'
            'struct list *demo(struct list *x)\n'
            '/*@ Require listrep(x)\n'
            '    Ensure  listrep(__return) */\n'
            '{\n'
            '    return list_tail(x);\n'
            '}\n'
        )
        return src_dir, lib_dir, callee, caller

    def test_qualified_require_import_under_R_prefix(self, tmp_path):
        """When the project binds the lib dir to ``LIB.PREFIX``, the
        skeleton's ``Require Import`` for a cross-file callee uses the
        full qualified ``LIB.PREFIX.{callee}_rel_lib`` name.  This is the
        case in the user's run where the project has
        ``-R /output/gen/libs LLM4PV.output.gen.libs`` and the bare-name
        skeleton failed to resolve."""
        src_dir, lib_dir, callee_c, caller_c = self._setup(
            tmp_path, prefix="LIB.demo",
        )
        # Generate callee lib first (topo order).
        callee_path = generate_rel_lib_for_file(
            str(callee_c), str(lib_dir),
            sibling_dirs=[str(src_dir)],
        )
        assert callee_path is not None
        # Generate caller lib — its Require Import should be qualified.
        caller_path = generate_rel_lib_for_file(
            str(caller_c), str(lib_dir),
            sibling_dirs=[str(src_dir)],
        )
        assert caller_path is not None
        content = open(caller_path).read()
        assert "Require Import LIB.demo.list_tail_rel_lib." in content
        assert "Require Import list_tail_rel_lib." not in content

    def test_qualified_require_import_under_subdir(self, tmp_path):
        """User's actual layout: lib dir is under a registered prefix
        plus an extra subdirectory.  The resolver should include the
        relative path between the registered root and the file."""
        src_dir = tmp_path / "src"
        lib_root = tmp_path / "libs"
        lib_sub = lib_root / "demo"
        src_dir.mkdir()
        lib_sub.mkdir(parents=True)
        (tmp_path / "_CoqProject").write_text(
            f"-R {lib_root} LIB.libs\n", encoding="utf-8",
        )

        # Build minimal callee/caller using same shape as above.
        for c_name, body in [
            ("list_tail.c",
             'struct list { int data; struct list *next; };\n'
             '\n'
             'struct list *list_tail(struct list *x)\n'
             '/*@ Require listrep(x)\n'
             '    Ensure  listrep(__return) */\n'
             '{\n'
             '    /*@ Inv listrep(x) */\n'
             '    while (x) { x = x->next; }\n'
             '    return x;\n'
             '}\n'),
            ("demo.c",
             'struct list { int data; struct list *next; };\n'
             '\n'
             'struct list *list_tail(struct list *x);\n'
             '\n'
             'struct list *demo(struct list *x)\n'
             '/*@ Require listrep(x)\n'
             '    Ensure  listrep(__return) */\n'
             '{\n'
             '    return list_tail(x);\n'
             '}\n'),
        ]:
            (src_dir / c_name).write_text(
                '#include "verification_list.h"\n'
                '#include "sll_shape_def.h"\n\n' + body
            )

        # Generate callee into lib_sub, then caller — caller's Require
        # Import should resolve through the registered root.
        callee_path = generate_rel_lib_for_file(
            str(src_dir / "list_tail.c"), str(lib_sub),
            sibling_dirs=[str(src_dir)],
        )
        assert callee_path is not None
        caller_path = generate_rel_lib_for_file(
            str(src_dir / "demo.c"), str(lib_sub),
            sibling_dirs=[str(src_dir)],
        )
        assert caller_path is not None
        content = open(caller_path).read()
        # Expected: LIB.libs.demo.list_tail_rel_lib  (registered prefix +
        # relative subdir + filename).
        assert "Require Import LIB.libs.demo.list_tail_rel_lib." in content

    def test_bare_require_import_when_no_coq_project(self, tmp_path):
        """No discoverable _CoqProject → preserve historical bare-name
        emission so callers without project setup keep working."""
        # tmp_path does NOT contain a _CoqProject; walk up from output_dir
        # finds nothing relevant (parent dirs of pytest's tmp tree don't
        # have one either).
        src_dir, lib_dir, callee_c, caller_c = self._setup(tmp_path, prefix=None)
        # Remove the empty _CoqProject we created so walk-up truly fails
        # within this isolated tree.
        (tmp_path / "_CoqProject").unlink()
        callee_path = generate_rel_lib_for_file(
            str(callee_c), str(lib_dir), sibling_dirs=[str(src_dir)],
        )
        assert callee_path is not None
        caller_path = generate_rel_lib_for_file(
            str(caller_c), str(lib_dir), sibling_dirs=[str(src_dir)],
        )
        assert caller_path is not None
        content = open(caller_path).read()
        # Either bare name appears, OR — if walk-up happens to find a
        # _CoqProject from this test runner's parent dirs that doesn't
        # cover lib_dir — the fallback still resolves to bare.
        assert "Require Import list_tail_rel_lib." in content
