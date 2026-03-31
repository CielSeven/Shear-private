from GenMonads.absprog.assemble import assemble_rel_lib_from_blocks
from GenMonads.absprog.gen_rel_lib import generate_rel_lib, generate_rel_lib_for_file


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
    path = generate_rel_lib_for_file("shape_invdataset/sll/sll_multi_merge.c", str(output_dir))
    assert path is not None

    content = (output_dir / "sll_multi_merge_rel_lib.v").read_text(encoding="utf-8")
    assert "Parameter sll_merge_M : list Z -> list Z -> MONAD (list Z)." in content
    assert "Definition sll_multi_merge_M_loop :" in content


def test_generate_rel_lib_for_early_return_function_includes_early_result_scaffold(tmp_path):
    output_dir = tmp_path / "coq"
    path = generate_rel_lib_for_file("shape_invdataset/sll/sll_multi_merge.c", str(output_dir))
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


def test_assemble_rel_lib_from_blocks_preserves_early_return_scaffold():
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
        "shape_invdataset/sll/sll_multi_merge.c",
        "sll_multi_merge",
        blocks,
    )

    assert "Inductive early_result (S Ret : Type) :=" in content
    assert "Arguments Continue {S Ret} _." in content
    assert "Arguments ReturnNow {S Ret} _." in content
    assert "Definition sll_multi_merge_M_after_loop" in content
    assert "Parameter sll_merge_M : list Z -> list Z -> MONAD (list Z)." in content
    assert "Definition sll_multi_merge_M_loop_before" in content
