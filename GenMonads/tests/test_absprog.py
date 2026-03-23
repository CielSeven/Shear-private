from GenMonads.absprog.gen_rel_lib import generate_rel_lib


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
