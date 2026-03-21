from GenMonads.absprog.gen_rel_lib import generate_rel_lib


def test_generate_rel_lib_uses_function_scoped_guard_names():
    func_infos = [
        {
            "func_name": "sll_rotate_left",
            "require_var_count": 1,
            "inv_var_count": 2,
            "ensure_var_count": 1,
            "coq_guard": "fun a =>\n  let '(l1, l2) := a in\n  l1 <> [].",
        },
        {
            "func_name": "sll_rotate_right",
            "require_var_count": 1,
            "inv_var_count": 3,
            "ensure_var_count": 1,
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
            "inv_var_count": 3,
            "ensure_var_count": 2,
            "coq_guard": "fun a =>\n  let '(l1, l2, l3) := a in\n  l2 <> [].",
        }
    ]

    content = generate_rel_lib("sll_copy", func_infos)

    assert "Definition maketuple {A B} (a : A) (b : B) : (A * B) := (a, b)." in content
    assert "Parameter MretTy : Type." in content
