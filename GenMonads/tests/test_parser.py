"""
Test suite for the assertion parser module.

Tests parsing assertion strings into ASTs and recovering them back.
"""

import pytest

from GenMonads.transshape.parser import (
    parse_assertion,
    recover_assertion,
    Var,
    BinOp,
    FieldAccess,
    Deref,
    CallExpr,
    SpatialPred,
    SepConj,
    AndConj,
    Implies,
    Exists,
)


class TestParse:
    def test_parse_simple_predicate(self):
        ast = parse_assertion("listrep(x)")
        assert isinstance(ast, SpatialPred)
        assert ast.name == "listrep"
        assert len(ast.args) == 1
        assert isinstance(ast.args[0], Var)
        assert ast.args[0].name == "x"

    def test_parse_predicate_multiple_args(self):
        ast = parse_assertion("lseg(x, y)")
        assert isinstance(ast, SpatialPred)
        assert ast.name == "lseg"
        assert len(ast.args) == 2

    def test_parse_sep_conj(self):
        ast = parse_assertion("listrep(x) * lseg(y, z)")
        assert isinstance(ast, SepConj)
        assert len(ast.formulas) == 2
        assert isinstance(ast.formulas[0], SpatialPred)
        assert isinstance(ast.formulas[1], SpatialPred)

    def test_parse_and_conj(self):
        ast = parse_assertion("t != 0 && listrep(x)")
        assert isinstance(ast, AndConj)
        assert len(ast.formulas) == 2
        assert isinstance(ast.formulas[0], BinOp)
        assert isinstance(ast.formulas[1], SpatialPred)

    def test_parse_exists(self):
        ast = parse_assertion("exists u, listrep(u)")
        assert isinstance(ast, Exists)
        assert ast.vars == ["u"]
        assert isinstance(ast.body, SpatialPred)

    def test_parse_exists_with_body(self):
        ast = parse_assertion("exists u, listrep(u) * listrep(v)")
        assert isinstance(ast, Exists)
        assert ast.vars == ["u"]
        assert isinstance(ast.body, SepConj)
        assert len(ast.body.formulas) == 2

    def test_parse_field_access(self):
        ast = parse_assertion("t -> next == 0")
        assert isinstance(ast, BinOp)
        assert ast.op == "=="
        assert isinstance(ast.left, FieldAccess)
        assert ast.left.field == "next"

    def test_parse_deref_comparison(self):
        ast = parse_assertion("*head == head_node")
        assert isinstance(ast, BinOp)
        assert ast.op == "=="
        assert isinstance(ast.left, Deref)
        assert isinstance(ast.left.expr, Var)
        assert ast.left.expr.name == "head"
        assert isinstance(ast.right, Var)
        assert ast.right.name == "head_node"

    def test_parse_at_pre(self):
        ast = parse_assertion("lseg(x@pre, p)")
        assert isinstance(ast, SpatialPred)
        assert ast.name == "lseg"
        assert isinstance(ast.args[0], Var)
        assert ast.args[0].name == "x@pre"

    def test_parse_emp(self):
        ast = parse_assertion("emp")
        assert isinstance(ast, SpatialPred)
        assert ast.name == "emp"
        assert ast.args == []

    def test_parse_number_arg(self):
        ast = parse_assertion("t != 0")
        assert isinstance(ast, BinOp)
        assert ast.right == 0

    def test_parse_complex(self):
        ast = parse_assertion("t != 0 && t -> next == 0 && sllseg(x@pre, p, l1) * sll(p, l2) * sllseg(y, t, l3)")
        assert isinstance(ast, SepConj) or isinstance(ast, AndConj)

    def test_parse_parenthesized_pure_implication(self):
        ast = parse_assertion("((nxt == 0) => (stop == 0))")
        assert isinstance(ast, Implies)
        assert isinstance(ast.left, BinOp)
        assert ast.left.op == "=="
        assert isinstance(ast.right, BinOp)
        assert ast.right.op == "=="

    def test_parse_implication_as_conjunct(self):
        ast = parse_assertion("node != 0 && ((nxt == 0) => (stop == 0)) && listrep(stop)")
        assert isinstance(ast, AndConj)
        assert isinstance(ast.formulas[1], Implies)

    def test_sep_star_after_pure_equality_is_not_multiplication(self):
        ast = parse_assertion("x -> data == v * listrep(y)")
        assert isinstance(ast, SepConj)
        assert len(ast.formulas) == 2
        assert isinstance(ast.formulas[0], BinOp)
        assert ast.formulas[0].op == "=="
        assert isinstance(ast.formulas[0].right, Var)
        assert ast.formulas[0].right.name == "v"
        assert isinstance(ast.formulas[1], SpatialPred)
        assert ast.formulas[1].name == "listrep"

    def test_parse_multiplication_before_non_predicate_operand(self):
        ast = parse_assertion("v_len == 2 * n@pre + 2")
        assert isinstance(ast, BinOp)
        assert ast.op == "=="
        assert isinstance(ast.right, BinOp)
        assert ast.right.op == "+"
        assert isinstance(ast.right.left, BinOp)
        assert ast.right.left.op == "*"

    def test_unknown_call_after_comparison_rhs_star_is_spatial(self):
        ast = parse_assertion("n == v * foopred(y)")
        assert isinstance(ast, SepConj)
        assert isinstance(ast.formulas[0], BinOp)
        assert ast.formulas[0].right == Var("v")
        assert isinstance(ast.formulas[1], SpatialPred)
        assert ast.formulas[1].name == "foopred"

    def test_qualified_call_after_comparison_rhs_star_is_spatial(self):
        ast = parse_assertion("n == v * IntArray::full(p, n, l)")
        assert isinstance(ast, SepConj)
        assert isinstance(ast.formulas[0], BinOp)
        assert ast.formulas[0].right == Var("v")
        assert isinstance(ast.formulas[1], SpatialPred)
        assert ast.formulas[1].name == "IntArray::full"

    def test_registered_pure_call_after_star_is_multiplication(self):
        ast = parse_assertion("n == v * Zlength(y)")
        assert isinstance(ast, BinOp)
        assert ast.op == "=="
        assert isinstance(ast.right, BinOp)
        assert ast.right.op == "*"
        assert isinstance(ast.right.right, CallExpr)
        assert ast.right.right.name == "Zlength"

    def test_unknown_pure_call_comparison_is_rejected(self):
        with pytest.raises(ValueError, match="Unexpected trailing text"):
            parse_assertion("foofun(y) == n")


class TestRecover:
    def test_recover_predicate(self):
        ast = SpatialPred("sll", [Var("x"), Var("l1")])
        assert recover_assertion(ast) == "sll(x, l1)"

    def test_recover_emp(self):
        ast = SpatialPred("emp", [])
        assert recover_assertion(ast) == "emp"

    def test_recover_exists(self):
        body = SpatialPred("sll", [Var("x"), Var("l1")])
        ast = Exists(["l1"], body)
        result = recover_assertion(ast)
        assert "exists l1," in result
        assert "sll(x, l1)" in result

    def test_recover_sep_conj(self):
        ast = SepConj([
            SpatialPred("sll", [Var("x"), Var("l1")]),
            SpatialPred("sll", [Var("y"), Var("l2")]),
        ])
        assert recover_assertion(ast) == "sll(x, l1) * sll(y, l2)"

    def test_recover_deref_comparison(self):
        ast = BinOp("==", Deref(Var("head")), Var("head_node"))
        assert recover_assertion(ast) == "*head == head_node"

    @pytest.mark.parametrize("text", [
        "listrep(x)",
        "lseg(x, y)",
        "t != 0",
        "t -> next == 0",
        "*head == head_node",
        "listrep(x) * lseg(y, z)",
        "t != 0 && listrep(x)",
        "((nxt == 0) => (stop == 0))",
    ])
    def test_recover_roundtrip(self, text):
        ast = parse_assertion(text)
        recovered = recover_assertion(ast)
        # Re-parse to verify structural equivalence
        ast2 = parse_assertion(recovered)
        assert type(ast) == type(ast2)


# ---------------------------------------------------------------------------
# IntArray support — qualified predicate names + arithmetic comparisons.


def test_parse_qualified_predicate_name():
    """Namespaced predicate names like ``IntArray::full_shape`` parse as
    one SpatialPred node with the qualified name."""
    from GenMonads.transshape.parser import parse_assertion, SpatialPred, Var

    ast = parse_assertion("IntArray::full_shape(height, n)")
    assert isinstance(ast, SpatialPred)
    assert ast.name == "IntArray::full_shape"
    assert len(ast.args) == 2
    assert isinstance(ast.args[0], Var) and ast.args[0].name == "height"


def test_parse_multi_level_qualified_predicate():
    """Triple-nested namespaces also parse — keeps the grammar
    forward-compatible for deeper qualifications."""
    from GenMonads.transshape.parser import parse_assertion, SpatialPred

    ast = parse_assertion("Foo::Bar::Baz(x)")
    assert isinstance(ast, SpatialPred)
    assert ast.name == "Foo::Bar::Baz"


def test_parse_bare_predicate_still_works():
    """Qualified-identifier support must not regress bare predicates
    (``listrep``, ``lseg``)."""
    from GenMonads.transshape.parser import parse_assertion, SpatialPred

    ast = parse_assertion("listrep(x)")
    assert isinstance(ast, SpatialPred)
    assert ast.name == "listrep"


def test_parse_ordering_comparisons():
    """``<=``, ``>=``, ``<``, ``>`` are recognized as comparison
    operators (in addition to ``==`` / ``!=``).  Two-char operators are
    checked before their single-char prefixes."""
    from GenMonads.transshape.parser import parse_assertion, BinOp

    for text, expected_op in [
        ("0 <= n", "<="),
        ("n < 10000", "<"),
        ("v_water >= 0", ">="),
        ("v_left > v_right", ">"),
    ]:
        ast = parse_assertion(text)
        assert isinstance(ast, BinOp), f"{text!r} did not produce a BinOp"
        assert ast.op == expected_op


def test_parse_arithmetic_in_comparison_rhs():
    """``v_left <= v_right + 1`` parses as a comparison whose right side
    is a ``BinOp('+', ...)`` expression."""
    from GenMonads.transshape.parser import parse_assertion, BinOp, Var

    ast = parse_assertion("v_left <= v_right + 1")
    assert isinstance(ast, BinOp)
    assert ast.op == "<="
    assert isinstance(ast.right, BinOp)
    assert ast.right.op == "+"
    assert isinstance(ast.right.left, Var) and ast.right.left.name == "v_right"
    assert ast.right.right == 1


def test_parse_arithmetic_left_associative():
    """``a + b - c`` parses as ``(a + b) - c`` (left associative)."""
    from GenMonads.transshape.parser import parse_assertion, BinOp

    # Embed in a comparison so it parses (the parser's entry point
    # expects formulas, not bare expressions).
    ast = parse_assertion("0 < a + b - c")
    assert isinstance(ast, BinOp) and ast.op == "<"
    rhs = ast.right
    assert isinstance(rhs, BinOp) and rhs.op == "-"
    assert isinstance(rhs.left, BinOp) and rhs.left.op == "+"


def test_parse_lc42_require_clause():
    """The exact ``Require`` clause from ``lc42_trap_rain.c`` parses
    without error.  Pin to catch any regression."""
    from GenMonads.transshape.parser import parse_assertion

    text = "0 <= n && n < 10000 && IntArray::full_shape(height, n)"
    ast = parse_assertion(text)
    # Just check it parsed — the exact tree structure is incidental.
    assert ast is not None


def test_parse_lc42_invariant_clause():
    """The arithmetic-laden ``Inv`` clause from ``lc42_trap_rain.c``
    (multi-var exists, ``@pre`` references, arithmetic comparisons,
    namespaced predicate) parses end-to-end.

    ``store(&…)`` calls are NOT exercised here because the higher-level
    translator runs ``_extract_memory_state_predicates`` before parsing —
    so the parser never sees them.  The end-to-end test below
    (``test_lc42_end_to_end_translates_namespaced_predicate``) covers
    the integrated flow; this test pins the parser-only contract."""
    from GenMonads.transshape.parser import parse_assertion

    text = (
        "exists v_left v_right v_left_max v_right_max v_water, "
        "0 <= v_left && v_left <= v_right + 1 && v_right < n@pre && "
        "height == height@pre && n == n@pre && "
        "0 <= n@pre && n@pre < 10000 && "
        "IntArray::full_shape(height@pre, n@pre)"
    )
    ast = parse_assertion(text)
    assert ast is not None


def test_predicate_mapping_int_array_full():
    """``IntArray::full_shape`` translates to ``IntArray::full`` with
    one ``list Z`` data witness appended (matches the listrep → sll
    pattern)."""
    from GenMonads.predicate_mapping import get_predicate_mappings

    mappings = get_predicate_mappings()
    assert "IntArray::full_shape" in mappings
    m = mappings["IntArray::full_shape"]
    assert m.data_name == "IntArray::full"
    assert m.shape_arity == 2
    assert m.data_var_types == ["list Z"]


def test_predicate_mapping_int_array_seg_and_missing_i():
    """The two sibling predicates (``seg_shape``, ``missing_i_shape``)
    are also mapped consistently."""
    from GenMonads.predicate_mapping import get_predicate_mappings

    mappings = get_predicate_mappings()
    assert mappings["IntArray::seg_shape"].data_name == "IntArray::seg"
    assert mappings["IntArray::seg_shape"].shape_arity == 3
    assert mappings["IntArray::missing_i_shape"].data_name == "IntArray::missing_i"
    assert mappings["IntArray::missing_i_shape"].shape_arity == 4


def test_lc42_end_to_end_translates_namespaced_predicate(tmp_path):
    """End-to-end: running the translator on a synthetic int_array file
    rewrites ``IntArray::full_shape(...)`` to ``IntArray::full(..., ?lN)``
    with the data witness appended."""
    from GenMonads.transshape.process_and_translate import process_and_translate_file

    src = (
        '#include "int_array_def.h"\n'
        '\n'
        'int demo(int *height, int n)\n'
        '/*@\n'
        '    Require 0 <= n && IntArray::full_shape(height, n)\n'
        '    Ensure  IntArray::full_shape(height, n)\n'
        ' */\n'
        '{ return 0; }\n'
    )
    path = tmp_path / "demo.c"
    path.write_text(src)
    result = process_and_translate_file(str(path))
    fs = (result.get("functions") or [result])[0]["funcspec"]
    assert "IntArray::full(height, n, ?l1)" in fs["require"]["translated"]
    assert "IntArray::full(height, n, ?l2)" in fs["ensure"]["translated"]


# ---------------------------------------------------------------------------
# Unary minus — needed by ``lc31_next_permutation.c``-style invariants
# (``-1 <= v_i``) and any pattern with explicitly-bounded loop counters.


def test_parse_unary_minus_integer_literal():
    """``-1`` produces the negative integer ``-1`` (not a BinOp around
    zero) so downstream comparisons see a clean literal."""
    from GenMonads.transshape.parser import parse_assertion, BinOp

    ast = parse_assertion("-1 <= v_i")
    assert isinstance(ast, BinOp)
    assert ast.op == "<="
    assert ast.left == -1


def test_parse_unary_minus_with_arithmetic_chain():
    """Mixed: ``v_i <= n@pre - 2`` (binary minus, not unary) and
    ``-1 <= v_i`` (unary minus) in the same conjunction."""
    from GenMonads.transshape.parser import parse_assertion, AndConj, BinOp

    ast = parse_assertion("-1 <= v_i && v_i <= n@pre - 2")
    assert isinstance(ast, AndConj)
    assert len(ast.formulas) == 2
    # First conjunct uses unary minus on the literal.
    assert ast.formulas[0].left == -1
    # Second conjunct's RHS is ``BinOp('-', Var(n@pre), 2)``.
    rhs = ast.formulas[1].right
    assert isinstance(rhs, BinOp) and rhs.op == "-"


def test_parse_unary_minus_on_variable_expression():
    """``-v_i <= 0`` parses as ``(0 - v_i) <= 0`` — the renderer's
    arithmetic chain handles the negation via subtraction."""
    from GenMonads.transshape.parser import parse_assertion, BinOp, Var

    ast = parse_assertion("-v_i <= 0")
    assert isinstance(ast, BinOp) and ast.op == "<="
    lhs = ast.left
    assert isinstance(lhs, BinOp) and lhs.op == "-"
    assert lhs.left == 0
    assert isinstance(lhs.right, Var) and lhs.right.name == "v_i"


def test_parse_unary_minus_does_not_swallow_field_arrow():
    """``-`` as start of ``->`` (field access) must not be consumed by
    the unary-minus path.  Sanity check the peek logic."""
    from GenMonads.transshape.parser import parse_assertion, BinOp, FieldAccess

    ast = parse_assertion("x -> next == 0")
    # If we accidentally consumed ``-``, ``x`` would have parsed as an
    # identifier and the ``->`` would be misread.  This guards against
    # that regression.
    assert isinstance(ast, BinOp)
    assert isinstance(ast.left, FieldAccess)
    assert ast.left.field == "next"


def test_parse_lc31_first_invariant_clause():
    """The first Inv of ``lc31_next_permutation.c`` (the one that was
    failing) — pin it as a regression."""
    from GenMonads.transshape.parser import parse_assertion

    text = (
        "exists v_i v_j v_left v_right v_tmp, "
        "-1 <= v_i && v_i <= n@pre - 2 && "
        "a == a@pre && n == n@pre && "
        "0 <= n@pre && n@pre < 2147483647 && "
        "IntArray::full_shape(a@pre, n@pre)"
    )
    ast = parse_assertion(text)
    assert ast is not None


def test_lc31_end_to_end_all_invariants_translate(tmp_path):
    """Every invariant in ``lc31_next_permutation.c`` parses and
    translates — caught the regression where Inv #1 silently failed and
    Inv #3 then got mis-indexed (``M_loop`` instead of ``M_loop3``)."""
    from GenMonads.transshape.process_and_translate import process_and_translate_file

    result = process_and_translate_file(
        "shape_invdataset/int_array/lc31_next_permutation.c"
    )
    fd = (result.get("functions") or [result])[0]
    invs = fd.get("inner_assertions") or []
    assert len(invs) == 3
    for i, inv in enumerate(invs, start=1):
        assert "error" not in inv, f"Inv #{i} failed: {inv.get('error')}"
        assert "translated" in inv
        # Each invariant gets its own per-loop prefix in the generated
        # data witness (l1_1, l2_1, l3_1).
        assert f"l{i}_1" in inv["variables"]


# ---------------------------------------------------------------------------
# lc5_longest_palindrom support — Assert blocks, function-call expressions,
# typed exists binders.


def test_parse_function_call_expression():
    """Function-call expressions inside predicate args parse as CallExpr
    nodes — needed by ``CharArray::full(p, n, app(out, cons(0, nil)))``."""
    from GenMonads.transshape.parser import parse_assertion, CallExpr, SpatialPred

    ast = parse_assertion("CharArray::full(p, n, app(out, cons(0, nil)))")
    assert isinstance(ast, SpatialPred) and ast.name == "CharArray::full"
    # Third arg is the nested call ``app(out, cons(0, nil))``.
    nested = ast.args[2]
    assert isinstance(nested, CallExpr) and nested.name == "app"
    inner = nested.args[1]
    assert isinstance(inner, CallExpr) and inner.name == "cons"


def test_recover_function_call_expression_round_trip():
    """The ``recover_expr`` function emits CallExpr nodes back as
    function-call syntax — needed so translated assertions can be
    re-parsed downstream."""
    from GenMonads.transshape.parser import parse_assertion, recover_assertion

    text = "app(out, cons(0, nil)) == out"
    ast = parse_assertion(text)
    recovered = recover_assertion(ast)
    assert "app(out, cons(0, nil))" in recovered


def test_parse_predicate_args_with_arithmetic():
    """SpatialPred arguments may contain ``+``/``-`` arithmetic — e.g.
    ``IntArray::seg(p, 0, v_i + 1, l)`` or ``CharArray::undef_seg(output,
    __return + 1, n + 1)``.  These parse as a single arithmetic
    expression per arg."""
    from GenMonads.transshape.parser import parse_assertion, SpatialPred, BinOp

    ast = parse_assertion("IntArray::seg(p, 0, v_i + 1, l)")
    assert isinstance(ast, SpatialPred)
    assert len(ast.args) == 4
    # Third arg is the ``v_i + 1`` arithmetic expression.
    assert isinstance(ast.args[2], BinOp) and ast.args[2].op == "+"


def test_parse_exists_typed_binders():
    """Coq-style ``exists (name : Type), body`` parses, capturing only
    the names; types are discarded (the translator infers them
    separately)."""
    from GenMonads.transshape.parser import parse_assertion, Exists

    ast = parse_assertion("exists (x : list Z), x == nil")
    assert isinstance(ast, Exists)
    assert ast.vars == ["x"]


def test_parse_exists_mixed_bare_and_typed_binders():
    """``exists v_i v_j (s2_full : list Z) (p_done : list Z), body``
    — the canonical lc5 pattern."""
    from GenMonads.transshape.parser import parse_assertion, Exists

    ast = parse_assertion(
        "exists v_i v_j (s2_full : list Z) (p_done : list Z), 1 <= v_i"
    )
    assert isinstance(ast, Exists)
    assert ast.vars == ["v_i", "v_j", "s2_full", "p_done"]


def test_parse_exists_bare_then_typed_then_body():
    """Mixed binders without trailing typed binders shouldn't break."""
    from GenMonads.transshape.parser import parse_assertion, Exists

    ast = parse_assertion("exists v_i (s2_full : list Z), 1 <= v_i")
    assert isinstance(ast, Exists)
    assert ast.vars == ["v_i", "s2_full"]


def test_parse_exists_typed_then_body_starts_with_identifier():
    """After a typed binder + ``,``, a bare identifier in the body
    isn't another binder — pin this regression."""
    from GenMonads.transshape.parser import parse_assertion, Exists, BinOp

    ast = parse_assertion("exists (x : list Z), x == nil")
    assert isinstance(ast, Exists)
    assert ast.vars == ["x"]
    assert isinstance(ast.body, BinOp) and ast.body.op == "=="


def test_preprocessor_extracts_bare_assert_block(tmp_path):
    """Bare ``/*@ Assert ... */`` proof-checkpoint blocks are
    classified as ``type='Assert'`` (not ``'unknown'``), with the
    ``Assert`` keyword stripped from the content so the parser sees
    only the assertion body."""
    from GenMonads.transshape.preprocess import AnnotationExtractor

    src = (
        'void f()\n'
        '/*@ Require emp Ensure emp */\n'
        '{\n'
        '    /*@ Assert\n'
        '        exists x,\n'
        '        listrep(x)\n'
        '    */\n'
        '    /*@ Inv Assert exists y, listrep(y) */\n'
        '    while (1) {}\n'
        '}\n'
    )
    path = tmp_path / "demo.c"
    path.write_text(src)
    r = AnnotationExtractor().process_file(str(path))
    fd = (r.get("functions") or [r])[0]
    invs = fd.get("inner_assertions") or []
    assert len(invs) == 2
    # First is the bare Assert — type='Assert', content starts with the
    # actual body (no leading ``Assert`` keyword leaked).
    assert invs[0]["type"] == "Assert"
    assert invs[0]["content"].startswith("exists x")
    # Second is ``Inv Assert ...`` — type='Inv', the ``Assert`` prefix
    # is stripped by the existing nested handler.
    assert invs[1]["type"] == "Inv"
    assert invs[1]["content"].startswith("exists y")


def test_lc5_end_to_end_all_assertions_translate():
    """End-to-end: every assertion in ``lc5_longest_palindrom.c``
    (Require, Ensure, 4 Inv, 7 Assert) translates without error.  Pin
    the multi-bug fix:
        * preprocessor recognises bare ``/*@ Assert ... */``
        * parser accepts function-call expressions
        * parser accepts typed ``(name : Type)`` exists binders
        * predicate args parse arithmetic via ``parse_arith_expr``."""
    from GenMonads.transshape.process_and_translate import process_and_translate_file

    r = process_and_translate_file(
        "shape_invdataset/int_array/lc5_longest_palindrom.c"
    )
    fd = (r.get("functions") or [r])[0]
    fs = fd.get("funcspec") or {}
    assert "error" not in fs.get("require") or {}, fs["require"].get("error")
    assert "error" not in fs.get("ensure") or {}, fs["ensure"].get("error")
    inv_kinds = []
    for inv in fd.get("inner_assertions") or []:
        assert "error" not in inv, (inv["type"], inv.get("error"))
        inv_kinds.append(inv["type"])
    # 4 Inv blocks (one per loop) + 7 Assert proof-checkpoints.
    assert inv_kinds.count("Inv") == 4
    assert inv_kinds.count("Assert") == 7


# ---------------------------------------------------------------------------
# `Inv Assert` qualifier preservation — the QCP distinction between bare
# `Inv` and `Inv Assert` must round-trip through translation.


def test_preprocessor_records_inv_assert_qualifier(tmp_path):
    """A ``/*@ Inv Assert ... */`` source block is classified as
    ``type='Inv'`` AND carries ``inv_assert=True``, so the substitution
    layer can re-emit the original qualifier."""
    from GenMonads.transshape.preprocess import AnnotationExtractor

    src = (
        'void f()\n'
        '/*@ Require emp Ensure emp */\n'
        '{\n'
        '    /*@ Inv exists x, listrep(x) */\n'
        '    while (1) {}\n'
        '    /*@ Inv Assert exists y, listrep(y) */\n'
        '    while (1) {}\n'
        '}\n'
    )
    path = tmp_path / "demo.c"
    path.write_text(src)
    r = AnnotationExtractor().process_file(str(path))
    fd = (r.get("functions") or [r])[0]
    invs = fd.get("inner_assertions") or []
    assert len(invs) == 2
    # Bare Inv — no inv_assert flag.
    assert invs[0]["type"] == "Inv"
    assert not invs[0].get("inv_assert")
    # Inv Assert — flag set to True.
    assert invs[1]["type"] == "Inv"
    assert invs[1].get("inv_assert") is True


def test_translated_rel_c_preserves_inv_assert_qualifier(tmp_path):
    """When the source has ``/*@ Inv Assert ... */``, the translated
    rel.c must emit ``/*@ Inv Assert ... */`` (not bare ``/*@ Inv ... */``).

    The QCP verifier treats the two qualifiers differently — ``Inv
    Assert`` is a strict assertion at the loop head, bare ``Inv`` is a
    regular invariant — so the qualifier must round-trip."""
    from GenMonads.translate_c_file import translate_c_file

    src = (
        '#include "h.h"\n'
        '\n'
        'long demo(struct list *x)\n'
        '/*@ Require listrep(x) Ensure emp */\n'
        '{\n'
        '    long s;\n'
        '    s = 0;\n'
        '    /*@ Inv Assert exists v, store(&s, long, v) * listrep(x) */\n'
        '    while (s < 10) { s = s + 1; }\n'
        '    return s;\n'
        '}\n'
    )
    src_path = tmp_path / "demo.c"
    src_path.write_text(src)
    rel_c = tmp_path / "demo_rel.c"
    assert translate_c_file(str(src_path), str(rel_c))
    out = rel_c.read_text()
    # The translated invariant must keep the ``Inv Assert`` qualifier
    # (not collapse to bare ``Inv``).
    assert "/*@ Inv Assert" in out
    # And there must NOT be any bare ``/*@ Inv exists ...`` — the source
    # only had one invariant and it was an Inv Assert.
    import re as _re
    bare_inv_count = len(_re.findall(r"/\*@ Inv\s+(?!Assert)", out))
    assert bare_inv_count == 0, f"expected 0 bare Inv blocks, found {bare_inv_count}"


def test_translated_rel_c_distinguishes_inv_vs_inv_assert(tmp_path):
    """In a file with both bare ``Inv`` and ``Inv Assert`` blocks,
    each is emitted with its original qualifier."""
    from GenMonads.translate_c_file import translate_c_file

    src = (
        '#include "h.h"\n'
        '\n'
        'long demo(struct list *x)\n'
        '/*@ Require listrep(x) Ensure emp */\n'
        '{\n'
        '    long a;\n'
        '    long b;\n'
        '    a = 0;\n'
        '    b = 0;\n'
        '    /*@ Inv exists v, store(&a, long, v) * listrep(x) */\n'
        '    while (a < 5) { a = a + 1; }\n'
        '    /*@ Inv Assert exists v, store(&b, long, v) * listrep(x) */\n'
        '    while (b < 5) { b = b + 1; }\n'
        '    return a + b;\n'
        '}\n'
    )
    src_path = tmp_path / "demo.c"
    src_path.write_text(src)
    rel_c = tmp_path / "demo_rel.c"
    assert translate_c_file(str(src_path), str(rel_c))
    out = rel_c.read_text()
    # Exactly one bare Inv and one Inv Assert in the output.
    import re as _re
    inv_assert_count = len(_re.findall(r"/\*@ Inv Assert", out))
    bare_inv_count = len(_re.findall(r"/\*@ Inv\s+(?!Assert)", out))
    assert inv_assert_count == 1, f"expected 1 Inv Assert, found {inv_assert_count}"
    assert bare_inv_count == 1, f"expected 1 bare Inv, found {bare_inv_count}"
