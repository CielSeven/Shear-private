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
    Predicate,
    SepConj,
    AndConj,
    Exists,
)


class TestParse:
    def test_parse_simple_predicate(self):
        ast = parse_assertion("listrep(x)")
        assert isinstance(ast, Predicate)
        assert ast.name == "listrep"
        assert len(ast.args) == 1
        assert isinstance(ast.args[0], Var)
        assert ast.args[0].name == "x"

    def test_parse_predicate_multiple_args(self):
        ast = parse_assertion("lseg(x, y)")
        assert isinstance(ast, Predicate)
        assert ast.name == "lseg"
        assert len(ast.args) == 2

    def test_parse_sep_conj(self):
        ast = parse_assertion("listrep(x) * lseg(y, z)")
        assert isinstance(ast, SepConj)
        assert len(ast.formulas) == 2
        assert isinstance(ast.formulas[0], Predicate)
        assert isinstance(ast.formulas[1], Predicate)

    def test_parse_and_conj(self):
        ast = parse_assertion("t != 0 && listrep(x)")
        assert isinstance(ast, AndConj)
        assert len(ast.formulas) == 2
        assert isinstance(ast.formulas[0], BinOp)
        assert isinstance(ast.formulas[1], Predicate)

    def test_parse_exists(self):
        ast = parse_assertion("exists u, listrep(u)")
        assert isinstance(ast, Exists)
        assert ast.vars == ["u"]
        assert isinstance(ast.body, Predicate)

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
        assert isinstance(ast, Predicate)
        assert ast.name == "lseg"
        assert isinstance(ast.args[0], Var)
        assert ast.args[0].name == "x@pre"

    def test_parse_emp(self):
        ast = parse_assertion("emp")
        assert isinstance(ast, Predicate)
        assert ast.name == "emp"
        assert ast.args == []

    def test_parse_number_arg(self):
        ast = parse_assertion("t != 0")
        assert isinstance(ast, BinOp)
        assert ast.right == 0

    def test_parse_complex(self):
        ast = parse_assertion("t != 0 && t -> next == 0 && sllseg(x@pre, p, l1) * sll(p, l2) * sllseg(y, t, l3)")
        assert isinstance(ast, SepConj) or isinstance(ast, AndConj)


class TestRecover:
    def test_recover_predicate(self):
        ast = Predicate("sll", [Var("x"), Var("l1")])
        assert recover_assertion(ast) == "sll(x, l1)"

    def test_recover_emp(self):
        ast = Predicate("emp", [])
        assert recover_assertion(ast) == "emp"

    def test_recover_exists(self):
        body = Predicate("sll", [Var("x"), Var("l1")])
        ast = Exists(["l1"], body)
        result = recover_assertion(ast)
        assert "exists l1," in result
        assert "sll(x, l1)" in result

    def test_recover_sep_conj(self):
        ast = SepConj([
            Predicate("sll", [Var("x"), Var("l1")]),
            Predicate("sll", [Var("y"), Var("l2")]),
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
    ])
    def test_recover_roundtrip(self, text):
        ast = parse_assertion(text)
        recovered = recover_assertion(ast)
        # Re-parse to verify structural equivalence
        ast2 = parse_assertion(recovered)
        assert type(ast) == type(ast2)
