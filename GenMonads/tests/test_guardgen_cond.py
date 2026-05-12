"""Tests for GuardGen condition parser field dereference (->)  support."""
import pytest
from GenMonads.guardgen.registry import PREDICATES
from GenMonads.guardgen.cond.lexer import lex_cond
from GenMonads.guardgen.cond.parser import parse_cond_full
from GenMonads.guardgen.cond.ast import AtomKind
from GenMonads.guardgen import gen_coq_guard
from GenMonads.guardgen.parsing.invariant import extract_pure_aliases


# ---------------------------------------------------------------------------
# Lexer tests
# ---------------------------------------------------------------------------

class TestLexerArrow:
    def test_arrow_no_spaces(self):
        toks = lex_cond("u->next")
        kinds = [t.kind for t in toks]
        assert kinds == ["ID", "ARROW", "ID"]
        assert toks[0].text == "u"
        assert toks[1].text == "->"
        assert toks[2].text == "next"

    def test_arrow_with_spaces(self):
        toks = lex_cond("u -> next")
        kinds = [t.kind for t in toks]
        assert kinds == ["ID", "ARROW", "ID"]

    def test_arrow_in_compound_condition(self):
        toks = lex_cond("p && p->next")
        kinds = [t.kind for t in toks]
        assert kinds == ["ID", "AND", "ID", "ARROW", "ID"]

    def test_arrow_with_comparison(self):
        toks = lex_cond("u->next == null")
        kinds = [t.kind for t in toks]
        assert kinds == ["ID", "ARROW", "ID", "EQ", "ID"]

    def test_arrow_ne_zero(self):
        toks = lex_cond("p->next != 0")
        kinds = [t.kind for t in toks]
        assert kinds == ["ID", "ARROW", "ID", "NE1", "NUM"]


# ---------------------------------------------------------------------------
# Parser tests
# ---------------------------------------------------------------------------

class TestParserFieldAccess:
    def test_bare_field_access_sugar(self):
        """Bare u->next is sugar for u->next != null."""
        node = parse_cond_full("u->next")
        assert node.kind == "atom"
        assert node.atom.kind == AtomKind.PTR_NE_NULL
        assert node.atom.ptr1 == "u->next"

    def test_field_access_eq_null(self):
        node = parse_cond_full("u->next == null")
        assert node.kind == "atom"
        assert node.atom.kind == AtomKind.PTR_EQ_NULL
        assert node.atom.ptr1 == "u->next"

    def test_field_access_ne_null(self):
        node = parse_cond_full("p->next != null")
        assert node.kind == "atom"
        assert node.atom.kind == AtomKind.PTR_NE_NULL
        assert node.atom.ptr1 == "p->next"

    def test_field_access_eq_zero(self):
        node = parse_cond_full("p->next == 0")
        assert node.kind == "atom"
        assert node.atom.kind == AtomKind.PTR_EQ_NULL
        assert node.atom.ptr1 == "p->next"

    def test_field_access_ne_zero(self):
        node = parse_cond_full("p->next != 0")
        assert node.kind == "atom"
        assert node.atom.kind == AtomKind.PTR_NE_NULL
        assert node.atom.ptr1 == "p->next"

    def test_field_access_eq_ptr(self):
        node = parse_cond_full("p->next == q")
        assert node.kind == "atom"
        assert node.atom.kind == AtomKind.PTR_EQ_PTR
        assert node.atom.ptr1 == "p->next"
        assert node.atom.ptr2 == "q"

    def test_compound_condition_with_field(self):
        """p && p->next parses as AND of two atoms."""
        node = parse_cond_full("p && p->next")
        assert node.kind == "and"
        assert node.left.kind == "atom"
        assert node.left.atom.kind == AtomKind.PTR_NE_NULL
        assert node.left.atom.ptr1 == "p"
        assert node.right.kind == "atom"
        assert node.right.atom.kind == AtomKind.PTR_NE_NULL
        assert node.right.atom.ptr1 == "p->next"

    def test_negated_field_access(self):
        node = parse_cond_full("!p->next")
        assert node.kind == "not"
        assert node.child.atom.ptr1 == "p->next"

    def test_field_access_missing_field_name(self):
        """p-> without field name should raise an error."""
        with pytest.raises(ValueError):
            parse_cond_full("p->")


# ---------------------------------------------------------------------------
# Integration: gen_coq_guard with field dereference
# ---------------------------------------------------------------------------

class TestCoqGuardFieldAccess:
    def test_field_access_root_null(self):
        """u->next in condition matches sll(u -> next, l1) in invariant."""
        inv = "sll(u -> next, l1) * sllseg(x, t, l2)"
        result = gen_coq_guard(inv, "u->next")
        assert result.strip().endswith("l1 <> []")

    def test_field_access_eq_null(self):
        inv = "sll(u -> next, l1) * sllseg(x, t, l2)"
        result = gen_coq_guard(inv, "u->next == null")
        assert "l1 = []" in result

    def test_field_access_with_no_space_in_inv(self):
        """Also works when invariant uses 'u->next' without spaces."""
        inv = "sll(u->next, l1)"
        result = gen_coq_guard(inv, "u->next")
        assert "l1 <> []" in result

    def test_compound_with_field_access(self):
        """p && p->next with matching spatial predicates."""
        inv = "sll(p, l1) * sll(p->next, l2)"
        result = gen_coq_guard(inv, "p && p->next")
        assert "l1 <> []" in result
        assert "l2 <> []" in result

    def test_regression_bare_pointer(self):
        """Existing bare pointer conditions still work."""
        inv = "sll(p, l1) * sll(q, l2)"
        result = gen_coq_guard(inv, "p")
        assert "l1 <> []" in result

    def test_regression_and_condition(self):
        """Existing x && y conditions still work."""
        inv = "sll(x, l1) * sll(y, l2)"
        result = gen_coq_guard(inv, "x && y")
        assert "l1 <> []" in result
        assert "l2 <> []" in result


# ---------------------------------------------------------------------------
# Pure equality alias resolution
# ---------------------------------------------------------------------------

class TestPureAliasExtraction:
    def test_basic_alias(self):
        aliases = extract_pure_aliases("exists w, u -> next == w && sll(w, l1)")
        assert aliases["u->next"] == "w"
        assert aliases["w"] == "u->next"

    def test_multiple_aliases(self):
        aliases = extract_pure_aliases(
            "exists w v, t -> next == w && t -> data == v && sll(w, l1)"
        )
        assert aliases["t->next"] == "w"
        assert aliases["t->data"] == "v"

    def test_no_numeric_aliases(self):
        """t == 0 should not create an alias (0 is numeric)."""
        aliases = extract_pure_aliases("t != 0 && t == 0 && sll(p, l1)")
        assert "t" not in aliases

    def test_no_null_aliases(self):
        aliases = extract_pure_aliases("p == null && sll(q, l1)")
        assert "p" not in aliases

    def test_plain_pointer_alias(self):
        aliases = extract_pure_aliases("x == y && sll(y, l1)")
        assert aliases["x"] == "y"
        assert aliases["y"] == "x"

    def test_empty_aliases(self):
        aliases = extract_pure_aliases("sll(p, l1) * sll(q, l2)")
        assert aliases == {}


class TestCoqGuardWithAliases:
    def test_field_access_via_alias(self):
        """u->next resolves through alias w to sll(w, l1)."""
        inv = "exists w, u -> next == w && sll(w, l1) * sllseg(x, t, l2)"
        result = gen_coq_guard(inv, "u->next")
        assert "l1 <> []" in result

    def test_field_access_eq_null_via_alias(self):
        inv = "exists w, u -> next == w && sll(w, l1)"
        result = gen_coq_guard(inv, "u->next == null")
        assert "l1 = []" in result

    def test_plain_pointer_alias(self):
        """x resolves through alias to sll(y, l1)."""
        inv = "x == y && sll(y, l1)"
        result = gen_coq_guard(inv, "x")
        assert "l1 <> []" in result

    def test_direct_still_preferred(self):
        """When pointer is directly in spatial, alias is not needed."""
        inv = "u -> next == w && sll(u -> next, l1) * sll(w, l2)"
        result = gen_coq_guard(inv, "u->next")
        assert "l1 <> []" in result


class TestGuardPredicateRegistryConfig:
    def test_builtin_predicates_loaded_from_json(self):
        assert "sll" in PREDICATES
        assert "sllseg" in PREDICATES
        assert "store_tree" in PREDICATES

    def test_json_loaded_root_null_rule(self):
        spec = PREDICATES["sll"]
        payload = spec.parse_args(["x", "l1"])
        assert spec.to_coq_root_null(payload, True) == "l1 = []"
        assert spec.to_coq_root_null(payload, False) == "l1 <> []"

    def test_json_loaded_segment_eq_rule(self):
        spec = PREDICATES["sllseg"]
        payload = spec.parse_args(["x", "y", "l1"])
        assert spec.to_coq_segment_eq(payload, True, False) == "l1 = []"
        assert spec.to_coq_segment_eq(payload, False, False) == "l1 <> []"

    def test_json_loaded_field_deref_null_rule_for_sll_next(self):
        spec = PREDICATES["sll"]
        payload = spec.parse_args(["x", "l1"])
        assert spec.to_coq_field_deref_null is not None
        assert spec.to_coq_field_deref_null(payload, "next", True) == "tl l1 = []"
        assert spec.to_coq_field_deref_null(payload, "next", False) == "tl l1 <> []"

    def test_sll_field_deref_unsupported_field_raises(self):
        spec = PREDICATES["sll"]
        payload = spec.parse_args(["x", "l1"])
        with pytest.raises(ValueError):
            spec.to_coq_field_deref_null(payload, "prev", False)

    def test_gen_coq_guard_x_next_via_sll_root(self):
        # Loop guard `x->next != 0` with invariant `sll(x, l2)` resolves via
        # the field-deref handler: the loop continues while the tail of l2
        # is non-empty (i.e. the list has ≥ 2 elements).
        inv = "exists l1 l2, x != 0 && sllseg(x@pre, x, l1) * sll(x, l2)"
        result = gen_coq_guard(inv, "x->next != 0")
        assert "tl l2 <> []" in result
        assert "Parameter" not in result

    def test_gen_coq_guard_single_var_binds_directly(self):
        # When the invariant has exactly one abstract variable, the guard
        # body references that variable name (``l1``) — the lambda binder
        # must use that name, not the fresh ``a``, otherwise the body's
        # ``l1`` is unbound.
        inv = "exists l1, sll(x, l1)"
        result = gen_coq_guard(inv, "x != 0")
        assert "fun l1 =>" in result
        assert "let '(" not in result
        assert "l1 <> []" in result
