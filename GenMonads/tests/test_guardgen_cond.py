"""Tests for GuardGen condition parser field dereference (->)  support."""
import pytest
from GenMonads.guardgen.registry import PREDICATES
from GenMonads.guardgen.cond.lexer import lex_cond
from GenMonads.guardgen.cond.parser import parse_cond_full
from GenMonads.guardgen.cond.ast import AtomKind
from GenMonads.guardgen import gen_coq_guard
from GenMonads.guardgen.parsing.invariant import extract_pure_aliases, parse_invariant


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

    def test_sllseg_has_no_ungated_segment_eq_primitive(self):
        # Segment emptiness is NOT a per-predicate primitive anymore: emitting
        # ``l = []`` off a bare ``sllseg`` is unsound (a lasso breaks it).  The
        # rule now lives ONLY as the acyclicity-gated ``_composition_rules
        # .segment_eq`` (a root must terminate the segment), so ``sllseg`` ships
        # no direct ``to_coq_segment_eq`` handler.
        assert PREDICATES["sllseg"].to_coq_segment_eq is None

    def test_json_loaded_segment_eq_composition_rules(self):
        from GenMonads.guardgen.registry import COMPOSITION_RULES
        names = {r.name for r in COMPOSITION_RULES.get("segment_eq", [])}
        # Both endpoint orderings are registered from the JSON, each requiring a
        # trailing root (role "R") as the acyclicity witness.
        assert names == {"seg_eq_forward_rooted", "seg_eq_reversed_rooted"}
        for rule in COMPOSITION_RULES["segment_eq"]:
            kinds = [clause["kind"] for clause in rule.match]
            assert kinds == ["segment", "root"]

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


class TestSegmentEqAcyclicity:
    """``start = end  <=>  l = []`` for ``sllseg(start, end, l)`` is only sound
    when a root ``sll(end, _)`` terminates the segment (rules out a lasso).  The
    guard generator must require that acyclicity witness rather than reading the
    emptiness off the bare segment predicate."""

    def test_segment_eq_with_trailing_root_emits(self):
        # ``node->next != stop`` over ``sllseg(nxt, stop, l2) * sll(stop, l3)``
        # (the iter_back inner-loop shape): the trailing ``sll(stop, _)`` is the
        # acyclicity witness, so the segment-emptiness guard is emitted.
        inv = (
            "exists nxt l2 l3, store(&(node->next), struct list *, nxt) * "
            "sllseg(nxt, stop, l2) * sll(stop, l3)"
        )
        result = gen_coq_guard(inv, "node->next != stop")
        assert "l2 <> []" in result
        assert "Parameter" not in result

    def test_segment_eq_endpoints_either_order(self):
        # Same shape, operands written in the reverse order (``stop != nxt``):
        # the emitted guard is unchanged (segment emptiness is symmetric).
        inv = "exists l2 l3, sllseg(nxt, stop, l2) * sll(stop, l3)"
        assert "l2 <> []" in gen_coq_guard(inv, "nxt != stop")
        assert "l2 <> []" in gen_coq_guard(inv, "stop != nxt")

    def test_segment_eq_without_trailing_root_refuses(self):
        # A dangling segment with no root at its end could be circular, so the
        # naive ``x = y <=> l = []`` rule is unsound — the generator must refuse.
        inv = "exists l2, sllseg(nxt, stop, l2)"
        with pytest.raises(ValueError, match="acyclicity witness|rule out a cycle"):
            gen_coq_guard(inv, "nxt != stop")


class TestMemoryStatePredicatesIgnored:
    """Memory-state predicates (``store``, ``undef_data_at``) are not shape
    predicates and must be skipped by the invariant parser rather than raising
    `Unknown predicate`.  They never root at the loop pointer, so the guard is
    derived purely from the shape atoms."""

    def test_parse_invariant_skips_store(self):
        atoms = parse_invariant(
            "exists s l1 l2, store(&sum, long, s) * sllseg(h, c, l1) * sll(c, l2)"
        )
        names = [a.spec.name for a in atoms]
        assert names == ["sllseg", "sll"]

    def test_parse_invariant_skips_undef_data_at(self):
        atoms = parse_invariant(
            "exists l, undef_data_at(&tmp, int) * sll(p, l)"
        )
        assert [a.spec.name for a in atoms] == ["sll"]

    def test_parse_invariant_still_rejects_unknown_shape_predicate(self):
        with pytest.raises(ValueError, match="Unknown predicate 'bogus'"):
            parse_invariant("exists l, bogus(p, l) * sll(p, l)")

    def test_gen_coq_guard_with_store_clause(self):
        # A sum-accumulator loop: the `store(&acc, ...)` clause must not block
        # guard generation; the guard comes from `sll(cur, l2)`.
        inv = "exists s l1 l2, store(&acc, long, s) * sllseg(head, cur, l1) * sll(cur, l2)"
        result = gen_coq_guard(inv, "cur != 0", extra_vars=["s"])
        assert "l2 <> []" in result
        assert "Parameter" not in result

    def test_gen_coq_guard_with_desugared_field_store(self):
        # `p->data == v` desugars to `store(&(p->data), int, v)`; guard still
        # resolves from the `sll(p, l)` atom.
        inv = "exists v l, store(&(p->data), int, v) * sll(p, l)"
        result = gen_coq_guard(inv, "p != 0", extra_vars=["v"])
        assert "l <> []" in result
        assert "Parameter" not in result


# ---------------------------------------------------------------------------
# Scalar loop-condition support (while (i < n), etc.)
# ---------------------------------------------------------------------------

from GenMonads.guardgen.cond.ast import AtomKind as _AK
from GenMonads.guardgen.cond.parser import parse_cond_full as _parse_cond
from GenMonads.guardgen.parsing.invariant import extract_store_bindings


class TestScalarLexer:
    def test_lexes_ordering_operators(self):
        assert [t.kind for t in lex_cond("i < n")] == ["ID", "LT", "ID"]
        assert [t.kind for t in lex_cond("i <= n")] == ["ID", "LE", "ID"]
        assert [t.kind for t in lex_cond("i > n")] == ["ID", "GT", "ID"]
        assert [t.kind for t in lex_cond("i >= n")] == ["ID", "GE", "ID"]

    def test_lexes_multi_digit_numbers(self):
        toks = lex_cond("i < 100")
        assert toks[-1].kind == "NUM"
        assert toks[-1].text == "100"

    def test_arrow_not_confused_with_gt(self):
        assert [t.kind for t in lex_cond("p->next")] == ["ID", "ARROW", "ID"]

    def test_ne2_not_confused_with_lt(self):
        # `<>` must lex as a single NE2 token, not LT followed by GT.
        assert [t.kind for t in lex_cond("x <> 0")] == ["ID", "NE2", "NUM"]


class TestScalarParser:
    def test_ordering_produces_scalar_cmp(self):
        node = _parse_cond("i < n")
        assert node.kind == "atom"
        assert node.atom.kind == _AK.SCALAR_CMP
        assert (node.atom.ptr1, node.atom.op, node.atom.ptr2) == ("i", "<", "n")

    def test_nonzero_eq_is_scalar(self):
        node = _parse_cond("i == 5")
        assert node.atom.kind == _AK.SCALAR_CMP
        assert node.atom.op == "=="

    def test_zero_eq_stays_pointer_null(self):
        node = _parse_cond("p == 0")
        assert node.atom.kind == _AK.PTR_EQ_NULL

    def test_ident_eq_stays_pointer(self):
        node = _parse_cond("p == q")
        assert node.atom.kind == _AK.PTR_EQ_PTR


class TestStoreBindings:
    def test_simple_var(self):
        b = extract_store_bindings("exists vi, store(&i, int, vi) * sll(x, l)")
        assert b == {"i": "vi"}

    def test_multiple_and_field(self):
        b = extract_store_bindings(
            "store(&i,int,vi) * store(&sum,long,s) * store(&(p->data),int,v)"
        )
        assert b == {"i": "vi", "sum": "s", "p->data": "v"}


class TestScalarGuard:
    INV = "exists vi vn, store(&i, int, vi) * store(&n, int, vn)"

    def test_less_than(self):
        out = gen_coq_guard(self.INV, "i < n", extra_vars=["vi", "vn"])
        assert "vi < vn" in out
        assert "Parameter" not in out

    def test_less_equal(self):
        out = gen_coq_guard(self.INV, "i <= n", extra_vars=["vi", "vn"])
        assert "vi <= vn" in out

    def test_greater_than_literal(self):
        out = gen_coq_guard(self.INV, "i > 0", extra_vars=["vi", "vn"])
        assert "vi > 0" in out

    def test_eq_literal(self):
        out = gen_coq_guard(self.INV, "i == 5", extra_vars=["vi", "vn"])
        assert "vi = 5" in out

    def test_ne_zero_scalar_fallback(self):
        # `i != 0` with `i` store-bound is a scalar check, not a null check.
        out = gen_coq_guard(self.INV, "i != 0", extra_vars=["vi", "vn"])
        assert "vi <> 0" in out

    def test_eq_between_scalars(self):
        out = gen_coq_guard(self.INV, "i == n", extra_vars=["vi", "vn"])
        assert "vi = vn" in out

    def test_mixed_scalar_and_shape_state_order(self):
        inv = "exists vi vn l, store(&i,int,vi) * store(&n,int,vn) * sll(cur, l)"
        out = gen_coq_guard(inv, "cur != 0 && i < n", extra_vars=["vi", "vn"])
        # shape var first (from sll), then the scalar witnesses.
        assert "let '(l, vi, vn) := a in" in out
        assert "l <> []" in out
        assert "vi < vn" in out

    def test_unbound_scalar_operand_errors(self):
        # `j` has no store binding -> cannot resolve.
        with pytest.raises(ValueError, match="not a store-bound scalar"):
            gen_coq_guard(self.INV, "i < j", extra_vars=["vi", "vn"])

    def test_pointer_null_still_works(self):
        # Regression: no scalar bindings, plain list guard unaffected.
        out = gen_coq_guard("exists l, sll(x, l)", "x != 0")
        assert "l <> []" in out
        assert "Parameter" not in out
