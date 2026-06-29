"""Tests for the loop-forest analyser used by nested-loop codegen."""

import textwrap

import pytest

from GenMonads.absprog.loop_forest import (
    LoopNode,
    assign_invariants_in_source_order,
    assign_invariants_to_loops,
    build_loop_forest,
    build_loop_templates,
    top_level_loops,
)


def _mk_invs(n: int):
    """Build a list of minimal Inv-shaped assertion dicts (n entries) so
    ``build_loop_templates`` can pair them with detected loops in source
    order.  The placeholder body keeps each entry's ``variables`` /
    ``variable_types`` empty — exact contents don't matter for tests that
    care only about topology and early-return propagation flags.
    """
    return [
        {
            "type": "Inv",
            "variables": [],
            "variable_types": [],
            "translated": "exists , True",
            "command_guard": "True",
        }
        for _ in range(n)
    ]


def _src(code: str) -> str:
    return textwrap.dedent(code).lstrip("\n")


# ---------------------------------------------------------------------------
# Forest topology
# ---------------------------------------------------------------------------


def test_single_loop_no_parent():
    src = _src("""
        void f() {
            while (x) { x = x->next; }
        }
    """)
    loops = build_loop_forest(src)
    assert len(loops) == 1
    assert loops[0].keyword == "while"
    assert loops[0].parent is None
    assert loops[0].children == []
    assert top_level_loops(loops) == loops


def test_two_sequential_loops_share_no_parent():
    src = _src("""
        void f() {
            while (a) { a--; }
            while (b) { b--; }
        }
    """)
    loops = build_loop_forest(src)
    assert len(loops) == 2
    assert [lo.parent for lo in loops] == [None, None]
    assert [lo.children for lo in loops] == [[], []]
    # source order preserved
    assert loops[0].while_pos < loops[1].while_pos


def test_two_level_nesting():
    src = _src("""
        void f() {
            while (outer) {
                while (inner) { inner--; }
            }
        }
    """)
    loops = build_loop_forest(src)
    assert len(loops) == 2
    outer, inner = loops
    assert outer.parent is None
    assert inner.parent == outer.index
    assert outer.children == [inner.index]


def test_three_level_nesting_picks_immediate_parent():
    src = _src("""
        void f() {
            while (l1) {
                while (l2) {
                    while (l3) { l3--; }
                }
            }
        }
    """)
    loops = build_loop_forest(src)
    assert [lo.parent for lo in loops] == [None, 0, 1]
    assert loops[0].children == [1]
    assert loops[1].children == [2]


def test_mixed_nested_and_sequential_siblings():
    src = _src("""
        void f() {
            while (outer) {
                while (inner1) { inner1--; }
                while (inner2) { inner2--; }
            }
            while (sibling_of_outer) { x--; }
        }
    """)
    loops = build_loop_forest(src)
    assert len(loops) == 4
    outer, inner1, inner2, sibling = loops
    assert outer.parent is None
    assert sibling.parent is None
    assert inner1.parent == outer.index
    assert inner2.parent == outer.index
    assert outer.children == [inner1.index, inner2.index]


def test_for_loops_are_recognised():
    src = _src("""
        void f() {
            for (int i = 0; i < n; i++) {
                while (work) { work--; }
            }
        }
    """)
    loops = build_loop_forest(src)
    assert len(loops) == 2
    assert loops[0].keyword == "for"
    assert loops[1].keyword == "while"
    assert loops[1].parent == loops[0].index


# ---------------------------------------------------------------------------
# False-positive defences
# ---------------------------------------------------------------------------


def test_keyword_in_line_comment_is_ignored():
    src = _src("""
        void f() {
            // while (lie) { }
            while (real) { real--; }
        }
    """)
    loops = build_loop_forest(src)
    assert len(loops) == 1
    assert "real" in src[loops[0].while_pos:loops[0].while_pos + 40]


def test_keyword_in_block_comment_is_ignored():
    src = _src("""
        void f() {
            /* while (lie) { } */
            for (int i = 0; i < n; i++) { ; }
        }
    """)
    loops = build_loop_forest(src)
    assert len(loops) == 1
    assert loops[0].keyword == "for"


def test_keyword_in_qcp_annotation_is_ignored():
    # Inv annotations live in /*@ ... */ blocks; the keyword may legitimately
    # appear inside the annotation text.
    src = _src("""
        void f() {
            /*@ Inv exists l, listrep(while_x) */
            while (x) { x--; }
        }
    """)
    loops = build_loop_forest(src)
    assert len(loops) == 1


def test_keyword_in_string_literal_is_ignored():
    src = _src("""
        void f() {
            const char *s = "while (";
            while (x) { x--; }
        }
    """)
    loops = build_loop_forest(src)
    assert len(loops) == 1


def test_identifier_starting_with_while_is_not_a_loop():
    src = _src("""
        void f() {
            int while_count = 0;
            while_count = while_count + 1;
        }
    """)
    loops = build_loop_forest(src)
    assert loops == []


def test_loop_without_braces_is_skipped():
    # We require braced bodies (single-statement loops aren't useful targets
    # for the scaffold and are absent from this project's fixtures).
    src = _src("""
        void f() {
            while (x)
                x = x->next;
            while (y) { y--; }
        }
    """)
    loops = build_loop_forest(src)
    assert len(loops) == 1  # only the braced one


# ---------------------------------------------------------------------------
# Invariant assignment
# ---------------------------------------------------------------------------


def test_assign_invariants_pairs_each_inv_with_following_loop():
    src = _src("""
        void f() {
            /*@ Inv outer */
            while (a) {
                /*@ Inv inner */
                while (b) { b--; }
            }
        }
    """)
    loops = build_loop_forest(src)
    inv_outer_pos = src.find("/*@ Inv outer")
    inv_inner_pos = src.find("/*@ Inv inner")
    assert inv_outer_pos != -1 and inv_inner_pos != -1
    assign_invariants_to_loops(loops, [inv_outer_pos, inv_inner_pos])
    outer = next(lo for lo in loops if lo.parent is None)
    inner = next(lo for lo in loops if lo.parent == outer.index)
    assert outer.inv_index == 0
    assert inner.inv_index == 1


def test_assign_invariants_handles_inv_between_siblings():
    src = _src("""
        void f() {
            /*@ Inv first */
            while (a) { a--; }
            /*@ Inv second */
            while (b) { b--; }
        }
    """)
    loops = build_loop_forest(src)
    p1 = src.find("/*@ Inv first")
    p2 = src.find("/*@ Inv second")
    assign_invariants_to_loops(loops, [p1, p2])
    assert loops[0].inv_index == 0
    assert loops[1].inv_index == 1


def test_assign_invariants_silently_ignores_orphaned_inv():
    src = _src("""
        void f() {
            while (a) { a--; }
            /*@ Inv orphan */
        }
    """)
    loops = build_loop_forest(src)
    pos = src.find("/*@ Inv orphan")
    assign_invariants_to_loops(loops, [pos])
    # The Inv comes AFTER the only loop; nothing follows it, so nothing assigned.
    assert loops[0].inv_index is None


def test_empty_source_yields_empty_forest():
    assert build_loop_forest("") == []
    assert top_level_loops([]) == []


def test_assign_invariants_on_empty_forest_is_noop():
    assign_invariants_to_loops([], [42])  # must not raise
    assign_invariants_in_source_order([], 3)  # must not raise


def test_assign_invariants_in_source_order_nested():
    src = _src("""
        void f() {
            while (outer) {
                while (inner) { inner--; }
            }
        }
    """)
    loops = build_loop_forest(src)
    assign_invariants_in_source_order(loops, num_invariants=2)
    outer = next(lo for lo in loops if lo.parent is None)
    inner = next(lo for lo in loops if lo.parent == outer.index)
    assert outer.inv_index == 0
    assert inner.inv_index == 1


def test_assign_invariants_in_source_order_ignores_extra():
    src = _src("void f() { while (a) { a--; } }")
    loops = build_loop_forest(src)
    assign_invariants_in_source_order(loops, num_invariants=5)
    assert loops[0].inv_index == 0  # only the first invariant is consumed


# ---------------------------------------------------------------------------
# Per-loop early-return classification (direct + transitive)
# ---------------------------------------------------------------------------


def test_template_early_return_direct_on_single_top_level_loop():
    src = _src("""
        int f(int n) {
            while (n > 0) {
                if (n == 1) { return -1; }
                n--;
            }
            return 0;
        }
    """)
    templates = build_loop_templates("f", src, _mk_invs(1))
    assert len(templates) == 1
    t = templates[0]
    assert t["has_early_return"] is True
    assert t["has_early_return_in_subtree"] is True


def test_template_no_early_return_when_loop_clean():
    src = _src("""
        int f(int n) {
            while (n > 0) { n--; }
            return 0;
        }
    """)
    templates = build_loop_templates("f", src, _mk_invs(1))
    assert templates[0]["has_early_return"] is False
    assert templates[0]["has_early_return_in_subtree"] is False


def test_template_inner_early_return_propagates_to_outer():
    """If a nested loop has an early return, the enclosing loop is tainted
    too — control physically passes through the outer to leave the
    function.  Both must surface ``has_early_return_in_subtree=True`` even
    though only the inner has ``has_early_return=True`` directly."""
    src = _src("""
        int f(int n, int m) {
            while (n > 0) {
                while (m > 0) {
                    if (m == 7) { return -1; }
                    m--;
                }
                n--;
            }
            return 0;
        }
    """)
    templates = build_loop_templates("f", src, _mk_invs(2))
    assert len(templates) == 2
    outer = next(t for t in templates if t["parent"] is None)
    inner = next(t for t in templates if t["parent"] is not None)
    assert inner["has_early_return"] is True
    assert outer["has_early_return"] is False  # outer's own body has no return
    # …but propagation taints the outer's subtree:
    assert inner["has_early_return_in_subtree"] is True
    assert outer["has_early_return_in_subtree"] is True


def test_template_sequential_top_level_loops_classified_independently():
    """Sequential (non-nested) top-level loops don't share an enclosing
    loop, so an early return in the first does NOT taint the second's
    subtree.  Each top-level loop's flag stands alone."""
    src = _src("""
        int f(int n) {
            while (n > 0) {
                if (n == 1) { return -1; }
                n--;
            }
            while (n < 100) { n++; }
            return n;
        }
    """)
    templates = build_loop_templates("f", src, _mk_invs(2))
    assert len(templates) == 2
    # Source order corresponds to template order.
    first, second = templates
    assert first["has_early_return_in_subtree"] is True
    assert second["has_early_return_in_subtree"] is False


def test_template_outer_only_early_return_no_inner():
    """An early return in the outer loop's body — but outside the inner —
    taints the outer but not the inner."""
    src = _src("""
        int f(int n, int m) {
            while (n > 0) {
                if (n == 3) { return -1; }
                while (m > 0) { m--; }
                n--;
            }
            return 0;
        }
    """)
    templates = build_loop_templates("f", src, _mk_invs(2))
    outer = next(t for t in templates if t["parent"] is None)
    inner = next(t for t in templates if t["parent"] is not None)
    assert outer["has_early_return"] is True
    assert inner["has_early_return"] is False
    assert outer["has_early_return_in_subtree"] is True
    assert inner["has_early_return_in_subtree"] is False
