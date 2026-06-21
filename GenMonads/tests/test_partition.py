"""Tests for the Phase-1 C-source partitioner and the Phase-2 scaffold
annotations.

Covers the five block types from ``TODO/block_partition_refactor_plan.md``:
``Others``, ``IfNoReturn``, ``IfWithReturn``, ``WhileNoReturn``,
``WhileWithReturn``.

All fixtures are inline synthetic C — no dependency on any specific
dataset path.  The shapes mirror real verification-pipeline-compatible
inputs so the end-to-end tests (context + prompt) exercise the same code
paths a production run would.
"""

import pytest

from GenMonads.absprog.partition import (
    IfNoReturn,
    IfWithReturn,
    Others,
    WhileNoReturn,
    WhileWithReturn,
    partition_function_body,
    blocks_to_list,
)


# ---------------------------------------------------------------------------
# Synthetic fixtures — every test gets its C input from one of these
# constants (or writes one to ``tmp_path`` when a file path is needed).


# NOTE on fixture style: we do NOT inline ``struct list { ... };``
# definitions in these fixtures.  ``early_return.extract_function_body``
# locates the function body via the first ``{`` and last ``}`` in the
# source; an inline struct definition's braces would steal the
# "function-body" slot.  Real dataset files reach the same shape by
# ``#include``-ing the struct from a header, so the first ``{`` is
# always the function's.  We mirror that by relying on implicit
# ``struct list`` (forward-used).


# Shape 2 (no-loop early-return) — analogue of ``list_append_raw.c``.
_NO_LOOP_EARLY_RETURN_SRC = (
    'struct list *demo(struct list *x, struct list *y)\n'
    '/*@ Require listrep(x) * listrep(y)\n'
    '    Ensure  listrep(__return)\n'
    ' */\n'
    '{\n'
    '    struct list *tail;\n'
    '\n'
    '    if (x == 0) {\n'
    '        return y;\n'
    '    }\n'
    '\n'
    '    tail = helper(x);\n'
    '    tail->next = y;\n'
    '    return x;\n'
    '}\n'
)


# Shape 3 (single loop with pre-loop early-return guard) — analogue of
# ``list_tail.c``.
_LOOP_WITH_PRE_GUARD_SRC = (
    'struct list *demo(struct list *x)\n'
    '/*@ Require x != 0 && listrep(x)\n'
    '    Ensure  exists v, __return != 0 &&\n'
    '            __return -> next == 0 &&\n'
    '            __return -> data == v &&\n'
    '            lseg(x, __return)\n'
    '*/\n'
    '{\n'
    '    if (x == 0) {\n'
    '        return 0;\n'
    '    }\n'
    '\n'
    '    /*@ Inv Assert\n'
    '            x != 0 &&\n'
    '            lseg(x@pre, x) *\n'
    '            listrep(x)\n'
    '     */\n'
    '    while (x->next != 0) {\n'
    '        x = x->next;\n'
    '    }\n'
    '    return x;\n'
    '}\n'
)


# Shape 1 (straight-line — opaque ``M``) — analogue of ``glibc_slist_app.c``.
_STRAIGHT_LINE_SRC = (
    'struct list *demo(struct list *x, struct list *y)\n'
    '/*@ Require listrep(x) * listrep(y)\n'
    '    Ensure  listrep(__return)\n'
    ' */\n'
    '{\n'
    '    return helper(x, y);\n'
    '}\n'
)


# Shape 3 (single loop whose body IS the entire function) — analogue of
# ``glibc_slist_free.c``: no pre-loop work, no post-loop return.
_LOOP_ONLY_SRC = (
    'void demo(struct list *x)\n'
    '/*@ Require listrep(x)\n'
    '    Ensure  emp\n'
    ' */\n'
    '{\n'
    '    struct list *next;\n'
    '\n'
    '    /*@ Inv Assert undef_data_at(&next, struct list*) * listrep(x)\n'
    '     */\n'
    '    while (x != 0) {\n'
    '        next = x->next;\n'
    '        free_node(x);\n'
    '        x = next;\n'
    '    }\n'
    '}\n'
)


# Shape 3 with no early-return guard, loop produces a final value used by
# the post-loop return.  Used by `glibc_slist_iter`-style assertions.
_LOOP_WITH_PRE_AND_POST_SRC = (
    'long demo(struct list *x)\n'
    '/*@ Require listrep(x)\n'
    '    Ensure  emp\n'
    ' */\n'
    '{\n'
    '    long sum;\n'
    '    sum = 0;\n'
    '    /*@ Inv exists s, store(&sum, long, s) * listrep(x) */\n'
    '    while (x != 0) {\n'
    '        sum += x->data;\n'
    '        x = x->next;\n'
    '    }\n'
    '    return sum;\n'
    '}\n'
)


# Multi-loop function — falls into the forest scaffold, scaffold_segments
# stays empty.  Mirrors `glibc_slist_iter_back_2.c`'s nested-loop shape.
_MULTI_LOOP_SRC = (
    'long demo(struct list *x)\n'
    '/*@ Require listrep(x)\n'
    '    Ensure  emp\n'
    ' */\n'
    '{\n'
    '    struct list *stop;\n'
    '    long sum;\n'
    '\n'
    '    stop = 0;\n'
    '    sum = 0;\n'
    '    /*@ Inv exists st s,\n'
    '            store(&stop, struct list*, st) *\n'
    '            store(&sum, long, s) *\n'
    '            listrep(x)\n'
    '     */\n'
    '    while (x != stop) {\n'
    '        /*@ Inv exists st s,\n'
    '                store(&stop, struct list*, st) *\n'
    '                store(&sum, long, s) *\n'
    '                listrep(x)\n'
    '         */\n'
    '        while (x->next != stop) {\n'
    '            x = x->next;\n'
    '        }\n'
    '        sum += x->data;\n'
    '        stop = x;\n'
    '    }\n'
    '    return sum;\n'
    '}\n'
)


def _write_fixture(tmp_path, name: str, src: str) -> str:
    """Write a synthetic C source under *tmp_path* and return its path.

    Used by tests that drive the full pipeline (``collect_synthesis_context``,
    ``generate_rel_lib_for_file``) which need a file path on disk.
    """
    path = tmp_path / f"{name}.c"
    path.write_text(src, encoding="utf-8")
    return str(path)


# ---------------------------------------------------------------------------
# Real-shape partitioning — exercises the partitioner on synthetic
# C that mirrors the verification-pipeline's input shape.


def test_partition_no_loop_early_return_shape():
    """Canonical early-return-then-work shape: an early
    `if (x == 0) return y;` followed by post-decision body with a
    cross-file call.  Bug 3 from the design plan."""
    blocks = partition_function_body(_NO_LOOP_EARLY_RETURN_SRC)
    assert len(blocks) == 2
    assert isinstance(blocks[0], IfWithReturn)
    assert blocks[0].cond == "x == 0"
    assert blocks[0].then_terminates is True
    assert blocks[0].else_terminates is False
    # Then-body contains exactly one Others with the bare `return y;`
    assert len(blocks[0].then_body) == 1
    assert isinstance(blocks[0].then_body[0], Others)
    assert "return y;" in blocks[0].then_body[0].raw_c_text
    # Else-body empty (no else in C source)
    assert blocks[0].else_body == []
    # Trailing Others: call + assignment + terminal return
    assert isinstance(blocks[1], Others)
    assert "helper(x)" in blocks[1].raw_c_text
    assert "tail->next = y" in blocks[1].raw_c_text
    assert "return x;" in blocks[1].raw_c_text
    assert blocks[1].contains_terminal_return is True


def test_partition_recursive_no_loop_early_return():
    """Same shape as the above, but the post-decision body uses a
    recursive call instead of an external one — verifies the partitioner
    doesn't care about the call target."""
    src = (
        'long demo(struct list *x)\n'
        '/*@ Require listrep(x) Ensure emp */\n'
        '{\n'
        '    long sum;\n'
        '    if (x == 0) { return 0; }\n'
        '    sum = demo(x->next);\n'
        '    return sum + x->data;\n'
        '}\n'
    )
    blocks = partition_function_body(src)
    assert len(blocks) == 2
    assert isinstance(blocks[0], IfWithReturn)
    assert blocks[0].cond == "x == 0"
    assert isinstance(blocks[1], Others)
    assert blocks[1].contains_terminal_return is True


def test_partition_loop_after_early_return():
    """Early-return guard followed by a while loop followed by a terminal
    return.  Three blocks: IfWithReturn, then WhileNoReturn, then a
    trailing Others holding the return."""
    blocks = partition_function_body(_LOOP_WITH_PRE_GUARD_SRC)
    assert [type(b).__name__ for b in blocks] == [
        "IfWithReturn", "WhileNoReturn", "Others",
    ]
    assert blocks[1].cond == "x->next != 0"
    assert blocks[1].keyword == "while"
    # Loop body is an Others holding the iteration step.
    assert len(blocks[1].body) == 1
    assert isinstance(blocks[1].body[0], Others)
    assert "x = x->next" in blocks[1].body[0].raw_c_text
    # Trailing Others carries the terminal return.
    assert blocks[2].contains_terminal_return is True
    assert "return x;" in blocks[2].raw_c_text


# ---------------------------------------------------------------------------
# Synthetic shapes


_INTERLEAVED_C = """
struct list *demo(struct list *x, struct list *y) {
    if (x == 0) return y;
    real_work1();
    if (y == 0) return x;
    real_work2();
    return x;
}
"""


def test_partition_interleaved_early_returns():
    """The shape the user raised in design discussion: two early returns
    separated by real work.  Four blocks alternating IfWithReturn /
    Others."""
    blocks = partition_function_body(_INTERLEAVED_C)
    assert [type(b).__name__ for b in blocks] == [
        "IfWithReturn", "Others", "IfWithReturn", "Others",
    ]
    assert blocks[0].cond == "x == 0"
    assert blocks[2].cond == "y == 0"
    # Both IfWithReturn blocks have a terminating then and a continuing else.
    for if_block in (blocks[0], blocks[2]):
        assert if_block.then_terminates is True
        assert if_block.else_terminates is False
    # Trailing Others holds the final return.
    assert blocks[3].contains_terminal_return is True
    assert "real_work2" in blocks[3].raw_c_text
    assert "return x;" in blocks[3].raw_c_text


_NESTED_LOOP_INNER_RETURN_C = """
long check_all(struct list *p) {
    while (p) {
        if (p->data < 0) return -1;
        p = p->next;
    }
    return 0;
}
"""


def test_partition_outer_loop_inherits_with_return_via_nesting():
    """S1 from the design plan: a `return` inside an inner block (in this
    case inside an `if` inside the loop body) propagates upward — the
    outer loop must classify as WhileWithReturn even though no `return`
    appears at the loop's direct body level."""
    blocks = partition_function_body(_NESTED_LOOP_INNER_RETURN_C)
    assert [type(b).__name__ for b in blocks] == ["WhileNoReturn", "Others"] \
        or [type(b).__name__ for b in blocks] == ["WhileWithReturn", "Others"]
    # The actual assertion: the outer loop must be the with_return variant
    # because there's a `return` reachable via the inner `if`.
    assert isinstance(blocks[0], WhileWithReturn), (
        "outer loop's return-classification must be transitive: an inner "
        "`return` propagates up through enclosing loops"
    )
    # Inner block: IfWithReturn (with `return -1;`) + Others.
    inner = blocks[0].body
    assert [type(b).__name__ for b in inner] == ["IfWithReturn", "Others"]
    assert inner[0].cond == "p->data < 0"
    assert inner[0].then_terminates is True


_DOUBLY_NESTED_C = """
long deeper(struct list *p) {
    while (p) {
        while (p->next) {
            if (p->data < 0) return -1;
            p = p->next;
        }
    }
    return 0;
}
"""


def test_partition_doubly_nested_return_propagates_to_outermost_loop():
    """Three nested layers (outer while → inner while → if-return).  All
    loop layers must classify as WhileWithReturn because the inner return
    propagates outward through every level."""
    blocks = partition_function_body(_DOUBLY_NESTED_C)
    assert isinstance(blocks[0], WhileWithReturn)
    inner_loop = blocks[0].body[0]
    assert isinstance(inner_loop, WhileWithReturn)
    inner_if = inner_loop.body[0]
    assert isinstance(inner_if, IfWithReturn)
    assert inner_if.then_terminates is True


_BOTH_BRANCHES_RETURN_C = """
int choose(int x, int y) {
    if (x > y) {
        return x;
    } else {
        return y;
    }
}
"""


def test_partition_both_branches_return_no_trailing_block():
    """Both branches terminate the function → the IfWithReturn block IS
    the function tail; no trailing Others.  Renderer will collapse the
    outer match (no Continue path)."""
    blocks = partition_function_body(_BOTH_BRANCHES_RETURN_C)
    assert len(blocks) == 1
    assert isinstance(blocks[0], IfWithReturn)
    assert blocks[0].then_terminates is True
    assert blocks[0].else_terminates is True


_ELSE_BRANCH_RETURNS_C = """
int choose(int x, int y) {
    if (x > y) {
        y = compute(x);
    } else {
        return -1;
    }
    return y;
}
"""


def test_partition_else_branch_returns_block_owns_both_branches():
    """When only the ELSE branch returns, the IfWithReturn carries both
    branches (no else-hoisting per the revised design — the block owns
    its branches structurally)."""
    blocks = partition_function_body(_ELSE_BRANCH_RETURNS_C)
    assert isinstance(blocks[0], IfWithReturn)
    assert blocks[0].then_terminates is False   # then continues
    assert blocks[0].else_terminates is True
    # Else-body carries the `return -1;`.
    assert blocks[0].else_body
    assert "return -1" in blocks[0].else_body[0].raw_c_text
    # Then-body carries `y = compute(x);`.
    assert blocks[0].then_body
    assert "compute(x)" in blocks[0].then_body[0].raw_c_text
    # Trailing Others has the terminal `return y;`.
    assert isinstance(blocks[1], Others)
    assert blocks[1].contains_terminal_return is True


_IF_NO_RETURN_C = """
void update(int x, int y) {
    int z;
    if (x > y) {
        z = x;
    } else {
        z = y;
    }
    use(z);
}
"""


def test_partition_if_no_return_when_neither_branch_returns():
    """Plain conditional with no return in either branch maps to
    IfNoReturn — the renderer will emit `choice (assume!! cond ;; then)
    (assume!! !cond ;; else)` without `early_result` wrapping."""
    blocks = partition_function_body(_IF_NO_RETURN_C)
    # Decl `int z;` stripped; then IfNoReturn; then Others.
    types = [type(b).__name__ for b in blocks]
    assert "IfNoReturn" in types
    if_block = next(b for b in blocks if isinstance(b, IfNoReturn))
    assert if_block.cond == "x > y"
    assert if_block.then_body
    assert if_block.else_body


# ---------------------------------------------------------------------------
# Edge cases


def test_partition_single_return_body_is_one_others():
    """Function body that is literally `return X;` becomes one Others
    block with `contains_terminal_return=True`."""
    blocks = partition_function_body("int trivial() { return 42; }")
    assert len(blocks) == 1
    assert isinstance(blocks[0], Others)
    assert blocks[0].contains_terminal_return is True
    assert "return 42" in blocks[0].raw_c_text


def test_partition_drops_bare_declarations():
    """Bare variable declarations (no initializer) are dropped per P2."""
    src = """
    void demo() {
        struct list *tail;
        long sum;
        int *p;
        work();
    }
    """
    blocks = partition_function_body(src)
    assert len(blocks) == 1
    assert isinstance(blocks[0], Others)
    # None of the bare declarations leaked through.
    text = blocks[0].raw_c_text
    assert "struct list *tail" not in text
    assert "long sum" not in text
    assert "int *p" not in text
    assert "work()" in text


def test_partition_keeps_initialized_declarations():
    """`int x = foo();` is real work (a function call), not a declaration
    — it must NOT be dropped."""
    src = "int demo() { int x = foo(); return x; }"
    blocks = partition_function_body(src)
    assert len(blocks) == 1
    assert "int x = foo()" in blocks[0].raw_c_text


def test_partition_keeps_return_statements_against_naive_decl_regex():
    """Regression: a naive declaration regex sees `return X;` as
    `<type> <var>;` and drops it.  We exclude control-flow keywords."""
    src = "int demo() { return some_value; }"
    blocks = partition_function_body(src)
    assert len(blocks) == 1
    assert "return some_value" in blocks[0].raw_c_text
    assert blocks[0].contains_terminal_return is True


def test_partition_comments_stripped_from_partitioning():
    """C comments are removed before partitioning so they don't shift
    positions or false-match `return` inside `/* ... */`."""
    src = """
    void demo() {
        /* return early on failure */
        if (x == 0) {
            return;
        }
        /* return total */
        result = work();
    }
    """
    blocks = partition_function_body(src)
    # The IfWithReturn was detected (the comment didn't false-classify
    # the previous gap as containing a return).
    types = [type(b).__name__ for b in blocks]
    assert "IfWithReturn" in types


def test_partition_jsonable_via_blocks_to_list():
    """`blocks_to_list` produces JSON-friendly nested dicts for the CLI
    debug dump."""
    data = blocks_to_list(partition_function_body(_LOOP_WITH_PRE_GUARD_SRC))
    assert isinstance(data, list)
    # Top-level structure.
    assert data[0]["type"] == "IfWithReturn"
    # then_body is a nested list of dicts.
    assert isinstance(data[0]["then_body"], list)
    assert data[0]["then_body"][0]["type"] == "Others"
    # Loop body recursively serialised.
    assert data[1]["type"] == "WhileNoReturn"
    assert data[1]["body"][0]["type"] == "Others"


def test_partition_no_specials_yields_one_others():
    """Function body with no `if` / `while` / `for` at all becomes a
    single Others block."""
    src = "int demo() { x = y + z; foo(); return x; }"
    blocks = partition_function_body(src)
    assert len(blocks) == 1
    assert isinstance(blocks[0], Others)


def test_partition_empty_function_body():
    """Empty body produces an empty block list."""
    blocks = partition_function_body("void demo() {}")
    assert blocks == []


# ---------------------------------------------------------------------------
# Regression: `else if … else` chains used to drop the trailing else.


_ELSE_IF_ELSE_CHAIN_C = """
void demo(int x) {
    if (a) {
        path_a();
    } else if (b) {
        path_b();
    } else {
        path_c();
    }
    after();
}
"""


def test_partition_else_if_else_chain_nests_correctly():
    """Regression for the `glibc_slist_clean_multi_merge` bug: an
    `else if … else` chain was being clipped to the `else if` only,
    leaving the final `else { … }` orphaned in the following Others gap.
    The fix consumes the full composite if-else chain via
    `_consume_statement_with_else_chain`."""
    blocks = partition_function_body(_ELSE_IF_ELSE_CHAIN_C)
    assert isinstance(blocks[0], IfNoReturn)
    # Outer if's else_body holds the nested `if (b) ... else { ... }`.
    assert len(blocks[0].else_body) == 1
    inner = blocks[0].else_body[0]
    assert isinstance(inner, IfNoReturn)
    assert inner.cond == "b"
    # Inner if has both branches.
    assert inner.then_body and "path_b" in inner.then_body[0].raw_c_text
    assert inner.else_body and "path_c" in inner.else_body[0].raw_c_text
    # No `else` token leaks into a sibling Others.
    for block in blocks:
        if isinstance(block, Others):
            assert "else" not in block.raw_c_text, (
                "else clause leaked into a sibling Others — chain wasn't fully consumed"
            )
    # Trailing `after();` is its own Others.
    assert any(
        isinstance(b, Others) and "after()" in b.raw_c_text for b in blocks
    )


def test_partition_three_way_chain_with_return_classifies_correctly():
    """An `else if … else` chain where one branch returns must produce
    `IfWithReturn` with the correct terminating flags."""
    src = """
    int demo(int a, int b) {
        if (a) {
            return 1;
        } else if (b) {
            do_b();
        } else {
            do_c();
        }
        return 0;
    }
    """
    blocks = partition_function_body(src)
    assert isinstance(blocks[0], IfWithReturn)
    # Outer: then returns, else (the chain) does not.
    assert blocks[0].then_terminates is True
    assert blocks[0].else_terminates is False
    # The else_body chain itself doesn't return.
    inner = blocks[0].else_body[0]
    assert isinstance(inner, IfNoReturn)


# ---------------------------------------------------------------------------
# Documented limitations — these tests pin the CURRENT (sub-optimal)
# behavior so a future fix is reminded to update the assertions.


def test_do_while_known_limitation_misclassifies():
    """Pin for L1 in ``TODO/partition_known_limitations.md``.

    Current behavior: ``do { body }`` → leading Others; ``while (cond);``
    → WhileNoReturn with empty body; trailing → Others.  When ``do``
    keyword detection lands, update this test to assert a single
    composite While* block and remove L1 from the TODO.
    """
    src = "void f() { do { step(); } while (cond); after(); }"
    blocks = partition_function_body(src)
    types = [type(b).__name__ for b in blocks]
    assert types == ["Others", "WhileNoReturn", "Others"], types
    # The misclassified while has an empty body.
    while_block = blocks[1]
    assert while_block.body == []


def test_switch_treated_as_opaque_others():
    """Pin for L2 in ``TODO/partition_known_limitations.md``.

    Whole ``switch`` lands in one ``Others``.  Update when a ``Switch``
    block type is introduced; remove L2 from the TODO.
    """
    src = "void f() { switch (x) { case 1: a(); break; case 2: b(); break; } after(); }"
    blocks = partition_function_body(src)
    assert len(blocks) == 1
    assert isinstance(blocks[0], Others)
    assert "switch" in blocks[0].raw_c_text


# ---------------------------------------------------------------------------
# Phase 2a — block-tree-driven scaffold annotations.


from GenMonads.absprog.partition import (
    format_c_segment_comment,
    render_blocks_as_c_snippet,
    split_for_no_loop_early_return,
)


def test_split_for_no_loop_early_return_separates_decision_from_body():
    """No-loop-early-return shape: M_before should carry the leading
    IfWithReturn; M_normal should carry everything after."""
    blocks = partition_function_body(_NO_LOOP_EARLY_RETURN_SRC)
    split = split_for_no_loop_early_return(blocks)
    assert split is not None
    # M_before: just the IfWithReturn at the head.
    assert len(split["m_before"]) == 1
    assert isinstance(split["m_before"][0], IfWithReturn)
    # M_normal: the trailing Others with the call + final return.
    assert len(split["m_normal"]) == 1
    assert isinstance(split["m_normal"][0], Others)
    assert "helper(x)" in split["m_normal"][0].raw_c_text
    assert "return x;" in split["m_normal"][0].raw_c_text


def test_split_for_no_loop_early_return_with_leading_prep_blocks():
    """When prep statements precede the early-return decision, they
    belong with M_before — the agent still has to do them before the
    decision can be evaluated."""
    src = """
    int demo(int x) {
        int* p = setup();    // prep before the decision
        do_init();
        if (p == 0) return -1;
        return p->value;
    }
    """
    blocks = partition_function_body(src)
    split = split_for_no_loop_early_return(blocks)
    assert split is not None
    # M_before contains the prep Others AND the IfWithReturn.
    assert len(split["m_before"]) == 2
    assert isinstance(split["m_before"][0], Others)
    assert isinstance(split["m_before"][1], IfWithReturn)
    # M_normal carries the post-decision body.
    assert len(split["m_normal"]) == 1
    assert "return p->value" in split["m_normal"][0].raw_c_text


def test_split_returns_none_when_no_early_return():
    """A function with no IfWithReturn doesn't fit the simple
    no-loop-early-return scaffold; the helper returns None."""
    blocks = partition_function_body("int f() { return work(); }")
    assert split_for_no_loop_early_return(blocks) is None


def test_format_c_segment_comment_renders_indented_block():
    """The Coq comment wraps the C snippet with consistent indentation
    so the agent can read both sides at a glance."""
    out = format_c_segment_comment(
        "demo_M_before",
        "the early-return decision",
        "if (x == 0) {\n    return y;\n}",
    )
    assert out.startswith("(*")
    assert out.rstrip().endswith("*)")
    assert "demo_M_before models the early-return decision:" in out
    # Indented C lines preserved.
    assert "       if (x == 0) {" in out
    assert "       }" in out


def test_render_blocks_as_c_snippet_concatenates_with_blank_lines():
    """Multiple blocks become a single snippet joined by blank lines."""
    blocks = partition_function_body(_NO_LOOP_EARLY_RETURN_SRC)
    split = split_for_no_loop_early_return(blocks)
    snippet = render_blocks_as_c_snippet(split["m_normal"])
    # Single block → snippet contains its raw text.
    assert "helper(x)" in snippet
    assert "return x;" in snippet


def test_generated_rel_lib_is_clean_of_c_segment_annotations(tmp_path):
    """The lib ``.v`` is consumed by ``coqc`` and ``Require Import``; the
    C-source-to-hole binding is synthesis-time guidance, not lib content.
    Confirm the generator emits no per-Parameter binding comments."""
    from GenMonads.absprog.gen_rel_lib import generate_rel_lib_for_file

    src_path = _write_fixture(tmp_path, "demo", _NO_LOOP_EARLY_RETURN_SRC)
    out_dir = tmp_path / "lib_out"
    path = generate_rel_lib_for_file(
        src_path, str(out_dir),
        sibling_dirs=[str(tmp_path)],
        monad="staterr",
    )
    assert path is not None
    text = open(path).read()
    # The per-Parameter "X models Y" comment from Phase 2a's first
    # iteration must NOT appear in the lib (synthesis-only guidance
    # lives in the prompt, not the lib).
    assert "demo_M_before models" not in text
    assert "demo_M_normal models" not in text
    # Section header for the function's scaffold IS expected (it's the
    # only Coq comment the legacy generator emits).
    assert "(* ---- Abstract program segments for demo ---- *)" in text
    # And the Parameter declarations are still present.
    assert "Parameter demo_M_before" in text
    assert "Parameter demo_M_normal" in text


def test_context_carries_scaffold_segments_for_no_loop_early_return(tmp_path):
    """The block-tree-derived M_before / M_normal C segments live on
    ``context["prompt_context"]["scaffold_segments"]`` for downstream
    prompt rendering."""
    from GenMonads.absprog.context import collect_synthesis_context

    src_path = _write_fixture(tmp_path, "demo", _NO_LOOP_EARLY_RETURN_SRC)
    ctx = collect_synthesis_context(src_path)
    segs = ctx["prompt_context"]["scaffold_segments"]
    assert "M_before" in segs and "M_normal" in segs
    assert "if (x == 0)" in segs["M_before"]
    assert "return y;" in segs["M_before"]
    assert "helper(x)" in segs["M_normal"]
    assert "tail->next = y" in segs["M_normal"]
    assert "return x;" in segs["M_normal"]


def test_context_omits_scaffold_segments_for_shapes_that_dont_use_them(tmp_path):
    """Straight-line functions (Shape 1: opaque ``M``) don't have a
    decomposed scaffold to bind against — their ``scaffold_segments`` is
    empty.

    Single-loop functions DO get bindings (Phase 2b); see
    ``test_context_carries_loop_scaffold_segments`` for that pinning.
    Multi-loop (forest) functions still get empty segments — see
    ``test_context_omits_loop_segments_for_multi_loop_functions``.
    """
    from GenMonads.absprog.context import collect_synthesis_context

    # Shape 1: straight-line (no early return).
    src_path = _write_fixture(tmp_path, "demo", _STRAIGHT_LINE_SRC)
    ctx_app = collect_synthesis_context(src_path, func_name="demo")
    assert ctx_app["prompt_context"]["scaffold_segments"] == {}


def test_prompt_emits_binding_section_for_no_loop_early_return(tmp_path):
    """End-to-end: the rendered prompt for a no-loop-early-return
    function includes the ``## Abstract-Program ↔ C Segment Binding``
    section with both M_before and M_normal C snippets."""
    from GenMonads.absprog.context import collect_synthesis_context
    from GenMonads.absprog.templates import render_prompt

    src_path = _write_fixture(tmp_path, "demo", _NO_LOOP_EARLY_RETURN_SRC)
    ctx = collect_synthesis_context(src_path)
    prompt = render_prompt(ctx)
    assert "## Abstract-Program ↔ C Segment Binding" in prompt
    # M_before's snippet appears verbatim.
    assert "if (x == 0)" in prompt and "return y;" in prompt
    # M_normal's snippet — including the cross-file call the agent must
    # NOT put into M_before.
    binding_start = prompt.index("## Abstract-Program ↔ C Segment Binding")
    binding = prompt[binding_start:]
    assert "helper(x)" in binding
    assert "tail->next = y" in binding
    # The "do not mix work across hole boundaries" instruction is shown.
    assert "must NOT be placed into" in binding or "do not mix work" in binding


def test_prompt_omits_binding_section_for_straight_line_function(tmp_path):
    """Straight-line functions (one opaque ``M`` hole) don't have
    decomposed scaffold holes to bind against — no binding section."""
    from GenMonads.absprog.context import collect_synthesis_context
    from GenMonads.absprog.templates import render_prompt

    src_path = _write_fixture(tmp_path, "demo", _STRAIGHT_LINE_SRC)
    ctx = collect_synthesis_context(src_path, func_name="demo")
    prompt = render_prompt(ctx)
    assert "## Abstract-Program ↔ C Segment Binding" not in prompt


# ---------------------------------------------------------------------------
# Phase 2b — loop scaffold C↔hole binding.


from GenMonads.absprog.partition import split_for_loop_scaffold


def test_split_for_loop_scaffold_pre_loop_body_post():
    """Loop-with-pre-guard shape: pre-loop guard → M_loop_before, while
    body → M_loop_M2, post-loop return → M_loop_end."""
    blocks = partition_function_body(_LOOP_WITH_PRE_GUARD_SRC)
    split = split_for_loop_scaffold(blocks)
    assert split is not None
    # M_loop_before: the pre-loop early-return guard.
    assert len(split["M_loop_before"]) == 1
    assert isinstance(split["M_loop_before"][0], IfWithReturn)
    # M_loop_M2: the single Others inside the loop body.
    assert len(split["M_loop_M2"]) == 1
    assert isinstance(split["M_loop_M2"][0], Others)
    assert "x = x->next" in split["M_loop_M2"][0].raw_c_text
    # M_loop_end: the terminal `return x;`.
    assert len(split["M_loop_end"]) == 1
    assert isinstance(split["M_loop_end"][0], Others)
    assert "return x" in split["M_loop_end"][0].raw_c_text


def test_split_for_loop_scaffold_loop_only_function():
    """A function whose body IS just a loop produces empty pre/post
    segments — the renderer treats them as `return s` defaults."""
    blocks = partition_function_body(_LOOP_ONLY_SRC)
    split = split_for_loop_scaffold(blocks)
    assert split is not None
    assert split["M_loop_before"] == []
    assert split["M_loop_M2"]    # the free_node call is here
    assert split["M_loop_end"] == []


def test_split_for_loop_scaffold_returns_none_for_multi_loop():
    """When the function has more than one top-level loop block, the
    helper returns None — multi-loop scaffolds need per-loop bindings
    handled by `loop_forest` (out of scope for Phase 2b)."""
    src = """
    void f() {
        while (a) { step_a(); }
        while (b) { step_b(); }
    }
    """
    blocks = partition_function_body(src)
    assert split_for_loop_scaffold(blocks) is None


def test_split_for_loop_scaffold_returns_none_when_no_loop():
    """No-loop function → None.  Caller uses
    split_for_no_loop_early_return instead."""
    blocks = partition_function_body(_NO_LOOP_EARLY_RETURN_SRC)
    assert split_for_loop_scaffold(blocks) is None


def test_context_carries_loop_scaffold_segments(tmp_path):
    """The single-loop case populates the three loop-scaffold hole keys
    in the context's ``scaffold_segments``."""
    from GenMonads.absprog.context import collect_synthesis_context

    src_path = _write_fixture(tmp_path, "demo", _LOOP_WITH_PRE_GUARD_SRC)
    ctx = collect_synthesis_context(src_path)
    segs = ctx["prompt_context"]["scaffold_segments"]
    assert set(segs.keys()) == {"M_loop_before", "M_loop_M2", "M_loop_end"}
    assert "if (x == 0)" in segs["M_loop_before"]
    assert "x = x->next" in segs["M_loop_M2"]
    assert "return x" in segs["M_loop_end"]


def test_context_emits_forest_segments_for_multi_loop_functions(tmp_path):
    """Multi-loop (forest) functions get per-loop segments populated by
    Phase 3A — keyed by the existing forest scaffold's hole names
    (``M_loop{k}_before``, ``M_loop{k}_M2`` for leaves, etc.).
    Replaces the pre-Phase-3A behaviour where ``scaffold_segments`` was
    deliberately left empty."""
    from GenMonads.absprog.context import collect_synthesis_context

    src_path = _write_fixture(tmp_path, "demo", _MULTI_LOOP_SRC)
    ctx = collect_synthesis_context(src_path)
    segs = ctx["prompt_context"]["scaffold_segments"]
    assert segs   # populated, not empty
    # Per-loop keys for the nested-loop fixture (outer = loop1, inner = loop2).
    expected_keys = {
        "M_loop1_before", "M_loop1_to_inner_2",
        "M_loop2_M2",
        "M_loop1_after_inner_2", "M_loop1_end",
    }
    assert set(segs.keys()) == expected_keys


def test_prompt_renders_loop_scaffold_binding_section(tmp_path):
    """End-to-end: the rendered prompt for a single-loop function
    includes the C↔hole binding for all three loop scaffold holes."""
    from GenMonads.absprog.context import collect_synthesis_context
    from GenMonads.absprog.templates import render_prompt

    src_path = _write_fixture(tmp_path, "demo", _LOOP_WITH_PRE_GUARD_SRC)
    ctx = collect_synthesis_context(src_path)
    prompt = render_prompt(ctx)
    assert "## Abstract-Program ↔ C Segment Binding" in prompt
    binding = prompt.split("## Abstract-Program ↔ C Segment Binding", 1)[1]
    # All three loop holes show up with their C snippets.
    assert "demo_M_loop_before` models" in binding
    assert "demo_M_loop_M2` models one iteration" in binding
    assert "demo_M_loop_end` models" in binding
    # Specific C statements bound to the right hole.
    assert "if (x == 0)" in binding   # in M_loop_before
    assert "x = x->next" in binding   # in M_loop_M2
    assert "return x;" in binding     # in M_loop_end


def test_prompt_handles_empty_loop_segments_with_trivial_default(tmp_path):
    """When a loop hole has no corresponding C statements (loop-only
    function: neither pre-loop work nor a post-loop return), the prompt
    explicitly tells the agent to emit a trivial Definition rather than
    leaving the slot ambiguous."""
    from GenMonads.absprog.context import collect_synthesis_context
    from GenMonads.absprog.templates import render_prompt

    src_path = _write_fixture(tmp_path, "demo", _LOOP_ONLY_SRC)
    ctx = collect_synthesis_context(src_path)
    prompt = render_prompt(ctx)
    binding = prompt.split("## Abstract-Program ↔ C Segment Binding", 1)[1]
    # M_loop_before is empty for this function.
    assert "M_loop_before` models the pre-loop preparation" in binding
    assert "no statements for this segment" in binding
    assert "trivial `Definition`" in binding


def test_prompt_orders_no_loop_segments_before_loop_segments():
    """Stable ordering rule: no-loop holes come first in the preferred
    list, then loop holes — for the two scaffolds combined into one
    pass-through the binding reads top-down naturally."""
    # This is a renderer-only test on a synthetic scaffold_segments dict.
    from GenMonads.absprog.templates import _render_scaffold_segments_section

    prompt_ctx = {
        "scaffold_segments": {
            "M_loop_end": "return x;",
            "M_loop_before": "init();",
            "M_normal": "after;",   # synthetic: shouldn't usually mix shapes
            "M_loop_M2": "step();",
            "M_before": "early;",
        }
    }
    ctx = {"summary": {"func_name": "demo"}}
    lines = _render_scaffold_segments_section(prompt_ctx, ctx)
    rendered = "\n".join(lines)
    # M_before / M_normal precede M_loop_*.
    i_before = rendered.index("M_before` models")
    i_normal = rendered.index("M_normal` models")
    i_lbef   = rendered.index("M_loop_before` models")
    i_lm2    = rendered.index("M_loop_M2` models")
    i_lend   = rendered.index("M_loop_end` models")
    assert i_before < i_normal < i_lbef < i_lm2 < i_lend


# ---------------------------------------------------------------------------
# Phase 3A — multi-loop (forest) C↔hole binding.


from GenMonads.absprog.partition import split_for_loop_forest


_NESTED_TWO_LOOPS_SRC = (
    'long demo(struct list *x)\n'
    '/*@ Require listrep(x)\n'
    '    Ensure  emp\n'
    ' */\n'
    '{\n'
    '    struct list *stop;\n'
    '    long sum;\n'
    '    stop = 0;\n'
    '    sum = 0;\n'
    '    /*@ Inv exists st s,\n'
    '            store(&stop, struct list*, st) *\n'
    '            store(&sum, long, s) *\n'
    '            listrep(x)\n'
    '     */\n'
    '    while (x != stop) {\n'
    '        struct list *node;\n'
    '        node = x;\n'
    '        /*@ Inv exists st s,\n'
    '                store(&stop, struct list*, st) *\n'
    '                store(&sum, long, s) *\n'
    '                listrep(x)\n'
    '         */\n'
    '        while (node->next != stop) {\n'
    '            node = node->next;\n'
    '        }\n'
    '        sum += node->data;\n'
    '        stop = node;\n'
    '    }\n'
    '    return sum;\n'
    '}\n'
)


def test_split_for_loop_forest_emits_per_loop_segments():
    """A function with one outer + one nested inner loop produces:
    - M_loop1_before (top-level pre-loop work)
    - M_loop1_to_inner_2 (outer body before the inner)
    - M_loop2_M2 (inner leaf body)
    - M_loop1_after_inner_2 (outer body after the inner)
    - M_loop1_end (top-level post-loop work)"""
    blocks = partition_function_body(_NESTED_TWO_LOOPS_SRC)
    segs = split_for_loop_forest(blocks)
    assert segs is not None
    expected = {
        "M_loop1_before",
        "M_loop1_to_inner_2",
        "M_loop2_M2",
        "M_loop1_after_inner_2",
        "M_loop1_end",
    }
    assert set(segs.keys()) == expected
    assert "stop = 0" in segs["M_loop1_before"]
    assert "sum = 0" in segs["M_loop1_before"]
    assert "node = x" in segs["M_loop1_to_inner_2"]
    assert "node = node->next" in segs["M_loop2_M2"]
    assert "sum += node->data" in segs["M_loop1_after_inner_2"]
    assert "return sum" in segs["M_loop1_end"]


def test_split_for_loop_forest_inserts_keys_in_execution_order():
    """The dict's insertion order is the execution narrative — outer
    starts, enters inner, inner body, exits inner, outer ends.  The
    prompt renderer relies on this order to read top-to-bottom."""
    blocks = partition_function_body(_NESTED_TWO_LOOPS_SRC)
    segs = split_for_loop_forest(blocks)
    keys = list(segs.keys())
    assert keys == [
        "M_loop1_before",
        "M_loop1_to_inner_2",
        "M_loop2_M2",
        "M_loop1_after_inner_2",
        "M_loop1_end",
    ]


def test_split_for_loop_forest_returns_none_when_no_loops():
    blocks = partition_function_body(
        "int demo() { return work(); }"
    )
    assert split_for_loop_forest(blocks) is None


def test_split_for_loop_forest_single_loop_treated_as_leaf():
    """Single top-level loop with no nesting → M_loop1_before, M_loop1_M2,
    M_loop1_end.  No to_inner / after_inner segments."""
    src = (
        'void demo(struct list *x)\n'
        '/*@ Require listrep(x) Ensure emp */\n'
        '{\n'
        '    /*@ Inv listrep(x) */\n'
        '    while (x != 0) { x = x->next; }\n'
        '}\n'
    )
    blocks = partition_function_body(src)
    segs = split_for_loop_forest(blocks)
    assert segs is not None
    assert "M_loop1_M2" in segs
    assert "x = x->next" in segs["M_loop1_M2"]
    assert all("to_inner" not in k for k in segs)
    assert all("after_inner" not in k for k in segs)


def test_context_carries_forest_segments_for_multi_loop_function(tmp_path):
    """End-to-end: a function whose loop_templates count is >1 gets the
    per-loop forest segments populated on its prompt_context."""
    from GenMonads.absprog.context import collect_synthesis_context

    src_path = tmp_path / "demo.c"
    src_path.write_text(_NESTED_TWO_LOOPS_SRC, encoding="utf-8")
    ctx = collect_synthesis_context(str(src_path))
    segs = ctx["prompt_context"]["scaffold_segments"]
    assert "M_loop1_before" in segs
    assert "M_loop2_M2" in segs
    assert "M_loop1_after_inner_2" in segs
    assert "M_loop1_end" in segs


def test_prompt_renders_per_loop_forest_binding_section(tmp_path):
    """The rendered prompt for a multi-loop function shows all loops'
    segments in execution order with their dynamic role descriptions."""
    from GenMonads.absprog.context import collect_synthesis_context
    from GenMonads.absprog.templates import render_prompt

    src_path = tmp_path / "demo.c"
    src_path.write_text(_NESTED_TWO_LOOPS_SRC, encoding="utf-8")
    ctx = collect_synthesis_context(str(src_path))
    prompt = render_prompt(ctx)
    assert "## Abstract-Program ↔ C Segment Binding" in prompt
    binding = prompt.split("## Abstract-Program ↔ C Segment Binding", 1)[1]
    # All five per-loop entries appear.
    for name in (
        "demo_M_loop1_before",
        "demo_M_loop1_to_inner_2",
        "demo_M_loop2_M2",
        "demo_M_loop1_after_inner_2",
        "demo_M_loop1_end",
    ):
        assert name + "` models" in binding, f"missing entry: {name}"
    # And in execution order.
    pos = [
        binding.index("demo_M_loop1_before"),
        binding.index("demo_M_loop1_to_inner_2"),
        binding.index("demo_M_loop2_M2"),
        binding.index("demo_M_loop1_after_inner_2"),
        binding.index("demo_M_loop1_end"),
    ]
    assert pos == sorted(pos), f"out of order: {pos}"


def test_prompt_renders_forest_role_descriptions_dynamically():
    """Forest role text mentions the actual loop indices."""
    from GenMonads.absprog.templates import _forest_role_for
    role, instr = _forest_role_for("M_loop3_to_inner_4")
    assert "loop 3" in role and "inner loop 4" in role
    assert "loop 3" in instr and "loop 4" in instr

    role, instr = _forest_role_for("M_loop1_M2")
    assert "leaf loop 1" in role
    # Unknown key returns None.
    assert _forest_role_for("M_before") is None


# ---------------------------------------------------------------------------
# Phase 3B — loop body early-return sub-segment.


_LOOP_BODY_EARLY_RETURN_SRC = (
    'long demo(struct list *x)\n'
    '/*@ Require listrep(x)\n'
    '    Ensure  emp\n'
    ' */\n'
    '{\n'
    '    long sum;\n'
    '    sum = 0;\n'
    '    /*@ Inv exists s, store(&sum, long, s) * listrep(x) */\n'
    '    while (x != 0) {\n'
    '        if (x->data < 0) {\n'
    '            return -1;\n'
    '        }\n'
    '        sum += x->data;\n'
    '        x = x->next;\n'
    '    }\n'
    '    return sum;\n'
    '}\n'
)


def test_split_for_loop_scaffold_emits_m2_split_when_body_has_early_return():
    """When the loop body contains an inner IfWithReturn, the split
    helper returns an extra ``M_loop_M2_split`` entry showing the
    pre-decision / decision / post-decision breakdown."""
    blocks = partition_function_body(_LOOP_BODY_EARLY_RETURN_SRC)
    from GenMonads.absprog.partition import split_for_loop_scaffold
    split = split_for_loop_scaffold(blocks)
    assert split is not None
    assert "M_loop_M2_split" in split
    m2 = split["M_loop_M2_split"]
    # No pre-decision work in this fixture — the if is the first body block.
    assert m2["pre_decision"] == []
    # The decision is the inner IfWithReturn.
    assert isinstance(m2["decision"], IfWithReturn)
    assert m2["decision"].cond == "x->data < 0"
    # Post-decision contains the iteration step.
    assert len(m2["post_decision"]) == 1
    assert "sum += x->data" in m2["post_decision"][0].raw_c_text


def test_split_for_loop_scaffold_omits_m2_split_when_body_has_no_early_return():
    """A loop whose body has no early-return doesn't get the M2 split."""
    blocks = partition_function_body(_LOOP_WITH_PRE_GUARD_SRC)
    from GenMonads.absprog.partition import split_for_loop_scaffold
    split = split_for_loop_scaffold(blocks)
    assert split is not None
    assert "M_loop_M2_split" not in split


def test_split_for_loop_scaffold_with_prep_before_inner_if():
    """Pre-decision work shows up in the M_loop_M2_split entry when the
    if isn't the first body statement."""
    src = (
        'long demo(struct list *x)\n'
        '/*@ Require listrep(x) Ensure emp */\n'
        '{\n'
        '    long sum;\n'
        '    sum = 0;\n'
        '    /*@ Inv exists s, store(&sum, long, s) * listrep(x) */\n'
        '    while (x != 0) {\n'
        '        sum += 1;\n'
        '        if (x->data < 0) return -1;\n'
        '        x = x->next;\n'
        '    }\n'
        '    return sum;\n'
        '}\n'
    )
    blocks = partition_function_body(src)
    from GenMonads.absprog.partition import split_for_loop_scaffold
    split = split_for_loop_scaffold(blocks)
    assert split is not None
    assert "M_loop_M2_split" in split
    m2 = split["M_loop_M2_split"]
    assert len(m2["pre_decision"]) == 1
    assert "sum += 1" in m2["pre_decision"][0].raw_c_text


def test_context_carries_m2_split_metadata_for_loop_with_body_return(tmp_path):
    """End-to-end: the metadata keys flow through to prompt_context
    under the underscore-prefixed namespace."""
    from GenMonads.absprog.context import collect_synthesis_context

    src_path = tmp_path / "demo.c"
    src_path.write_text(_LOOP_BODY_EARLY_RETURN_SRC, encoding="utf-8")
    ctx = collect_synthesis_context(str(src_path))
    segs = ctx["prompt_context"]["scaffold_segments"]
    # Standard 3-key set still present.
    for key in ("M_loop_before", "M_loop_M2", "M_loop_end"):
        assert key in segs
    # Phase 3B metadata.
    assert "_M_loop_M2_decision" in segs
    assert "x->data < 0" in segs["_M_loop_M2_decision"]
    assert segs["_M_loop_M2_decision_cond"] == "x->data < 0"
    # Pre-decision empty here; post-decision carries iteration work.
    assert segs["_M_loop_M2_pre_decision"] == ""
    assert "sum += x->data" in segs["_M_loop_M2_post_decision"]


def test_prompt_renders_loop_body_substructure_when_early_return_in_body(tmp_path):
    """The prompt's M_loop_M2 entry is augmented with the
    pre-decision / decision / post-decision breakdown when the loop
    body has an inner early-return."""
    from GenMonads.absprog.context import collect_synthesis_context
    from GenMonads.absprog.templates import render_prompt

    src_path = tmp_path / "demo.c"
    src_path.write_text(_LOOP_BODY_EARLY_RETURN_SRC, encoding="utf-8")
    ctx = collect_synthesis_context(str(src_path))
    prompt = render_prompt(ctx)
    binding = prompt.split("## Abstract-Program ↔ C Segment Binding", 1)[1]
    assert "**Loop body structure**" in binding
    assert "Wrap `M_loop_M2`'s output with `early_result`" in binding
    assert "Early-return decision:" in binding
    assert "x->data < 0" in binding
    assert "Post-decision work" in binding
    # The substructure appears AFTER the main M_loop_M2 entry, not
    # before it (so the agent reads the hole's binding first, then the
    # substructure as supplementary guidance).
    main_pos = binding.index("demo_M_loop_M2` models")
    sub_pos = binding.index("**Loop body structure**")
    assert main_pos < sub_pos


def test_prompt_omits_loop_body_substructure_when_no_inner_early_return(tmp_path):
    """A loop with no internal early-return doesn't get the structure
    block in its prompt."""
    from GenMonads.absprog.context import collect_synthesis_context
    from GenMonads.absprog.templates import render_prompt

    src_path = tmp_path / "demo.c"
    src_path.write_text(_LOOP_WITH_PRE_GUARD_SRC, encoding="utf-8")
    ctx = collect_synthesis_context(str(src_path))
    prompt = render_prompt(ctx)
    binding = prompt.split("## Abstract-Program ↔ C Segment Binding", 1)[1]
    assert "**Loop body structure**" not in binding


def test_prompt_underscore_keys_dont_appear_as_their_own_bindings(tmp_path):
    """The underscore-prefixed metadata keys (e.g. ``_M_loop_M2_decision``)
    must NOT be rendered as standalone binding entries; they're only
    surfaced inline under M_loop_M2's section."""
    from GenMonads.absprog.context import collect_synthesis_context
    from GenMonads.absprog.templates import render_prompt

    src_path = tmp_path / "demo.c"
    src_path.write_text(_LOOP_BODY_EARLY_RETURN_SRC, encoding="utf-8")
    ctx = collect_synthesis_context(str(src_path))
    prompt = render_prompt(ctx)
    # No "{fn}__M_loop_M2_pre_decision` models" style entry.
    assert "_M_loop_M2_pre_decision` models" not in prompt
    assert "_M_loop_M2_decision` models" not in prompt
    assert "_M_loop_M2_decision_cond` models" not in prompt
    assert "_M_loop_M2_post_decision` models" not in prompt


# ---------------------------------------------------------------------------
# Phase 3C — interleaved early-returns: template + annotations.


from GenMonads.absprog.partition import split_for_interleaved_early_return


_INTERLEAVED_TWO_DECISIONS_SRC = (
    '#include "header.h"\n'
    '\n'
    'struct list *demo(struct list *x, struct list *y)\n'
    '/*@ Require listrep(x) * listrep(y)\n'
    '    Ensure  listrep(__return)\n'
    ' */\n'
    '{\n'
    '    if (x == 0) { return y; }\n'
    '    real_work1();\n'
    '    if (y == 0) { return x; }\n'
    '    real_work2();\n'
    '    return x;\n'
    '}\n'
)


_INTERLEAVED_THREE_DECISIONS_SRC = (
    '#include "header.h"\n'
    '\n'
    'struct list *demo(struct list *x, struct list *y, struct list *z)\n'
    '/*@ Require listrep(x) * listrep(y) * listrep(z)\n'
    '    Ensure  listrep(__return)\n'
    ' */\n'
    '{\n'
    '    if (x == 0) { return y; }\n'
    '    w1();\n'
    '    if (y == 0) { return z; }\n'
    '    w2();\n'
    '    if (z == 0) { return x; }\n'
    '    w3();\n'
    '    return x;\n'
    '}\n'
)


def test_split_for_interleaved_early_return_two_decisions():
    """Two early-return decisions separated by work: helper returns
    decisions + phases (N and N respectively, with the last phase
    being the terminal work)."""
    blocks = partition_function_body(_INTERLEAVED_TWO_DECISIONS_SRC)
    split = split_for_interleaved_early_return(blocks)
    assert split is not None
    assert len(split["decisions"]) == 2
    assert len(split["phases"]) == 2
    assert split["decisions"][0].cond == "x == 0"
    assert split["decisions"][1].cond == "y == 0"
    # phases[0] = work between decision 1 and decision 2 (real_work1).
    assert any("real_work1" in b.raw_c_text for b in split["phases"][0])
    # phases[1] = terminal (real_work2 + return).
    assert any("real_work2" in b.raw_c_text for b in split["phases"][1])
    assert any("return x" in b.raw_c_text for b in split["phases"][1])


def test_split_for_interleaved_early_return_three_decisions():
    """N=3 case: produces three decisions and three phases."""
    blocks = partition_function_body(_INTERLEAVED_THREE_DECISIONS_SRC)
    split = split_for_interleaved_early_return(blocks)
    assert split is not None
    assert len(split["decisions"]) == 3
    assert len(split["phases"]) == 3


def test_split_for_interleaved_early_return_single_decision_returns_none():
    """One decision is the existing no-loop-early-return scaffold — the
    interleaved helper should defer."""
    blocks = partition_function_body(_NO_LOOP_EARLY_RETURN_SRC)
    assert split_for_interleaved_early_return(blocks) is None


def test_split_for_interleaved_early_return_loop_present_returns_none():
    """Loop-bearing functions go through loop scaffolds, not the
    interleaved scaffold."""
    blocks = partition_function_body(_LOOP_WITH_PRE_GUARD_SRC)
    assert split_for_interleaved_early_return(blocks) is None


def test_split_for_interleaved_early_return_no_decisions_returns_none():
    """Straight-line functions don't have any decisions."""
    blocks = partition_function_body(_STRAIGHT_LINE_SRC)
    assert split_for_interleaved_early_return(blocks) is None


def test_context_emits_interleaved_segments_in_execution_order(tmp_path):
    """The synthesis context inserts segments in execution-narrative
    order: decision_1 → phase_1 → decision_2 → … → M_final."""
    from GenMonads.absprog.context import collect_synthesis_context

    src_path = tmp_path / "demo.c"
    src_path.write_text(_INTERLEAVED_TWO_DECISIONS_SRC, encoding="utf-8")
    ctx = collect_synthesis_context(str(src_path))
    keys = list(ctx["prompt_context"]["scaffold_segments"].keys())
    assert keys == ["M_decision_1", "M_phase_1", "M_decision_2", "M_final"]


def test_context_skips_interleaved_branch_for_single_decision(tmp_path):
    """A single-decision no-loop function still gets M_before/M_normal,
    not the interleaved scaffold."""
    from GenMonads.absprog.context import collect_synthesis_context

    src_path = tmp_path / "demo.c"
    src_path.write_text(_NO_LOOP_EARLY_RETURN_SRC, encoding="utf-8")
    ctx = collect_synthesis_context(str(src_path))
    segs = ctx["prompt_context"]["scaffold_segments"]
    assert "M_before" in segs and "M_normal" in segs
    assert all(not k.startswith("M_decision_") for k in segs)


def test_prompt_renders_interleaved_binding_section(tmp_path):
    """End-to-end: the prompt for an interleaved function shows each
    decision and phase with dynamic role text mentioning the indices."""
    from GenMonads.absprog.context import collect_synthesis_context
    from GenMonads.absprog.templates import render_prompt

    src_path = tmp_path / "demo.c"
    src_path.write_text(_INTERLEAVED_TWO_DECISIONS_SRC, encoding="utf-8")
    ctx = collect_synthesis_context(str(src_path))
    prompt = render_prompt(ctx)
    binding = prompt.split("## Abstract-Program ↔ C Segment Binding", 1)[1]
    # All four bindings appear with their dynamic role text.
    assert "demo_M_decision_1` models early-return decision number 1" in binding
    assert "demo_M_phase_1` models the work between decision 1 and decision 2" in binding
    assert "demo_M_decision_2` models early-return decision number 2" in binding
    assert "demo_M_final` models the terminal phase" in binding
    # The C snippets appear.
    assert "if (x == 0)" in binding
    assert "if (y == 0)" in binding
    assert "real_work1" in binding
    assert "real_work2" in binding


def test_generated_rel_lib_emits_interleaved_scaffold(tmp_path):
    """End-to-end: ``generate_rel_lib_for_file`` emits the new
    interleaved scaffold for a 2-decision function."""
    from GenMonads.absprog.gen_rel_lib import generate_rel_lib_for_file

    src_path = tmp_path / "demo.c"
    src_path.write_text(_INTERLEAVED_TWO_DECISIONS_SRC, encoding="utf-8")
    out_path = generate_rel_lib_for_file(
        str(src_path), str(tmp_path / "lib"), monad="staterr",
    )
    text = open(out_path).read()
    # The interleaved scaffold's structural artifacts.
    assert "interleaved early-returns: 2 decisions" in text
    assert "Parameter demo_state_1 : Type." in text
    assert "Parameter demo_state_2 : Type." in text
    assert "Parameter demo_state_3 : Type." in text
    assert "Parameter demo_M_decision_1" in text
    assert "Parameter demo_M_phase_1" in text
    assert "Parameter demo_M_decision_2" in text
    assert "Parameter demo_M_final" in text
    # The mechanical cascading composition.
    assert "Definition demo_M" in text
    assert "e_1 <- demo_M_decision_1" in text
    assert "match e_1 with" in text
    assert "e_2 <- demo_M_decision_2" in text
    assert "match e_2 with" in text
    assert "demo_M_final s_3" in text
    # Only ONE Definition-terminating period (the outer ``end.``).
    assert text.count("    end.\n") == 1
    # And one inner ``end`` without period.
    assert "        end\n" in text


def test_generated_rel_lib_does_not_use_interleaved_for_single_decision(tmp_path):
    """A single-decision function uses the legacy M_before / M_normal
    scaffold, not the interleaved one."""
    from GenMonads.absprog.gen_rel_lib import generate_rel_lib_for_file

    src_path = tmp_path / "demo.c"
    src_path.write_text(_NO_LOOP_EARLY_RETURN_SRC, encoding="utf-8")
    out_path = generate_rel_lib_for_file(
        str(src_path), str(tmp_path / "lib"), monad="staterr",
    )
    text = open(out_path).read()
    assert "interleaved early-returns" not in text
    assert "Parameter demo_M_before" in text
    assert "Parameter demo_M_normal" in text
    assert "Parameter demo_M_decision_1" not in text
