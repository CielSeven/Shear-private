"""Tests for the Phase-2 block-tree-driven Coq renderer.

Phase 2.0 scope: callee-only straight-line functions (Shape 1) get a
concrete ``Definition {fn}_M := …`` instead of the legacy opaque
``Parameter`` — eliminating the LLM hole for those functions.

These tests pin both:

* the per-statement translation logic in ``block_renderer.py`` (unit-level,
  ``try_render_concrete_definition`` directly), and
* the end-to-end emission via ``generate_rel_lib_for_file`` with the
  ``use_block_renderer=True`` feature flag, on synthetic C sources.

All fixtures are inline — no dependency on any dataset path.
"""

import os

import pytest

from GenMonads.absprog.block_renderer import (
    _parse_statement,
    _split_statements,
    try_render_concrete_definition,
)
from GenMonads.absprog.gen_rel_lib import generate_rel_lib_for_file
from GenMonads.absprog.partition import (
    IfWithReturn,
    Others,
    WhileNoReturn,
    partition_function_body,
)


# ---------------------------------------------------------------------------
# Unit tests — try_render_concrete_definition


def _others(text: str) -> Others:
    """Build a one-element block list containing the given C statements."""
    return Others(raw_c_text=text)


def test_render_passthrough_returns_call_directly():
    """A bare ``return callee(args);`` becomes ``callee_M args.``"""
    body = try_render_concrete_definition(
        fn_name="passthrough",
        blocks=[_others("return helper(x, y);")],
        require_var_names=["x", "y"],
        available_callees={"helper": "<sig>"},
    )
    assert body is not None
    assert "fun x y =>" in body
    assert "helper_M x y" in body
    # No trailing `return` — the call IS the result.
    assert "    helper_M x y." in body


def test_render_call_chain_emits_monadic_binds():
    """A sequence of ``x = f(...);`` followed by ``return x;`` produces a
    bind chain ending in ``return x``."""
    body = try_render_concrete_definition(
        fn_name="chain",
        blocks=[_others(
            "x = f(x, y);"
            " x = g(x, z);"
            " return x;"
        )],
        require_var_names=["x", "y", "z"],
        available_callees={"f": "<sig>", "g": "<sig>"},
    )
    assert body is not None
    assert "fun x y z =>" in body
    assert "x <- f_M x y;;" in body
    assert "x <- g_M x z;;" in body
    assert "return x." in body


def test_render_terminal_return_call_uses_value():
    """An ``x = f(...); return f2(x);`` chain ends with the trailing
    call (no ``return`` keyword wrap)."""
    body = try_render_concrete_definition(
        fn_name="end_with_call",
        blocks=[_others(
            "x = f(x);"
            " return g(x);"
        )],
        require_var_names=["x"],
        available_callees={"f": "<sig>", "g": "<sig>"},
    )
    assert body is not None
    assert "x <- f_M x;;" in body
    assert "    g_M x." in body


def test_render_rejects_unknown_callee():
    """A callee not in ``available_callees`` falls back to ``None``
    (caller emits ``Parameter`` instead)."""
    body = try_render_concrete_definition(
        fn_name="demo",
        blocks=[_others("return mystery(x);")],
        require_var_names=["x"],
        available_callees={},   # nothing available
    )
    assert body is None


def test_render_rejects_unknown_variable_reference():
    """An argument that isn't a parameter or prior lhs is rejected."""
    body = try_render_concrete_definition(
        fn_name="demo",
        blocks=[_others("return f(out);")],   # `out` never bound
        require_var_names=["x"],
        available_callees={"f": "<sig>"},
    )
    assert body is None


def test_render_rejects_no_terminal_return():
    """The body must end in a return statement."""
    body = try_render_concrete_definition(
        fn_name="demo",
        blocks=[_others("x = f(x);")],         # no return
        require_var_names=["x"],
        available_callees={"f": "<sig>"},
    )
    assert body is None


def test_render_rejects_initialization_to_zero():
    """``out = 0;`` isn't a call; Phase 2.0 doesn't (yet) handle pure
    initializations and returns ``None`` so the caller falls back to a
    Parameter."""
    body = try_render_concrete_definition(
        fn_name="demo",
        blocks=[_others(
            "out = 0;"
            " out = f(x, out);"
            " return out;"
        )],
        require_var_names=["x"],
        available_callees={"f": "<sig>"},
    )
    assert body is None


def test_render_rejects_multi_block_function():
    """Shape 2 / 3 (early returns or loops) is out of scope for Phase 2.0;
    multi-block trees return ``None``."""
    body = try_render_concrete_definition(
        fn_name="demo",
        blocks=[
            IfWithReturn(raw_c_text="if (x == 0) return y;", cond="x == 0"),
            _others("return f(x);"),
        ],
        require_var_names=["x", "y"],
        available_callees={"f": "<sig>"},
    )
    assert body is None


def test_render_rejects_loop_function():
    body = try_render_concrete_definition(
        fn_name="demo",
        blocks=[
            WhileNoReturn(raw_c_text="while (x) { x = f(x); }", cond="x"),
            _others("return x;"),
        ],
        require_var_names=["x"],
        available_callees={"f": "<sig>"},
    )
    assert body is None


def test_render_rejects_complex_argument_expression():
    """``f(x->next, y)`` has a member-access argument — Phase 2.0
    accepts only bare identifiers."""
    body = try_render_concrete_definition(
        fn_name="demo",
        blocks=[_others("return f(x->next, y);")],
        require_var_names=["x", "y"],
        available_callees={"f": "<sig>"},
    )
    assert body is None


def test_render_zero_param_function_emits_no_fun_binder():
    """For a function with zero parameters, the body is a monadic value
    of type ``MONAD T`` — not ``unit -> MONAD T``.  Emitting
    ``fun tt => …`` would make the Definition's type disagree with its
    declared signature; Coq would reject it.  The renderer must omit the
    ``fun`` binder entirely when ``require_var_names`` is empty.
    """
    body = try_render_concrete_definition(
        fn_name="demo",
        blocks=[_others("return f();")],
        require_var_names=[],
        available_callees={"f": "<sig>"},
    )
    assert body is not None
    assert "fun " not in body, (
        "zero-param Definition must not introduce a fun binder"
    )
    # The body is just the call, no trailing-space whitespace bug.
    assert body.strip() == "f_M."


def test_render_zero_arg_call_has_no_trailing_space():
    """``return f();`` inside a body with params: the call renders as
    ``f_M.`` not ``f_M .`` — whitespace correctness."""
    body = try_render_concrete_definition(
        fn_name="demo",
        blocks=[_others("y = f(); return f(y);")],
        require_var_names=["x"],
        available_callees={"f": "<sig>"},
    )
    assert body is not None
    # Bind step: ``y <- f_M;;`` (no space before ;;).
    assert "y <- f_M;;" in body
    assert "y <- f_M ;;" not in body
    # Terminal call: ``f_M y.`` (single space, no extra trailing space).
    assert "f_M y." in body


# ---------------------------------------------------------------------------
# Statement parser internals


def test_split_statements_handles_semicolons_in_function_call():
    """``f(a, b);`` is one statement even with commas inside parens."""
    stmts = _split_statements("x = f(a, b); return x;")
    assert stmts == ["x = f(a, b);", "return x;"]


def test_parse_statement_recognises_three_shapes():
    assert _parse_statement("x = f(a, b);") is not None
    assert _parse_statement("return f(a);") is not None
    assert _parse_statement("return x;") is not None
    # Unsupported shapes return None.
    assert _parse_statement("x->next = y;") is None
    assert _parse_statement("if (x) return y;") is None
    assert _parse_statement("x = 0;") is None


# ---------------------------------------------------------------------------
# End-to-end emission via generate_rel_lib_for_file


_PASSTHROUGH_C = (
    '#include "header.h"\n'
    '\n'
    'struct list *helper(struct list *x, struct list *y);\n'
    '\n'
    'struct list *passthrough(struct list *x, struct list *y)\n'
    '/*@ Require listrep(x) * listrep(y)\n'
    '    Ensure  listrep(__return)\n'
    ' */\n'
    '{\n'
    '    return helper(x, y);\n'
    '}\n'
)

_HELPER_C = (
    '#include "header.h"\n'
    'struct list *helper(struct list *x, struct list *y)\n'
    '/*@ Require listrep(x) * listrep(y) Ensure listrep(__return) */\n'
    '{ return x; }\n'
)


def _setup_passthrough(tmp_path):
    """Write a self-contained two-file project: a passthrough caller
    plus its trivial helper.  Returns ``(c_file, sibling_dirs)``."""
    src_dir = tmp_path / "src"
    src_dir.mkdir()
    (src_dir / "passthrough.c").write_text(_PASSTHROUGH_C)
    (src_dir / "helper.c").write_text(_HELPER_C)
    return str(src_dir / "passthrough.c"), [str(src_dir)]


def test_end_to_end_legacy_emits_parameter(tmp_path):
    """With the flag off, behaviour is unchanged — ``Parameter`` is
    emitted as today's legacy renderer does."""
    c_file, sib = _setup_passthrough(tmp_path)
    out_dir = tmp_path / "legacy_lib"
    out_path = generate_rel_lib_for_file(
        c_file, str(out_dir), sibling_dirs=sib, monad="staterr",
        use_block_renderer=False,
    )
    text = open(out_path).read()
    block = text.split("declaration for passthrough", 1)[1]
    assert "Parameter passthrough_M" in block
    assert "Definition passthrough_M" not in block


def test_end_to_end_phase2_emits_concrete_definition(tmp_path):
    """With ``use_block_renderer=True`` and an eligible function, a
    fully concrete ``Definition`` replaces the ``Parameter`` — no LLM
    hole remains for this function."""
    c_file, sib = _setup_passthrough(tmp_path)
    out_dir = tmp_path / "phase2_lib"
    out_path = generate_rel_lib_for_file(
        c_file, str(out_dir), sibling_dirs=sib, monad="staterr",
        use_block_renderer=True,
    )
    text = open(out_path).read()
    block = text.split("declaration for passthrough", 1)[1]
    assert "Parameter passthrough_M" not in block
    assert "Definition passthrough_M" in block
    assert "fun x y =>" in block
    assert "helper_M x y" in block


def test_end_to_end_phase2_falls_back_for_ineligible_function(tmp_path):
    """A function with an initialization (``sum = 0;``) doesn't fit
    Phase-2.0 rules — the Parameter form survives, so the agent can
    still fill it in."""
    src = (
        '#include "header.h"\n'
        '\n'
        'struct list *helper(struct list *x);\n'
        '\n'
        'long demo(struct list *x)\n'
        '/*@ Require listrep(x)\n'
        '    Ensure  emp\n'
        ' */\n'
        '{\n'
        '    long sum;\n'
        '    sum = 0;\n'              # initialization — Phase 2.0 skips
        '    return sum;\n'
        '}\n'
    )
    helper = (
        '#include "header.h"\n'
        'struct list *helper(struct list *x)\n'
        '/*@ Require listrep(x) Ensure listrep(__return) */\n'
        '{ return x; }\n'
    )
    src_dir = tmp_path / "src"
    src_dir.mkdir()
    (src_dir / "demo.c").write_text(src)
    (src_dir / "helper.c").write_text(helper)
    out_path = generate_rel_lib_for_file(
        str(src_dir / "demo.c"), str(tmp_path / "lib"),
        sibling_dirs=[str(src_dir)], monad="staterr",
        use_block_renderer=True,
    )
    text = open(out_path).read()
    # Falls back to Parameter for the ineligible Shape 1 variant.
    assert "Parameter demo_M" in text


def test_end_to_end_phase2_does_not_disturb_loop_functions(tmp_path):
    """A loop-bearing function still goes through the legacy loop
    scaffold — Phase 2.0 only touches the Shape-1 path."""
    src = (
        '#include "header.h"\n'
        '\n'
        'struct list *demo(struct list *x)\n'
        '/*@ Require x != 0 && listrep(x)\n'
        '    Ensure  listrep(__return)\n'
        '*/\n'
        '{\n'
        '    /*@ Inv x != 0 && listrep(x) */\n'
        '    while (x->next != 0) {\n'
        '        x = x->next;\n'
        '    }\n'
        '    return x;\n'
        '}\n'
    )
    src_dir = tmp_path / "src"
    src_dir.mkdir()
    (src_dir / "demo.c").write_text(src)
    out_path = generate_rel_lib_for_file(
        str(src_dir / "demo.c"), str(tmp_path / "lib"),
        sibling_dirs=[str(src_dir)], monad="staterr",
        use_block_renderer=True,
    )
    text = open(out_path).read()
    # Loop scaffold's holes are still Parameters — the block renderer
    # didn't touch them.
    assert "Parameter demo_M_loop_M1" in text
    assert "Parameter demo_M_loop_M2" in text
