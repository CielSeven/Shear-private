"""Tests for the LLM-synthesized loop-guard path: when GuardGen cannot
produce a concrete guard, the LLM must supply ``{fn}_guardP`` with a fixed
signature."""

import pytest

from GenMonads.absprog.context import _build_control_flow_template
from GenMonads.absprog.parse_coq import (
    _component_parameter_name,
    parse_synthesized_components,
)
from GenMonads.absprog.assemble import assemble_rel_lib_from_blocks
from GenMonads.absprog.templates import render_prompt
from GenMonads.absprog.synthesize import _validate_guard_signature


def _loop_context(required, guard_signature="(list Z * Z) -> Prop"):
    return {
        "summary": {"func_name": "demo"},
        "control_flow": {
            "required_components": required,
            "guard_signature": guard_signature,
        },
    }


# --- control-flow template -------------------------------------------------


def test_control_flow_adds_guardp_when_guard_unavailable():
    cf = _build_control_flow_template(
        "demo", ["list Z"], ["list Z", "Z"], "list Z",
        has_pre_loop_early_return=False,
        has_loop_body_early_return=False,
        guard_available=False,
        loop_condition="x != stop",
    )
    assert "guardP" in cf["required_components"]
    assert cf["guard_available"] is False
    assert cf["prompt_signatures"]["guardP"] == "(list Z * Z) -> Prop"
    assert cf["guard_signature"] == "(list Z * Z) -> Prop"
    assert cf["loop_condition"] == "x != stop"


def test_control_flow_omits_guardp_when_guard_available():
    cf = _build_control_flow_template(
        "demo", ["list Z"], ["list Z", "Z"], "list Z",
        has_pre_loop_early_return=False,
        has_loop_body_early_return=False,
        guard_available=True,
    )
    assert "guardP" not in cf["required_components"]
    assert cf["guard_available"] is True
    assert "guardP" not in cf["prompt_signatures"]


# --- parser ----------------------------------------------------------------


def test_parse_coq_resolves_guardp_component():
    assert _component_parameter_name("guardP", "demo") == "demo_guardP"
    response = (
        "Definition MretTy : Type := (list Z * Z).\n"
        "Definition demo_M_loop_before : list Z -> MONAD (list Z * Z) := fun l => return (l, 0).\n"
        "Definition demo_M_loop_M1 : (list Z * Z) -> MONAD MretTy := fun a => return a.\n"
        "Definition demo_M_loop_M2 : (list Z * Z) -> MONAD (list Z * Z) := fun a => a.\n"
        "Definition demo_M_loop_end : MretTy -> MONAD ((list Z * Z)) := fun r => return r.\n"
        "Definition demo_guardP : (list Z * Z) -> Prop := fun a => let '(l, s) := a in l <> nil.\n"
    )
    blocks = parse_synthesized_components(
        response, "demo",
        required=["MretTy", "M_loop_before", "M_1", "M_2", "M_loop_end", "guardP"],
    )
    assert "guardP" in blocks
    assert "demo_guardP" in blocks["guardP"]
    assert blocks["guardP"].strip().endswith("l <> nil.")


# --- assembler -------------------------------------------------------------


_C_SRC = (
    'struct list { int data; struct list *next; };\n'
    '\n'
    'long iter_sum(struct list *x)\n'
    '/*@ Require listrep(x)\n'
    '    Ensure  listrep(x@pre)\n'
    ' */\n'
    '{\n'
    '    long s = 0;\n'
    '    struct list *p = x;\n'
    '    /*@ Inv exists l s2, store(&s, long, s2) * listrep(p) */\n'
    '    while (p != x) {\n'
    '        s = s + p->data;\n'
    '        p = p->next;\n'
    '    }\n'
    '    return s;\n'
    '}\n'
)


def test_assembler_replaces_parameter_guardp_with_definition(tmp_path):
    c_file = tmp_path / "iter_sum.c"
    c_file.write_text(_C_SRC, encoding="utf-8")

    # Build blocks for every required component; the exact bodies don't matter
    # for this structural check, only that guardP replaces the Parameter.
    blocks = {
        "MretTy": "Definition MretTy : Type := (list Z * Z).",
        "M_loop_before": "Definition iter_sum_M_loop_before : list Z -> MONAD (list Z * Z) := fun l => return (l, 0).",
        "M_1": "Definition iter_sum_M_loop_M1 : (list Z * Z) -> MONAD MretTy := fun a => return a.",
        "M_2": "Definition iter_sum_M_loop_M2 : (list Z * Z) -> MONAD (list Z * Z) := fun a => a.",
        "M_loop_end": "Definition iter_sum_M_loop_end : MretTy -> MONAD ((list Z * Z)) := fun r => return r.",
        "guardP": "Definition iter_sum_guardP : (list Z * Z) -> Prop := fun a => let '(l, s) := a in l <> nil.",
    }
    content = assemble_rel_lib_from_blocks(str(c_file), "iter_sum", blocks)
    assert "Parameter iter_sum_guardP" not in content
    assert "Definition iter_sum_guardP : (list Z * Z) -> Prop :=" in content


# --- prompt ----------------------------------------------------------------


def test_prompt_instructs_guardp_synthesis_with_fixed_signature():
    context = {
        "summary": {"func_name": "demo"},
        "predicate_family": "sll",
        "features": {
            "loop_count": 1, "require_var_count": 1, "inv_var_count": 2,
            "ensure_var_count": 1, "has_seg_predicate": False, "has_multi_return": False,
        },
        "prompt_context": {
            "c_source": "long demo(struct list *x) { return 0; }",
            "with_clause": "X l1",
            "require_with_safeexec": "REQ",
            "ensure_with_safeexec": "ENS",
            "loop_invariant_with_safeexec": "INV",
            "loop_condition": "x != stop",
            "guard_coq": "",
        },
        "signatures": {},
        "control_flow": {
            "template_case": "none",
            "required_components": ["MretTy", "M_loop_before", "M_1", "M_2", "M_loop_end", "guardP"],
            "guard_signature": "(list Z * Z) -> Prop",
            "loop_condition": "x != stop",
            "prompt_signatures": {
                "M_loop_before": "list Z -> MONAD (list Z * Z)",
                "guardP": "(list Z * Z) -> Prop",
            },
        },
        "generation_policy": {"must_define": ["demo_guardP"]},
    }
    prompt = render_prompt(context)
    assert "GuardGen could not synthesize the loop guard" in prompt
    assert "Definition demo_guardP : (list Z * Z) -> Prop :=" in prompt
    assert "do NOT change it" in prompt
    assert "guardP: (list Z * Z) -> Prop" in prompt
    assert "- `demo_guardP`" in prompt


# --- validator -------------------------------------------------------------


def test_validate_guard_signature_passes_with_correct_signature():
    ctx = _loop_context(["MretTy", "M_1", "guardP"])
    response = "Definition demo_guardP : (list Z * Z) -> Prop := fun a => True."
    _validate_guard_signature(ctx, response)  # should not raise


def test_validate_guard_signature_tolerates_outer_parens():
    ctx = _loop_context(["guardP"], guard_signature="(list Z * Z) -> Prop")
    response = "Definition demo_guardP : ((list Z * Z) -> Prop) := fun a => True."
    _validate_guard_signature(ctx, response)  # normalized equal


def test_validate_guard_signature_rejects_changed_signature():
    ctx = _loop_context(["guardP"])
    response = "Definition demo_guardP : list Z -> Prop := fun a => True."
    with pytest.raises(ValueError, match="signature must not change"):
        _validate_guard_signature(ctx, response)


def test_validate_guard_signature_rejects_missing_definition():
    ctx = _loop_context(["guardP"])
    response = "Definition demo_M_loop_M1 : (list Z * Z) -> MONAD MretTy := fun a => return a."
    with pytest.raises(ValueError, match="Missing required `Definition demo_guardP"):
        _validate_guard_signature(ctx, response)


def test_validate_guard_signature_noop_when_guard_available():
    ctx = _loop_context(["MretTy", "M_1"])  # guardP not required
    # No guardP definition, but validator must not complain.
    _validate_guard_signature(ctx, "Definition demo_M_loop_M1 : T := x.")


# ---------------------------------------------------------------------------
# Forest (multi-loop) prompt + validation (task #22)
# ---------------------------------------------------------------------------


def _forest_context(func_name="demo"):
    """Build a minimal multi-loop context with one parent and one leaf — the
    same shape as glibc_slist_iter_back_2, without any C source dependency."""
    loop_templates = [
        {
            "func_name": func_name, "loop_index": 0, "parent": None,
            "children": [1], "inv_index": 0,
            "inv_variables": ["l", "s"], "inv_var_types": ["list Z", "Z"],
            "state_type": "(list Z * Z)",
            "loop_condition": "x != stop", "coq_guard": "",
            "guard_available": False, "loop_invariant_translated": "",
            "data_witnesses": [], "keyword": "while",
        },
        {
            "func_name": func_name, "loop_index": 1, "parent": 0,
            "children": [], "inv_index": 1,
            "inv_variables": ["l2", "s"], "inv_var_types": ["list Z", "Z"],
            "state_type": "(list Z * Z)",
            "loop_condition": "node->next != stop", "coq_guard": "",
            "guard_available": False, "loop_invariant_translated": "",
            "data_witnesses": [], "keyword": "while",
        },
    ]
    required = [
        "MretTy",
        "loop1_guardP", "M_loop1_M1", "M_loop1_to_inner_2", "M_loop1_after_inner_2",
        "loop2_guardP", "M_loop2_M1", "M_loop2_M2",
        "M_loop1_before", "M_loop1_end",
    ]
    prompt_sigs = {
        "MretTy": "Type",
        "loop1_guardP": "(list Z * Z) -> Prop",
        "loop2_guardP": "(list Z * Z) -> Prop",
        "M_loop1_M1": "(list Z * Z) -> MONAD MretTy",
        "M_loop1_to_inner_2": "(list Z * Z) -> MONAD (list Z * Z)",
        "M_loop1_after_inner_2": "(list Z * Z) -> MretTy -> MONAD (list Z * Z)",
        "M_loop2_M1": "(list Z * Z) -> MONAD MretTy",
        "M_loop2_M2": "(list Z * Z) -> MONAD (list Z * Z)",
        "M_loop1_before": "list Z -> MONAD (list Z * Z)",
        "M_loop1_end": "MretTy -> MONAD ((list Z * Z))",
    }
    must_define = ["MretTy"] + [f"{func_name}_{c}" for c in required if c != "MretTy"]
    return {
        "summary": {"func_name": func_name},
        "predicate_family": "sll",
        "features": {
            "loop_count": 2, "require_var_count": 1, "inv_var_count": 2,
            "ensure_var_count": 1,
            "has_seg_predicate": False, "has_multi_return": False,
        },
        "prompt_context": {
            "c_source": "long demo(struct list *x) { return 0; }",
            "with_clause": "X l1",
            "require_with_safeexec": "REQ",
            "ensure_with_safeexec": "ENS",
            "loop_invariant_with_safeexec": "INV",
            "loop_condition": "x != stop",
            "guard_coq": "",
        },
        "signatures": {},
        "control_flow": {
            "template_case": "forest",
            "required_components": required,
            "prompt_signatures": prompt_sigs,
            "loop_templates": loop_templates,
            "loop_forest": [
                {"loop_index": t["loop_index"], "parent": t["parent"],
                 "children": t["children"], "keyword": "while",
                 "inv_index": t["inv_index"]}
                for t in loop_templates
            ],
        },
        "generation_policy": {"must_define": must_define},
    }


def test_render_prompt_emits_forest_section():
    """In workdir-mode the Loop Forest section still surfaces the dynamic
    per-loop topology + holes.  Static framework prose ("this function has
    multiple loops", "do NOT redefine it" etc.) is now in AGENTS.md."""
    ctx = _forest_context()
    prompt = render_prompt(ctx)
    # Loop Forest section with per-loop entries.
    assert "## Loop Forest" in prompt
    assert "- loop1 (parent, top-level; children: loop2)" in prompt
    assert "- loop2 (leaf, child of loop1; children: none)" in prompt
    # Required Holes lists every component with its signature.
    assert "## Required Holes (per loop)" in prompt
    assert "Definition demo_M_loop1_M1 : (list Z * Z) -> MONAD MretTy" in prompt
    assert "Definition demo_M_loop1_to_inner_2 : (list Z * Z) -> MONAD (list Z * Z)" in prompt
    assert "Definition demo_M_loop1_after_inner_2 : (list Z * Z) -> MretTy -> MONAD (list Z * Z)" in prompt
    assert "Definition demo_loop1_guardP : (list Z * Z) -> Prop" in prompt
    assert "Definition demo_loop2_guardP : (list Z * Z) -> Prop" in prompt
    assert "Definition demo_M_loop2_M2 : (list Z * Z) -> MONAD (list Z * Z)" in prompt
    # Single-loop static instruction text is no longer here.
    assert "the 4 non-guard components" not in prompt
    # Forest static prose dropped (moved to AGENTS.md).
    assert "mechanically wired the nesting" not in prompt
    assert "This function has multiple loops" not in prompt


def test_render_prompt_signatures_match_required_order():
    ctx = _forest_context()
    prompt = render_prompt(ctx)
    # The Required Signatures section enumerates the required components in
    # the same order they were registered.
    req_order = ctx["control_flow"]["required_components"]
    sigs_block = prompt.split("## Required Signatures", 1)[1].split("##", 1)[0]
    positions = []
    for name in req_order:
        idx = sigs_block.find(f"{name}:")
        assert idx >= 0, f"missing signature line for {name}"
        positions.append(idx)
    assert positions == sorted(positions), \
        f"signature order drift: {req_order} vs positions {positions}"


def test_validate_guard_signature_accepts_correct_forest_guards():
    ctx = _forest_context()
    response = (
        "Definition demo_loop1_guardP : (list Z * Z) -> Prop := fun a => True.\n"
        "Definition demo_loop2_guardP : (list Z * Z) -> Prop := fun a => True.\n"
    )
    _validate_guard_signature(ctx, response)  # must not raise


def test_validate_guard_signature_rejects_missing_forest_guard():
    ctx = _forest_context()
    response = "Definition demo_loop1_guardP : (list Z * Z) -> Prop := fun a => True.\n"
    with pytest.raises(ValueError, match=r"demo_loop2_guardP"):
        _validate_guard_signature(ctx, response)


def test_validate_guard_signature_rejects_changed_forest_guard():
    ctx = _forest_context()
    response = (
        "Definition demo_loop1_guardP : (list Z * Z) -> Prop := fun a => True.\n"
        "Definition demo_loop2_guardP : list Z -> Prop := fun a => True.\n"
    )
    with pytest.raises(ValueError, match="must not change"):
        _validate_guard_signature(ctx, response)
