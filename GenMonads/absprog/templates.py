from typing import Dict, Iterable, List, Optional


# Workdir-mode synthesis (since the codex-workdir backend landed in
# task #33) stopped embedding per-call scaffold sketches in the prompt —
# the agent reads ``skeleton/<basename>_rel_lib.v`` directly inside the
# workdir, so an in-prompt sketch was just redundant copy.  The old
# ``_default_scaffold`` / ``_render_scaffold`` / ``_render_forest_scaffold_sketch``
# helpers were deleted with that change (task #34).


def _render_guard_section(context: Dict) -> List[str]:
    """Render the ``## Guard Function`` section.

    When GuardGen produced a concrete guard, show it (current behaviour).
    When it could not (``guardP`` is in ``required_components``), the skeleton
    leaves ``Parameter {fn}_guardP`` for the LLM to fill in — emit explicit
    instructions plus the fixed signature that must not change.
    """
    target = context.get("target", {})
    summary = context.get("summary", target.get("summary", {}))
    func_name = summary.get("func_name", "")
    prompt_context = context.get("prompt_context", target.get("prompt_context", {}))
    control_flow = context.get("control_flow", target.get("control_flow", {}))
    required = control_flow.get("required_components", [])

    if "guardP" not in required:
        return ["## Guard Function", prompt_context.get("guard_coq", "")]

    guard_sig = control_flow.get("guard_signature", "")
    loop_condition = (
        control_flow.get("loop_condition")
        or prompt_context.get("loop_condition", "")
    )
    return [
        "## Guard Function",
        "GuardGen could not synthesize the loop guard automatically, so you must "
        "provide it.",
        f"Define `{func_name}_guardP` capturing the loop-continuation condition "
        f"(the C `while (...)` test: `{loop_condition}`) as a pure proposition "
        "over the abstract loop state.",
        f"REQUIRED signature (do NOT change it): "
        f"`Definition {func_name}_guardP : {guard_sig} :=`",
        "The guard holds when the loop body should run again (continue branch); "
        "its negation drives the break branch.  Destructure the state tuple with "
        "`fun a => let '(...) := a in ...` exactly as the other components do.",
    ]


def _render_forest_section(context: Dict) -> List[str]:
    """Render the ``## Loop Forest`` section when the function has multiple
    loops.  Lists each loop with its nesting, state type, condition, and the
    typed holes the LLM must define (with their Coq signatures)."""
    target = context.get("target", {})
    summary = context.get("summary", target.get("summary", {}))
    func_name = summary.get("func_name", "")
    control_flow = context.get("control_flow", target.get("control_flow", {}))
    loop_templates = control_flow.get("loop_templates", []) or []
    prompt_sigs = control_flow.get("prompt_signatures", {}) or {}
    if len(loop_templates) <= 1:
        return []

    lines: List[str] = ["## Loop Forest"]
    top_levels = [t for t in loop_templates if t["parent"] is None]
    lines.append(
        f"This function has {len(loop_templates)} loops "
        f"({len(top_levels)} top-level)."
    )
    lines.append(
        "Codegen has emitted one ``M_loop{k}_*`` block per loop and "
        "mechanically composed the parent→child wiring; you fill the typed "
        "holes below."
    )
    lines.append("")
    for t in loop_templates:
        k = t["loop_index"] + 1
        parent = t["parent"]
        children = t["children"]
        kind = "leaf" if not children else "parent"
        parent_str = "top-level" if parent is None else f"child of loop{parent+1}"
        children_str = (
            ", ".join(f"loop{c+1}" for c in children) if children else "none"
        )
        guard_state = "GuardGen-supplied" if t.get("guard_available") else "LLM-supplied"
        lines.append(
            f"- loop{k} ({kind}, {parent_str}; children: {children_str})"
        )
        lines.append(f"    state type    : {t.get('state_type')}")
        lines.append(f"    while-condition: `{t.get('loop_condition')}`")
        lines.append(f"    guardP        : {guard_state}")
        if t.get("has_early_return"):
            lines.append(
                "    early return  : YES (loop body contains `return`)"
            )
        safeexec_inv = t.get("loop_invariant_with_safeexec")
        if safeexec_inv:
            lines.append(f"    invariant     : `{safeexec_inv}`")
    lines.append("")

    must_define = (context.get("generation_policy", {}) or {}).get("must_define", [])
    fn_prefix = f"{func_name}_"
    held_components = [n[len(fn_prefix):] if n.startswith(fn_prefix) else n
                       for n in must_define]
    lines.append("## Required Holes (per loop)")
    lines.append("Each entry below is a Coq ``Definition`` you must provide. "
                 "The skeleton has the matching ``Parameter`` line ready for "
                 "replacement; do NOT change the signature.")
    for comp in held_components:
        sig = prompt_sigs.get(comp, "")
        full = comp if comp == "MretTy" else f"{fn_prefix}{comp}"
        if sig == "Type":
            lines.append(f"- `Definition {full} : Type := ...`")
        elif sig:
            lines.append(f"- `Definition {full} : {sig} := ...`")
        else:
            lines.append(f"- `Definition {full} := ...`")
    lines.append("")
    lines.append(
        "Mechanically generated (do NOT redefine): each parent loop's "
        "``M_loop{k}_M2`` (composed from your ``to_inner_{c}`` and "
        "``after_inner_{c}``), every ``M_loop{k}_body`` / ``M_loop{k}_aux``, "
        "and the top-level ``M``."
    )
    return lines


def _render_signature_lines(context: Dict) -> List[str]:
    target = context.get("target", {})
    summary = context.get("summary", target.get("summary", {}))
    signatures = context.get("signatures", target.get("signatures", {}))
    control_flow = context.get("control_flow", target.get("control_flow", {}))
    prompt_signatures = control_flow.get("prompt_signatures", {})

    # Forest case: the required_components list IS the ordering — enumerate
    # signatures in that order so the prompt mirrors the must_define list.
    if control_flow.get("template_case") == "forest":
        required = control_flow.get("required_components", []) or []
        return [
            f"{name}: {prompt_signatures[name]}"
            for name in required
            if name in prompt_signatures
        ]

    if prompt_signatures:
        order = [
            "guardP",
            "M_loop_before",
            "M_loop_body",
            "M_loop",
            "M_loop_M1",
            "M_loop_M2",
            "M_after_loop",
            "M_loop_end",
            "M_before",
            "M_normal",
            "M",
        ]
        lines = []
        for key in order:
            value = prompt_signatures.get(key)
            if value:
                lines.append(f"{key}: {value}")
        return lines

    return [
        f"M_loop_before: {signatures['M_loop_before']}",
        f"M_1: {signatures['M_1']}",
        f"M_2: {signatures['M_2']}",
        f"M_loop_end: {signatures['M_loop_end']}",
        f"M: {signatures['M']}",
    ]


def _format_example(example: Dict) -> str:
    func_name = example["summary"]["func_name"]
    features = example["features"]
    prompt_context = example["prompt_context"]
    signatures = example["signatures"]
    gold = example.get("gold", {})
    components = gold.get("components", {})

    lines = [
        f"### Example: {func_name}",
        f"- Predicate family: {example.get('predicate_family')}",
        f"- Loop count: {features.get('loop_count')}",
        f"- Invariant vars: {features.get('inv_var_count')}",
        "",
        "Input context:",
        f"- Require with safeExec: {prompt_context.get('require_with_safeexec', '')}",
        f"- Ensure with safeExec: {prompt_context.get('ensure_with_safeexec', '')}",
        f"- Loop invariant with safeExec: {prompt_context.get('loop_invariant_with_safeexec', '')}",
        f"- Loop condition: {prompt_context.get('loop_condition', '')}",
        f"- Guard Coq: {prompt_context.get('guard_coq', '')}",
        f"- M_loop_before signature: {signatures.get('M_loop_before', '')}",
        f"- M_1 signature: {signatures.get('M_1', '')}",
        f"- M_2 signature: {signatures.get('M_2', '')}",
        f"- M_loop_end signature: {signatures.get('M_loop_end', '')}",
        "",
        "Output:",
        "```coq",
    ]

    if gold.get("MretTy"):
        lines.append(f"Definition MretTy : Type := {gold['MretTy']}.")
    for key in ("M_loop_before", "M_1", "M_2", "M_loop_end"):
        if components.get(key):
            lines.append(components[key])
    lines.append("```")
    return "\n".join(lines)


def render_prompt(context: Dict, few_shot_examples: Optional[Iterable[Dict]] = None) -> str:
    few_shot_examples = list(few_shot_examples or [])
    target = context.get("target", {})
    summary = context.get("summary", target.get("summary", {}))
    features = context.get("features", target.get("features", {}))
    prompt_context = context.get("prompt_context", target.get("prompt_context", {}))
    signatures = context.get("signatures", target.get("signatures", {}))
    control_flow = context.get("control_flow", target.get("control_flow", {}))
    available_callees = context.get("available_callees", [])
    opaque_call_obligations = context.get("opaque_call_obligations", [])
    generation_policy = context.get("generation_policy", {})

    template_case = control_flow.get("template_case", "none")
    no_loop = template_case in ("no_loop_early_return", "no_loop_simple")
    is_forest = template_case == "forest"

    # Static framework knowledge (identity, monad primitives, style rules,
    # forest mechanics, naming conventions, opaque-call obligations) lives
    # in workdir AGENTS.md.  This prompt is the dynamic per-attempt brief —
    # function summary, C source, holes to fill, repair feedback.

    lines: List[str] = [
        f"## Function Summary",
        f"Function: {summary['func_name']}",
        f"Predicate family: {context.get('predicate_family')}",
        f"Loop count: {features['loop_count']}",
        f"Require vars: {features['require_var_count']}",
        f"Invariant vars: {features['inv_var_count']}",
        f"Ensure vars: {features['ensure_var_count']}",
        f"Has segment predicate: {features['has_seg_predicate']}",
        f"Has multi return: {features['has_multi_return']}",
        f"Template case: {template_case}",
        "",
        "## C Source",
        target.get("c_source", prompt_context["c_source"]),
        "",
        "## Prompt Context",
        f"With clause: {prompt_context['with_clause']}",
        f"Require with safeExec: {prompt_context['require_with_safeexec']}",
        f"Ensure with safeExec: {prompt_context['ensure_with_safeexec']}",
        f"Loop invariant with safeExec: {prompt_context['loop_invariant_with_safeexec']}",
        f"Loop condition: {prompt_context['loop_condition']}",
        "",
        *_render_guard_section(context),
        "",
        "## Selected Scaffold",
        f"Template case: {control_flow.get('template_case', 'none')}",
        f"Pre-loop early return: {control_flow.get('has_pre_loop_early_return', False)}",
        f"Loop-body early return: {control_flow.get('has_loop_body_early_return', False)}",
        "The concrete skeleton (with the Parameter lines you must fill) is "
        "at `skeleton/<basename>_rel_lib.v` inside the workdir — read it "
        "before editing.",
        "",
        *_render_forest_section(context),
        "## Required Signatures",
        *(_render_signature_lines(context)),
        "",
    ]

    if available_callees:
        lines.extend([
            "## Available Callees",
            "Treat the following callees as opaque abstract programs.",
            "Cross-file callees are imported via `Require Import {callee}_rel_lib.` at the top of the generated rel-lib; do not redeclare their `Parameter`.",
        ])
        for callee in available_callees:
            origin = "cross-file" if callee.get("cross_file") else "same-file"
            lines.append(
                f"- `{callee['opaque_program']}` ({origin}): "
                f"{callee.get('externals', {}).get('M', '')}"
            )
            if callee.get("cross_file") and callee.get("defined_in"):
                lines.append(f"  Defined in: `{callee['defined_in']}`")
            spec = callee.get("spec", {})
            if spec.get("require"):
                lines.append(f"  Base Require: `{spec['require']}`")
            if spec.get("ensure"):
                lines.append(f"  Base Ensure: `{spec['ensure']}`")
            for site in callee.get("call_sites", []):
                lines.append(f"  Call site: `{site}`")
            if callee.get("c_source"):
                lines.append("  C body:")
                lines.append("  ```c")
                for body_line in callee["c_source"].splitlines():
                    lines.append(f"  {body_line}")
                lines.append("  ```")
        lines.append("")

    if opaque_call_obligations:
        # The rule ("bind result to a named variable, never `_`, never hand-
        # compute a replacement") lives in AGENTS.md A10.  Here we just list
        # the specific call sites that trigger the obligation.
        lines.append("## Opaque Call Obligations")
        for obligation in opaque_call_obligations:
            lines.append(
                f"- `{obligation['call_site']}` must use `{obligation['callee']}`"
            )
        lines.append("")

    must_define = generation_policy.get("must_define", [])

    # "## Definitions to Provide" — what the LLM must replace in the skeleton.
    # The HOW (signatures, monad style, naming, mechanical-M2 contract) is in
    # AGENTS.md; here we list only the names.
    lines.append("## Definitions to Provide")
    if generation_policy.get("opaque_external_programs"):
        lines.append(
            "Same-file opaque programs you may invoke: "
            + ", ".join(generation_policy["opaque_external_programs"])
        )
    if generation_policy.get("generated_scaffolding"):
        lines.append(
            "Already generated by the scaffold — do NOT redefine: "
            + ", ".join(generation_policy["generated_scaffolding"])
        )
    lines.append("Replace these Parameter declarations with Definitions in `skeleton/<basename>_rel_lib.v`:")
    if must_define:
        for name in must_define:
            lines.append(f"- `{name}`")
    else:
        # Legacy single-loop fallback when generation_policy isn't populated.
        for suffix in ("MretTy", "M_loop_before", "M_loop_M1", "M_loop_M2", "M_loop_end"):
            full = suffix if suffix == "MretTy" else f"{summary['func_name']}_{suffix}"
            lines.append(f"- `{full}`")

    if few_shot_examples:
        lines.extend(["", "## Examples"])
        for example in few_shot_examples:
            lines.extend(["", _format_example(example)])

    return "\n".join(lines) + "\n"


def render_repair_prompt(
    context: Dict,
    previous_response: str,
    failure_kind: str,
    failure_message: str,
    few_shot_examples: Optional[Iterable[Dict]] = None,
) -> str:
    base_prompt = render_prompt(context, few_shot_examples)
    repair_lines = [
        "",
        "## Repair Feedback",
        "Your previous answer could not be accepted.",
        f"Failure kind: {failure_kind}",
        "Failure details:",
        "```text",
        failure_message.strip(),
        "```",
        "",
        "Previous response:",
        "```coq",
        previous_response.strip(),
        "```",
        "",
        "Revise the answer and return a complete replacement.",
        "Return Coq definitions only for the required names.",
    ]
    return base_prompt + "\n".join(repair_lines) + "\n"


def prompt_payload(context: Dict, prompt: str, example_paths: Optional[List[str]] = None) -> Dict:
    return {
        "context_id": context["id"],
        "func_name": context["summary"]["func_name"],
        "source_c_file": context["source"]["c_file"],
        "example_paths": list(example_paths or []),
        "prompt": prompt,
    }
