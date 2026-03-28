from typing import Dict, Iterable, List, Optional


def _default_scaffold(func_name: str) -> str:
    return "\n".join([
        "```coq",
        f"Definition {func_name}_M : ReqArgs -> MONAD Ret :=",
        "  fun ... =>",
        f"    s0 <- {func_name}_M_loop_before ...;;",
        f"    r <- {func_name}_M_loop ...;;",
        f"    {func_name}_M_loop_end r.",
        "```",
    ])


def _render_scaffold(context: Dict) -> str:
    target = context.get("target", {})
    summary = context.get("summary", target.get("summary", {}))
    control_flow = context.get("control_flow", target.get("control_flow", {}))
    template = control_flow.get("template", {})
    loop_body = template.get("loop_body_definition")
    top_level = template.get("top_level")
    if loop_body or top_level:
        blocks = ["```coq"]
        if loop_body:
            blocks.append(loop_body)
        after_loop = template.get("after_loop_definition")
        if after_loop:
            blocks.extend(["", after_loop])
        if top_level:
            blocks.extend(["", top_level])
        blocks.append("```")
        return "\n".join(blocks)
    return _default_scaffold(summary["func_name"])


def _render_signature_lines(context: Dict) -> List[str]:
    target = context.get("target", {})
    summary = context.get("summary", target.get("summary", {}))
    signatures = context.get("signatures", target.get("signatures", {}))
    control_flow = context.get("control_flow", target.get("control_flow", {}))
    prompt_signatures = control_flow.get("prompt_signatures", {})

    if prompt_signatures:
        order = [
            "M_loop_before",
            "M_loop_body",
            "M_loop",
            "M_loop_M1",
            "M_loop_M2",
            "M_after_loop",
            "M_loop_end",
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

    lines: List[str] = [
        "You are generating Coq monadic abstract programs for formal verification.",
        "",
        "For now, only consider C functions with exactly one loop.",
        "",
        "## Function Summary",
        f"Function: {summary['func_name']}",
        f"Predicate family: {context.get('predicate_family')}",
        f"Loop count: {features['loop_count']}",
        f"Require vars: {features['require_var_count']}",
        f"Invariant vars: {features['inv_var_count']}",
        f"Ensure vars: {features['ensure_var_count']}",
        f"Has segment predicate: {features['has_seg_predicate']}",
        f"Has multi return: {features['has_multi_return']}",
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
        "## Guard Function",
        prompt_context["guard_coq"],
        "",
        "## Selected Scaffold",
        f"Template case: {control_flow.get('template_case', 'none')}",
        f"Pre-loop early return: {control_flow.get('has_pre_loop_early_return', False)}",
        f"Loop-body early return: {control_flow.get('has_loop_body_early_return', False)}",
        _render_scaffold(context),
        "",
        "## Required Signatures",
        *(_render_signature_lines(context)),
        "",
        "## QCP Monad Primitives",
        "- `return v` / `ret v`: return value v (monadic return)",
        "- `bind m f` / `m >>= f`: sequence m then f",
        "- `program unit T`: monadic program returning T (StateRelMonad)",
        "- `assume!! P`: lift a pure Coq proposition `P : Prop` into the monadic assumption form. Use this for branch conditions and pure facts such as `x <= y`, `l2 = nil`, or guard checks.",
        "- `assume P`: use this only when `P` is already in the library's expected state-predicate form. For these synthesis tasks, prefer `assume!!` over bare `assume`.",
        "- `any A`: return an arbitrary value of type A",
        "- `choice m1 m2`: nondeterministic branching",
        "- `repeat_break`: loop construct with break and continue branch",
        "- List operations: `app` (`++`), `cons` (`::`), `nil`, `length`, etc.",
        "",
    ]

    if available_callees:
        lines.extend([
            "## Available Callees",
            "Treat the following same-file callees as opaque abstract programs.",
        ])
        for callee in available_callees:
            lines.append(f"- `{callee['opaque_program']}`: {callee.get('externals', {}).get('M', '')}")
            spec = callee.get("spec", {})
            if spec.get("require"):
                lines.append(f"  Base Require: `{spec['require']}`")
            if spec.get("ensure"):
                lines.append(f"  Base Ensure: `{spec['ensure']}`")
            for site in callee.get("call_sites", []):
                lines.append(f"  Call site: `{site}`")
        lines.append("")

    if opaque_call_obligations:
        lines.extend([
            "## Opaque Call Obligations",
            "Every listed helper call is mandatory.",
            "You must model it using the listed opaque abstract program.",
            "Do not replace helper-call results with `any`.",
        ])
        for obligation in opaque_call_obligations:
            lines.append(
                f"- `{obligation['call_site']}` must use `{obligation['callee']}`"
            )
        lines.append("")

    lines.extend([
        "## Instructions",
        "Use the Selected Scaffold above as the authoritative composition rule for this target.",
        "Generate `MretTy` and the 4 non-guard components so the composed abstract program simulates the C source.",
    ])
    if generation_policy.get("generated_scaffolding"):
        lines.append(
            "The following definitions are already generated by the scaffold. Do not redefine them: "
            + ", ".join(generation_policy["generated_scaffolding"])
        )
    if generation_policy.get("opaque_external_programs"):
        lines.append(
            "Use opaque callee placeholders when modeling same-file calls: "
            + ", ".join(generation_policy["opaque_external_programs"])
        )
    lines.extend([
        "Return Coq definitions only for:",
        "- `MretTy`",
        f"- `{summary['func_name']}_M_loop_before`",
        f"- `{summary['func_name']}_M_loop_M1`",
        f"- `{summary['func_name']}_M_loop_M2`",
        f"- `{summary['func_name']}_M_loop_end`",
    ])

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
