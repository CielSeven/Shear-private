from typing import Dict, Iterable, List, Optional


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
    summary = context["summary"]
    features = context["features"]
    prompt_context = context["prompt_context"]
    signatures = context["signatures"]

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
        prompt_context["c_source"],
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
        "## Required Signatures",
        f"M_loop_before: {signatures['M_loop_before']}",
        f"M_1: {signatures['M_1']}",
        f"M_2: {signatures['M_2']}",
        f"M_loop_end: {signatures['M_loop_end']}",
        f"M: {signatures['M']}",
        "",
        "## QCP Monad Primitives",
        "- `return v` / `ret v`: return value v (monadic return)",
        "- `bind m f` / `m >>= f`: sequence m then f",
        "- `program unit T`: monadic program returning T (StateRelMonad)",
        "- `assume P`: enforce the condition P of type Prop and return unit",
        "- `any A`: return an arbitrary value of type A",
        "- `choice m1 m2`: nondeterministic branching",
        "- `repeat_break`: loop construct with break and continue branch",
        "- List operations: `app` (`++`), `cons` (`::`), `nil`, `length`, etc.",
        "",
        "## Abstract Program Decomposition",
        "The loop model uses `repeat_break` with two branches:",
        "- `M_2` (continue): when guard is true, one iteration step `S -> M(S)`",
        "- `M_1` (break): when guard is false, produce final result `S -> M(R)`",
        "",
        "The full program composes:",
        "  M_loop_before -> M_loop (repeat_break with M_1, M_2, guard) -> M_loop_end",
        "",
        "```coq",
        "f_M(l1, ..., lm) :=",
        "  s0 <- M_loop_before(l1, ..., lm);;",
        "  r <- M_loop(s0);;",
        "  M_loop_end(r)",
        "```",
        "",
        "## Instructions",
        "Generate `MretTy` and the 4 non-guard components so the composed abstract program simulates the C source.",
        "Return Coq definitions only for:",
        "- `MretTy`",
        f"- `{summary['func_name']}_M_loop_before`",
        f"- `{summary['func_name']}_M_loop_M1`",
        f"- `{summary['func_name']}_M_loop_M2`",
        f"- `{summary['func_name']}_M_loop_end`",
    ]

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
