import re
from typing import Dict, Iterable, List, Optional, Tuple


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


# Hole-name → (role-description, follow-up-instruction) lookup for the
# binding section.  Keep narrow: only LLM-synthesized holes that have a
# direct C-source counterpart deserve an entry.  ``M_loop_M1`` is the
# loop's break-branch hole and has no C-source counterpart (it's a
# mechanical "extract MretTy from the loop state at exit"), so we don't
# list it here.
_SEGMENT_ROLES = {
    "M_before": (
        "the early-return decision",
        "When the condition holds, return `(ReturnNow <abstract-value>)`. "
        "Otherwise return `(Continue <state>)` carrying the values "
        "`{fn}_M_normal` needs to finish the function.",
    ),
    "M_normal": (
        "the post-decision body (everything after the early-return)",
        "Receives the state from `M_before`'s `Continue` and produces "
        "the function's final return value via the monadic computation.",
    ),
    "M_loop_before": (
        "the pre-loop preparation (including any guard that exits before "
        "the loop runs)",
        "Initialize the abstract loop state from the function arguments.  "
        "If the C source has a pre-loop early-return guard, decide between "
        "`(ReturnNow <return-value>)` and `(Continue <initial-state>)`.",
    ),
    "M_loop_M2": (
        "one iteration of the loop body",
        "Take the current loop state, perform the iteration's work, and "
        "produce the next state.  Cross-file callee calls inside the loop "
        "body belong here, NOT in `M_loop_before` or `M_loop_end`.",
    ),
    "M_loop_end": (
        "the post-loop transformation (typically the function's final return)",
        "Receives the loop's break value (`MretTy`) and produces the "
        "function's return value.",
    ),
}


_FOREST_BEFORE_RE = re.compile(r"^M_loop(\d+)_before$")
_FOREST_END_RE = re.compile(r"^M_loop(\d+)_end$")
_FOREST_M2_RE = re.compile(r"^M_loop(\d+)_M2$")
_FOREST_TO_INNER_RE = re.compile(r"^M_loop(\d+)_to_inner_(\d+)$")
_FOREST_AFTER_INNER_RE = re.compile(r"^M_loop(\d+)_after_inner_(\d+)$")

_INTERLEAVED_DECISION_RE = re.compile(r"^M_decision_(\d+)$")
_INTERLEAVED_PHASE_RE = re.compile(r"^M_phase_(\d+)$")


def _forest_role_for(key: str) -> Optional[Tuple[str, str]]:
    """Return ``(role, instruction)`` for a multi-loop forest hole name.

    Returns ``None`` when *key* isn't a forest hole.  Static (single-loop
    and no-loop) keys go through ``_SEGMENT_ROLES``; forest keys arrive
    with embedded loop indices and need dynamic role text.
    """
    if (m := _FOREST_BEFORE_RE.match(key)) is not None:
        k = m.group(1)
        return (
            f"pre-loop preparation for loop {k} at the function level",
            "Initialize the abstract loop state from the function "
            "arguments.  If a pre-loop early-return guard exists, "
            f"decide between `(ReturnNow …)` and `(Continue …)` for loop {k}.",
        )
    if (m := _FOREST_END_RE.match(key)) is not None:
        k = m.group(1)
        return (
            f"post-loop transformation for the top-level loop {k} "
            "(typically the function's final return)",
            f"Receives loop {k}'s break value and produces the "
            "function's return value.",
        )
    if (m := _FOREST_M2_RE.match(key)) is not None:
        k = m.group(1)
        return (
            f"one iteration of leaf loop {k}'s body",
            f"Take loop {k}'s current state, perform the iteration's "
            "work, and produce the next state.",
        )
    if (m := _FOREST_TO_INNER_RE.match(key)) is not None:
        k, j = m.group(1), m.group(2)
        return (
            f"parent loop {k}'s body work BEFORE entering inner loop {j}",
            f"From loop {k}'s state, prepare the inputs for loop {j}.  "
            f"The composed loop {k} body invokes loop {j}'s `_aux` after this.",
        )
    if (m := _FOREST_AFTER_INNER_RE.match(key)) is not None:
        k, j = m.group(1), m.group(2)
        return (
            f"parent loop {k}'s body work AFTER inner loop {j} returns",
            f"Receive loop {j}'s output and prepare the next iteration "
            f"of loop {k}.",
        )
    # Phase 3C — interleaved early-return scaffold.
    if (m := _INTERLEAVED_DECISION_RE.match(key)) is not None:
        k = m.group(1)
        return (
            f"early-return decision number {k}",
            "When the condition holds, produce "
            "`(ReturnNow <abstract-return-value>)`.  Otherwise produce "
            f"`(Continue <state_{int(k) * 2 - 1}>)` carrying the values "
            f"needed by the next phase.",
        )
    if (m := _INTERLEAVED_PHASE_RE.match(key)) is not None:
        k = m.group(1)
        return (
            f"the work between decision {k} and decision {int(k) + 1} "
            "(runs only on the Continue path)",
            f"Receive `state_{int(k) * 2 - 1}` from decision {k}'s Continue "
            f"and produce `state_{int(k) * 2}` as input to decision "
            f"{int(k) + 1}.",
        )
    if key == "M_final":
        return (
            "the terminal phase: work after the last decision (produces "
            "the function's return value)",
            "Receive the last decision's Continue state and produce the "
            "function's return value via the monadic computation.",
        )
    return None


def _render_scaffold_segments_section(
    prompt_context: Dict, context: Dict,
) -> List[str]:
    """Render the ``## Abstract-Program ↔ C Segment Binding`` section when
    the function's scaffold has a non-empty C-segment binding.

    Each scaffold shape contributes its own set of hole names:

    * no-loop early-return → ``M_before`` / ``M_normal``
    * single-loop          → ``M_loop_before`` / ``M_loop_M2`` / ``M_loop_end``

    Each emitted entry tells the agent which exact C statements that
    Parameter is supposed to model, plus a short instruction on how to
    shape its output (when to use `ReturnNow` vs `Continue`, which side
    a cross-file call belongs on, etc.).  This is synthesis-time prompt
    material; the lib ``.v`` stays a clean Coq template.
    """
    segments = prompt_context.get("scaffold_segments") or {}
    if not segments:
        return []
    summary = context.get("summary", context.get("target", {}).get("summary", {}))
    fn = summary.get("func_name", "")

    # Underscore-prefixed keys are structural metadata (Phase 3B
    # sub-segments), not hole names.  Skip them in the main loop — they
    # get rendered inline under their parent hole.
    ordered_keys = _order_scaffold_segment_keys(
        [k for k in segments.keys() if not k.startswith("_")]
    )

    lines: List[str] = ["## Abstract-Program ↔ C Segment Binding"]
    lines.append(
        "Each LLM hole below corresponds to a specific span of the C "
        "source.  Translate only those C statements into the matching "
        "`Definition`; do not mix work across hole boundaries.  In "
        "particular, a cross-file callee call appearing in one segment "
        "MUST NOT be placed in another."
    )

    for key in ordered_keys:
        role_lookup = _SEGMENT_ROLES.get(key) or _forest_role_for(key)
        if role_lookup is None:
            # Unknown key — skip rather than crash (forward compat).
            continue
        role, instruction = role_lookup
        snippet = segments.get(key, "").strip()
        lines.append("")
        if snippet:
            lines.append(f"`{fn}_{key}` models {role}:")
            lines.append("```c")
            lines.append(snippet)
            lines.append("```")
        else:
            # Empty segment = "nothing to do here" — say so explicitly so
            # the agent doesn't search for missing C code.
            lines.append(
                f"`{fn}_{key}` models {role}.  The C source has no "
                f"statements for this segment — emit a trivial `Definition` "
                f"(typically `return s` or `fun s => return s`)."
            )
        if instruction:
            lines.append(instruction.format(fn=fn))
        # Phase 3B — when this is M_loop_M2 AND the loop body has an
        # inner early-return, append the substructure so the agent knows
        # how to encode ``early_result`` wrapping.
        if key == "M_loop_M2" and "_M_loop_M2_decision" in segments:
            lines.extend(_render_loop_body_early_return_substructure(fn, segments))
    return lines


def _render_loop_body_early_return_substructure(
    fn: str, segments: Dict[str, str],
) -> List[str]:
    """Append the pre-decision / decision / post-decision split to the
    M_loop_M2 entry when the loop body contains an early-return.

    The agent reads this and knows the M_loop_M2 body must be wrapped
    with ``early_result`` — when the condition holds, return
    ``ReturnNow``; otherwise, the rest of the body becomes the
    ``Continue`` path.
    """
    pre = (segments.get("_M_loop_M2_pre_decision") or "").strip()
    decision = (segments.get("_M_loop_M2_decision") or "").strip()
    decision_cond = (segments.get("_M_loop_M2_decision_cond") or "").strip()
    post = (segments.get("_M_loop_M2_post_decision") or "").strip()

    out: List[str] = ["", "**Loop body structure**: the body contains an "
        "internal early-return.  Wrap `M_loop_M2`'s output with "
        "`early_result`:"]
    if pre:
        out.append("")
        out.append("Pre-decision work (runs every iteration before the decision):")
        out.append("```c")
        out.append(pre)
        out.append("```")
    out.append("")
    out.append("Early-return decision:")
    out.append("```c")
    out.append(decision)
    out.append("```")
    if decision_cond:
        out.append(
            f"When the abstract counterpart of `{decision_cond}` holds, produce "
            "`(ReturnNow <abstract-return-value>)`.  Otherwise proceed to the "
            "post-decision work."
        )
    if post:
        out.append("")
        out.append("Post-decision work (runs only when the early-return doesn't fire):")
        out.append("```c")
        out.append(post)
        out.append("```")
        out.append(
            "After the post-decision work, produce `(Continue <next-state>)` "
            "so the loop continues."
        )
    return out


# Static ordering for the single-loop / no-loop keys.  Forest keys keep
# the order the partitioner inserted them in (execution narrative).
_STATIC_ORDER = [
    "M_before", "M_normal",
    "M_loop_before", "M_loop_M2", "M_loop_end",
]


def _order_scaffold_segment_keys(keys: List[str]) -> List[str]:
    """Stable order: static keys first (per ``_STATIC_ORDER``), then any
    other keys in their original (partitioner-inserted) order.  For
    forest functions the partitioner emits keys in execution-narrative
    order — preserving that order makes the prompt read top-to-bottom."""
    static_in = [k for k in _STATIC_ORDER if k in keys]
    others = [k for k in keys if k not in _STATIC_ORDER]
    return static_in + others


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
        *_render_scaffold_segments_section(prompt_context, context),
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
