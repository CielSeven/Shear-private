import json
import os
import re
import shutil
import subprocess
from typing import Dict, List, Optional, Tuple

from GenMonads.absprog.assemble import write_assembled_rel_lib
from GenMonads.absprog.check_rocq import check_rocq_file
from GenMonads.absprog.context import collect_synthesis_context, write_synthesis_context
from GenMonads.absprog.gen_func_residual import (
    _strip_wrapping_parens,
    generate_func_residual_entries,
    polish_residual_segment,
    promote_captured_identifiers_to_arguments,
)
from GenMonads.absprog.parse_coq import parse_synthesized_components
from GenMonads.absprog.templates import prompt_payload, render_prompt, render_repair_prompt
from GenMonads.cli_common import read_configure_value


def _load_json(path: str) -> Dict:
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)


def _write_text(path: str, content: str) -> str:
    parent = os.path.dirname(path)
    if parent:
        os.makedirs(parent, exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        f.write(content)
    return path


def _write_json(path: str, content: Dict) -> str:
    parent = os.path.dirname(path)
    if parent:
        os.makedirs(parent, exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        json.dump(content, f, indent=2)
        f.write("\n")
    return path


def _replay_gold_response(example: Dict) -> str:
    gold = example.get("gold")
    if not gold:
        raise ValueError("Replay backend requires an example JSON with a gold section")

    components = gold.get("components", {})
    lines = [
        "```coq",
        f"Definition MretTy : Type := {gold['MretTy']}.",
        components["M_loop_before"],
        components["M_1"],
        components["M_2"],
        components["M_loop_end"],
        "```",
        "",
    ]
    return "\n".join(lines)


# Default ceiling for any single command-backend invocation (20 minutes).
# Workdir-mode codex may iterate coqc multiple times; the legacy 10-min
# ceiling was too tight for that flow.
DEFAULT_COMMAND_TIMEOUT_SECONDS = 1200


class PrerequisiteError(Exception):
    """Pre-spawn / environment failure — codex missing, ``_CoqProject``
    missing, a cross-file callee lib still unsynthesized, etc.

    These conditions are deterministic: they cannot succeed after a
    retry unless the world changes out-of-band.  The synthesis pipeline
    catches this distinct exception type so it records one attempt with
    ``failure_kind="prerequisite"`` and aborts the per-function retry
    loop — instead of burning every ``--max-retries`` slot on the same
    actionable error.
    """


def _run_command_backend(
    prompt_text: str,
    context: Dict,
    output_dir: str,
    sibling_dirs: Optional[List[str]] = None,
    monad: str = "staterel",
    timeout: Optional[int] = DEFAULT_COMMAND_TIMEOUT_SECONDS,
    coq_lib_dir: Optional[str] = None,
    use_block_renderer: bool = False,
) -> str:
    """Workdir-mode synthesis backend.

    Builds a curated workdir under *output_dir* (which is the per-function
    synthesis output directory — reused across retries), invokes
    ``codex exec -C <workdir>`` sandboxed to ``workspace-write``, then
    enforces the agent's strict replacement contract (file-system whitelist
    + structural skeleton diff).  Returns the filled lib text as the
    "response" the rest of the pipeline parses and assembles.

    *coq_lib_dir* is the directory holding already-synthesized peer
    ``_rel_lib.v`` files (passed through from ``--coq-lib-dir`` at the CLI
    layer).  When ``None`` we fall back to
    ``read_configure_value("COQ_LIB_DIR")``.

    Raises:
        PrerequisiteError: pre-spawn environment failure — codex absent
            from PATH, ``_CoqProject`` not found, or a cross-file callee
            lib still unsynthesized.  Deterministic; no retry will help.
        ValueError: recoverable backend failures — codex non-zero exit,
            timeout, contract violation in the filled skeleton.  Retried
            with a repair prompt.
    """
    from GenMonads.absprog.assemble import generate_rel_lib_skeleton_for_file
    from GenMonads.absprog import workdir as workdir_mod

    codex = shutil.which("codex")
    if not codex:
        raise PrerequisiteError(
            "codex executable not found in PATH.  Workdir-mode synthesis "
            "requires the codex CLI."
        )

    c_file = context["source"]["c_file"]
    basename = context["source"].get("file_id") or _basename_from_c_file(c_file)

    # Pre-spawn hard checks (#29).  COQ_LIB_DIR must be set and every
    # cross-file callee lib in the skeleton must already be on disk.  Use
    # the per-invocation override when supplied; otherwise read CONFIGURE.
    effective_coq_lib_dir = coq_lib_dir or _coq_lib_dir_or_none()

    # Generate the skeleton from the C source.  This is deterministic given
    # the input — same input → identical skeleton across retries.  Passing
    # the lib dir lets cross-file ``Require Import`` lines pick up the
    # canonical qualified logical path from ``_CoqProject``.
    skeleton_text = generate_rel_lib_skeleton_for_file(
        c_file, sibling_dirs=sibling_dirs, monad=monad,
        coq_lib_dir=effective_coq_lib_dir,
        use_block_renderer=use_block_renderer,
    )
    try:
        workdir_mod.check_prerequisites(skeleton_text, effective_coq_lib_dir)
    except ValueError as exc:
        # Missing callee libs / unset COQ_LIB_DIR are deterministic env
        # problems, not LLM mistakes — surface as PrerequisiteError.
        raise PrerequisiteError(str(exc)) from exc

    try:
        paths = workdir_mod.prepare_workdir(
            parent_dir=output_dir, basename=basename, skeleton_text=skeleton_text,
        )
    except ValueError as exc:
        # _CoqProject not found is also a deterministic env problem.
        raise PrerequisiteError(str(exc)) from exc

    # Snapshot for the file-system whitelist (Layer 2).
    before = workdir_mod.snapshot_workdir(paths["workdir"])

    cmd = [
        codex, "exec",
        "-C", paths["workdir"],
        "--skip-git-repo-check",
        "-s", "workspace-write",
        "-c", 'sandbox_permissions=[]',
        "-c", "features.tool_call_mcp_elicitation=false",
        "--color", "never",
        "--output-last-message", paths["transcript"],
        "-",
    ]
    try:
        proc = subprocess.run(
            cmd, text=True, input=prompt_text, capture_output=True, timeout=timeout,
        )
    except subprocess.TimeoutExpired as exc:
        raise ValueError(
            f"codex exec timed out after {timeout}s "
            f"(set a higher --command-timeout if needed)"
        ) from exc
    if proc.returncode != 0:
        detail = proc.stderr.strip() or proc.stdout.strip() or f"exit code {proc.returncode}"
        raise ValueError(f"codex exec failed: {detail}")

    if not os.path.isfile(paths["skeleton_path"]):
        raise ValueError(
            "Agent did not produce a filled skeleton at "
            f"{paths['skeleton_path']}"
        )
    with open(paths["skeleton_path"], "r", encoding="utf-8") as f:
        filled_text = f.read()

    must_define = _must_define_from_context(context)
    ok, msg = workdir_mod.validate_attempt(
        paths["workdir"], before, skeleton_text, filled_text,
        must_define=must_define, basename=basename,
    )
    if not ok:
        raise ValueError(msg)

    return filled_text


def _basename_from_c_file(c_file: str) -> str:
    """Derive the lib basename (stem without ``.c`` / ``_rel.c``)."""
    name = os.path.basename(c_file)
    if name.endswith(".c"):
        name = name[:-2]
    if name.endswith("_rel"):
        name = name[:-4]
    return name


_TOP_LEVEL_DEFINITION_RE = re.compile(
    r"^Definition\s+(\w+)\s*[:=]", re.MULTILINE,
)


def _filter_must_define_against_emitted_lib(
    context: Dict,
    use_block_renderer: bool,
    sibling_dirs: Optional[List[str]] = None,
    monad: str = "staterel",
) -> None:
    """Phase 2.0 reconciliation between ``must_define`` and the lib.

    The ``must_define`` list in ``generation_policy`` is computed by
    ``context.py`` from the function's scaffold-required components (one
    entry per LLM hole the agent must replace).  When
    ``use_block_renderer=True`` is in effect, the rel_lib stage emitted
    a concrete ``Definition <name> := …`` for the mechanizable Shape 1
    functions.  Those names must be removed from ``must_define`` so:

    1. The synthesis prompt's "Definitions to Provide" list doesn't
       confusingly include names the agent shouldn't touch.
    2. The workdir strict-diff validator's must_set matches what the
       skeleton actually offers as Parameters (not what it might offer
       under different flag settings).

    We regenerate the skeleton from the C source using the same flag the
    rel_lib stage used.  Inspecting an arbitrary lib file on disk would
    be unsafe — it might be a stale filled lib from a prior synthesis
    that has Definitions for everything.

    No-op when ``use_block_renderer`` is ``False`` (legacy Parameter
    emission already keeps must_define consistent).
    """
    if not use_block_renderer:
        return
    c_file = context.get("source", {}).get("c_file")
    if not c_file or not os.path.isfile(c_file):
        return
    from GenMonads.absprog.assemble import generate_rel_lib_skeleton_for_file
    try:
        skeleton_text = generate_rel_lib_skeleton_for_file(
            c_file, sibling_dirs=sibling_dirs, monad=monad,
            use_block_renderer=use_block_renderer,
        )
    except Exception:
        return
    definition_names = {
        m.group(1) for m in _TOP_LEVEL_DEFINITION_RE.finditer(skeleton_text)
    }
    if not definition_names:
        return
    gp = context.get("generation_policy") or {}
    must_define = gp.get("must_define") or []
    filtered = [n for n in must_define if n not in definition_names]
    if filtered != must_define:
        gp["must_define"] = filtered
        context["generation_policy"] = gp


def _coq_lib_dir_or_none() -> Optional[str]:
    """Resolve COQ_LIB_DIR via env or CONFIGURE; ``None`` if unset."""
    try:
        return read_configure_value("COQ_LIB_DIR")
    except Exception:
        return None


def _must_define_from_context(context: Dict) -> List[str]:
    """The list of fully-prefixed Parameter names the LLM is expected to
    replace, sourced from the context's ``generation_policy``."""
    gp = context.get("generation_policy") or {}
    return list(gp.get("must_define") or [])


def generate_candidate_response(
    context: Dict,
    backend: str,
    prompt_text: str,
    prompt_file: str,
    context_file: str,
    output_dir: str,
    backend_response_file: str,
    replay_from: Optional[str] = None,
    response_file: Optional[str] = None,
    command: Optional[str] = None,
    command_timeout: Optional[int] = DEFAULT_COMMAND_TIMEOUT_SECONDS,
    sibling_dirs: Optional[List[str]] = None,
    monad: str = "staterel",
    coq_lib_dir: Optional[str] = None,
    use_block_renderer: bool = False,
) -> str:
    if backend == "gold-example":
        if replay_from:
            example = _load_json(replay_from)
        else:
            example = context
        return _replay_gold_response(example)

    if backend == "response-file":
        if not response_file:
            raise ValueError("response-file backend requires --response-file")
        with open(response_file, "r", encoding="utf-8") as f:
            return f.read()

    if backend == "command":
        # The ``command`` kwarg is retained for CLI backwards-compat but
        # ignored — workdir-mode owns the codex invocation now.
        return _run_command_backend(
            prompt_text=prompt_text,
            context=context,
            output_dir=output_dir,
            sibling_dirs=sibling_dirs,
            monad=monad,
            timeout=command_timeout,
            coq_lib_dir=coq_lib_dir,
            use_block_renderer=use_block_renderer,
        )

    raise ValueError(f"Unsupported backend: {backend}")


def _default_check_result() -> Dict:
    return {
        "status": "skipped",
        "passed": False,
        "reason": "check disabled",
        "stdout": "",
        "stderr": "",
    }


def _validate_opaque_callee_usage(context: Dict, response_text: str) -> None:
    required_programs = context.get("generation_policy", {}).get("opaque_external_programs", [])
    missing = []
    for name in required_programs:
        if name not in response_text:
            missing.append(name)

    if missing:
        obligations = context.get("opaque_call_obligations", [])
        detail_lines = [
            "Missing required opaque callee program(s) in synthesized response:",
            ", ".join(missing),
        ]
        if obligations:
            detail_lines.append("Required opaque call obligations:")
            for obligation in obligations:
                if obligation["callee"] in missing:
                    detail_lines.append(
                        f"- {obligation['call_site']} -> {obligation['callee']}"
                    )
        raise ValueError("\n".join(detail_lines))

    # Reject `_ <- callee_M(...)` (or `_ <- callee_M ...`): the LLM is calling
    # the opaque program but discarding its result, which makes the call
    # semantically meaningless.  Force the result to be bound to a named
    # variable so the rest of the body must reason about it.
    discarded = []
    for name in required_programs:
        pattern = rf"\b_\s*<-\s*{re.escape(name)}\b"
        if re.search(pattern, response_text):
            discarded.append(name)
    if discarded:
        raise ValueError(
            "Opaque callee result must be bound to a named variable, not `_`. "
            "Offending call(s): " + ", ".join(discarded)
        )


def _validate_early_return_scaffold(context: Dict, response_text: str) -> None:
    control_flow = context.get("control_flow") or context.get("target", {}).get("control_flow", {})
    if not control_flow.get("needs_early_result"):
        return

    if "early_result" not in response_text:
        detail_lines = [
            "Missing early-return-aware scaffold in synthesized response.",
            f"Template case: {control_flow.get('template_case', 'unknown')}",
            "Expected the generated definitions to mention `early_result`.",
        ]
        raise ValueError("\n".join(detail_lines))


def _normalize_coq_type(text: str) -> str:
    """Collapse whitespace and strip redundant outer parens for comparison."""
    text = re.sub(r"\s+", " ", text).strip()
    while text.startswith("(") and text.endswith(")"):
        # Only strip if the outer parens are balanced as a single group.
        depth = 0
        balanced = True
        for i, ch in enumerate(text):
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0 and i != len(text) - 1:
                    balanced = False
                    break
        if balanced:
            text = text[1:-1].strip()
        else:
            break
    return text


def _validate_one_guard_signature(
    response_text: str,
    guard_name: str,
    expected_sig: str,
) -> None:
    m = re.search(
        rf"Definition\s+{re.escape(guard_name)}\s*:\s*(.+?)\s*:=",
        response_text,
        re.DOTALL,
    )
    if not m:
        raise ValueError(
            f"Missing required `Definition {guard_name} : ... :=` in synthesized "
            "response (GuardGen could not produce this loop guard, so the LLM "
            "must supply it)."
        )
    expected = _normalize_coq_type(expected_sig)
    actual = _normalize_coq_type(m.group(1))
    if expected and actual != expected:
        raise ValueError(
            f"`{guard_name}` signature must not change.\n"
            f"Required: {expected}\n"
            f"Got:      {actual}"
        )


def _validate_guard_signature(context: Dict, response_text: str) -> None:
    """Validate every guardP the LLM is responsible for.

    Single-loop case: when ``"guardP"`` is in ``required_components``, require
    a ``Definition {fn}_guardP`` with the pinned signature.

    Forest case: per-loop ``loop{k}_guardP`` Definitions, each with the
    matching ``{Sk} -> Prop`` signature pulled from
    ``control_flow.prompt_signatures``.
    """
    control_flow = context.get("control_flow") or context.get("target", {}).get("control_flow", {})
    required = control_flow.get("required_components", [])
    func_name = context["summary"]["func_name"]

    # Single-loop guard
    if "guardP" in required:
        _validate_one_guard_signature(
            response_text,
            f"{func_name}_guardP",
            control_flow.get("guard_signature", ""),
        )

    # Forest guards: any component matching ``loop{k}_guardP``.
    prompt_sigs = control_flow.get("prompt_signatures", {}) or {}
    for component in required:
        if not re.fullmatch(r"loop\d+_guardP", component):
            continue
        _validate_one_guard_signature(
            response_text,
            f"{func_name}_{component}",
            prompt_sigs.get(component, ""),
        )


def _attempt_dir(output_dir: str, attempt_index: int) -> str:
    return os.path.join(output_dir, f"attempt-{attempt_index}")


def _attempt_file(attempt_dir: str, context_id: str, suffix: str) -> str:
    return os.path.join(attempt_dir, f"{context_id}.{suffix}")


def _root_file(output_dir: str, context_id: str, suffix: str) -> str:
    return os.path.join(output_dir, f"{context_id}.{suffix}")


def _default_coq_lib_dir() -> str:
    """Return COQ_LIB_DIR from env or CONFIGURE; error if neither is set."""
    value = read_configure_value("COQ_LIB_DIR")
    if value is None:
        raise RuntimeError(
            "COQ_LIB_DIR is not set. Define it via environment variable or in "
            "the CONFIGURE file at the repo root."
        )
    return value


def _format_residual_extern_decl(entry: Dict) -> str:
    arg_types = []
    for identifier in entry.captured_identifiers:
        ident_type = entry.captured_identifier_types.get(identifier)
        if not ident_type:
            raise ValueError(
                f"Missing captured type for residual argument '{identifier}' in "
                f"{entry.caller_component} call {entry.call_index}"
            )
        arg_types.append(ident_type)

    if not entry.callee_return_type or not entry.caller_return_type:
        raise ValueError(
            f"Missing residual signature types for {entry.caller_component} call {entry.call_index}"
        )

    arg_types.append(_strip_wrapping_parens(entry.callee_return_type.strip()))
    caller_type = entry.caller_return_type.strip()
    rendered = " -> ".join(arg_types + [f"program unit {caller_type}"])
    return (
        f"(residual_prog_in_{entry.caller_component}_call_{entry.call_index}: "
        f"{rendered})"
    )


def _append_missing_residual_decls_to_rel_c(rel_c_path: str, decls: List[str]) -> str:
    if not os.path.isfile(rel_c_path) or not decls:
        return ""

    with open(rel_c_path, "r", encoding="utf-8") as f:
        content = f.read()

    match = re.search(
        r"/\*@ Extern Coq\s*\n(?P<body>.*?\n)(?P<closing_ws>[ \t]*)\*/",
        content,
        re.DOTALL,
    )
    if not match:
        return ""

    body = match.group("body")
    closing_ws = match.group("closing_ws")
    existing_names = set(
        re.findall(r"\(\s*([A-Za-z_][A-Za-z0-9_']*)\s*:", body)
    )
    new_decls = []
    for decl in decls:
        name_match = re.match(r"\(\s*([A-Za-z_][A-Za-z0-9_']*)\s*:", decl)
        if name_match and name_match.group(1) in existing_names:
            continue
        new_decls.append(decl)
    if not new_decls:
        return rel_c_path

    # Infer per-line indentation from the existing body lines, falling back to closing_ws.
    body_lines = [line for line in body.splitlines() if line.strip()]
    if body_lines:
        indent_match = re.match(r"^([ \t]*)", body_lines[0])
        padding = indent_match.group(1) if indent_match else closing_ws
    else:
        padding = closing_ws

    insertion = "\n".join(f"{padding}{decl}" for decl in new_decls)
    close_marker = match.start("closing_ws")
    updated = content[:close_marker] + insertion + "\n" + closing_ws + "*/" + content[match.end():]

    with open(rel_c_path, "w", encoding="utf-8") as f:
        f.write(updated)
    return rel_c_path


def _extract_mretty_type(rel_lib_path: str) -> str:
    with open(rel_lib_path, "r", encoding="utf-8") as f:
        source = f.read()
    match = re.search(
        r"^Definition\s+MretTy\s*:\s*Type\s*:=\s*(.+?)\.\s*$",
        source,
        re.MULTILINE,
    )
    if not match:
        return ""
    return re.sub(r"%type\b", "", match.group(1)).strip()


def _wrap_type_for_substitution(concrete: str) -> str:
    stripped = concrete.strip()
    if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", stripped):
        return stripped
    if stripped.startswith("(") and stripped.endswith(")"):
        return stripped
    return f"({stripped})"


def _eliminate_mretty_in_rel_c(rel_c_path: str, concrete_type) -> str:
    """Substitute synthesized ``MretTy`` types into ``_rel.c``.

    ``concrete_type`` may be either:
      - a single string: substitute the bare ``MretTy`` token (single-function
        files emit one shared ``MretTy``).
      - a mapping ``{func_name: concrete_type}``: substitute each per-function
        ``{func_name}_MretTy`` token independently (multi-function files emit
        per-function ``MretTy`` names to match the merged rel_lib).
    """
    if not rel_c_path or not os.path.isfile(rel_c_path) or not concrete_type:
        return ""

    with open(rel_c_path, "r", encoding="utf-8") as f:
        content = f.read()

    if "MretTy" not in content:
        return rel_c_path

    updated = content
    if isinstance(concrete_type, dict):
        for func_name, concrete in concrete_type.items():
            if not concrete:
                continue
            token = f"{func_name}_MretTy"
            replacement = _wrap_type_for_substitution(concrete)
            updated = re.sub(
                rf"^[ \t]*/\*@\s*Extern\s+Coq\s*\(\s*{re.escape(token)}\s*::\s*\*\s*\)\s*\*/[ \t]*\n?",
                "",
                updated,
                flags=re.MULTILINE,
            )
            updated = re.sub(rf"\b{re.escape(token)}\b", replacement, updated)
    else:
        replacement = _wrap_type_for_substitution(concrete_type)
        updated = re.sub(
            r"^[ \t]*/\*@\s*Extern\s+Coq\s*\(\s*MretTy\s*::\s*\*\s*\)\s*\*/[ \t]*\n?",
            "",
            updated,
            flags=re.MULTILINE,
        )
        updated = re.sub(r"\bMretTy\b", replacement, updated)

    if updated == content:
        return rel_c_path

    with open(rel_c_path, "w", encoding="utf-8") as f:
        f.write(updated)
    return rel_c_path


def _sync_residual_artifacts(
    context: Dict,
    assembled_rel_lib: str,
    rel_c_path: Optional[str] = None,
) -> Dict[str, str]:
    if not assembled_rel_lib or not os.path.isfile(assembled_rel_lib):
        return {}

    patched_rel_c = ""
    caller_component = f"{context['summary']['func_name']}_M"
    # Collect callee signatures from the context so cross-file callees (only
    # imported via `Require Import`) still get a return-type annotation on
    # their residual definitions.
    callee_signatures: Dict[str, str] = {}
    for callee in context.get("available_callees", []):
        opaque_program = callee.get("opaque_program")
        sig = (callee.get("externals") or {}).get("M")
        if opaque_program and sig:
            callee_signatures[opaque_program] = sig

    all_entries = []
    for callee in context.get("available_callees", []):
        opaque_program = callee.get("opaque_program")
        if not opaque_program:
            continue
        entries = generate_func_residual_entries(
            assembled_rel_lib,
            opaque_program,
            caller_component,
            extra_signatures=callee_signatures,
        )
        all_entries.extend(entries)

    if not all_entries:
        if rel_c_path:
            mretty_type = _extract_mretty_type(assembled_rel_lib)
            patched_rel_c = _eliminate_mretty_in_rel_c(rel_c_path, mretty_type)
        return {"rel_c": patched_rel_c}

    all_entries = [polish_residual_segment(entry) for entry in all_entries]
    rendered_defs = [
        promote_captured_identifiers_to_arguments(
            entry.definition,
            entry.captured_identifiers,
            entry.captured_identifier_types,
        )
        for entry in all_entries
    ]
    with open(assembled_rel_lib, "r", encoding="utf-8") as f:
        original = f.read()
    new_content = original.rstrip() + "\n\n" + "\n\n".join(rendered_defs) + "\n"
    with open(assembled_rel_lib, "w", encoding="utf-8") as f:
        f.write(new_content)

    if rel_c_path:
        patched_rel_c = _append_missing_residual_decls_to_rel_c(
            rel_c_path,
            [_format_residual_extern_decl(entry) for entry in all_entries],
        ) or rel_c_path
        mretty_type = _extract_mretty_type(assembled_rel_lib)
        _eliminate_mretty_in_rel_c(rel_c_path, mretty_type)

    return {
        "rel_lib": assembled_rel_lib,
        "rel_c": patched_rel_c,
    }


def _promote_rel_lib_if_accepted(
    assembled_file: str,
    context_id: str,
    status: str,
    coq_lib_dir: Optional[str] = None,
) -> str:
    """Copy the accepted lib into the project's ``COQ_LIB_DIR``.

    *coq_lib_dir* — when supplied, overrides the CONFIGURE/env default
    (``--coq-lib-dir`` from the CLI flows here).  Without it, the lib was
    being silently dropped into ``./output/gen/libs/`` even when the user
    had asked for a different directory.
    """
    if status != "passed" or not assembled_file or not os.path.isfile(assembled_file):
        return ""

    target_dir = coq_lib_dir or _default_coq_lib_dir()
    os.makedirs(target_dir, exist_ok=True)
    target_root = os.path.join(target_dir, f"{context_id}_rel_lib")
    target_path = f"{target_root}.v"

    # Copy only the .v source; the .vo/.vok/.vos/.glob from the attempt dir
    # were compiled without the lib dir's logical-path prefix (the attempt
    # dir is outside `-R <target_dir> <prefix>`), so reusing them would leave
    # a name-mismatched .vo that breaks later `Require Import`.
    shutil.copyfile(assembled_file, target_path)
    # Remove any stale per-file compiled artifacts from a prior run.
    for ext in (".vo", ".vok", ".vos", ".glob"):
        stale = f"{target_root}{ext}"
        if os.path.isfile(stale):
            try:
                os.remove(stale)
            except OSError:
                pass

    # Recompile in target_dir so the project's `-R <target_dir> <prefix>`
    # applies and the embedded library name picks up the correct prefix.
    recheck = check_rocq_file(target_path)
    if recheck["status"] == "failed":
        print(
            f"Warning: recompile of promoted {target_path} failed: "
            f"{recheck.get('stderr', '').strip()}"
        )
    return target_path


def _final_status_from_attempt(attempt: Dict) -> str:
    if attempt["status"] == "passed":
        return "passed"
    if attempt["status"] == "assembled":
        return "assembled"
    return "failed"


def _build_attempt_summary(
    attempt_index: int,
    files: Dict[str, str],
    status: str,
    failure_kind: str,
    failure_message: str,
    check_result: Dict,
) -> Dict:
    return {
        "attempt": attempt_index,
        "status": status,
        "failure_kind": failure_kind,
        "failure_message": failure_message,
        "files": files,
        "check": check_result,
    }


def _copy_final_attempt_files(final_attempt: Dict, output_dir: str, context_id: str) -> Dict[str, str]:
    final_files = {}
    for label, path in final_attempt["files"].items():
        if not path:
            continue
        if label in {"context", "patched_rel_c"}:
            final_files[label] = path
            continue

        if label == "assembled_rel_lib":
            target = os.path.join(output_dir, f"{context_id}_rel_lib.v")
        elif label == "summary":
            target = os.path.join(output_dir, f"{context_id}.summary.json")
        else:
            suffix = os.path.basename(path).split(f"{context_id}.", 1)[-1]
            target = _root_file(output_dir, context_id, suffix)

        with open(path, "r", encoding="utf-8") as src:
            _write_text(target, src.read())
        final_files[label] = target
    return final_files


def _record_attempt(
    attempt_index: int,
    attempt_dir: str,
    context_id: str,
    files: Dict[str, str],
    status: str,
    failure_kind: str,
    failure_message: str,
    check_result: Dict,
    attempts: List[Dict],
    response_text: str,
) -> Tuple[str, str, str]:
    attempt_summary = _build_attempt_summary(
        attempt_index, files, status, failure_kind, failure_message, check_result
    )
    attempt_summary_file = _attempt_file(attempt_dir, context_id, "summary.json")
    _write_json(attempt_summary_file, attempt_summary)
    attempt_summary["files"]["summary"] = attempt_summary_file
    attempts.append(attempt_summary)
    return response_text, failure_kind, failure_message


def _build_final_summary(
    input_path: str,
    output_dir: str,
    context: Dict,
    backend: str,
    max_retries: int,
    attempts: List[Dict],
    final_attempt: Dict,
    status: str,
    promote_rel_lib: bool = True,
    coq_lib_dir: Optional[str] = None,
) -> Dict:
    final_files = _copy_final_attempt_files(final_attempt, output_dir, context["id"])
    summary = {
        "input_path": input_path,
        "context_id": context["id"],
        "func_name": context["summary"]["func_name"],
        "backend": backend,
        "max_retries": max_retries,
        "attempt_count": len(attempts),
        "attempts": attempts,
        "files": final_files,
        "check": final_attempt["check"],
        "status": status,
    }
    if promote_rel_lib:
        promoted_path = _promote_rel_lib_if_accepted(
            final_attempt["files"].get("assembled_rel_lib", ""),
            context["id"], status,
            coq_lib_dir=coq_lib_dir,
        )
        if promoted_path:
            summary["files"]["promoted_rel_lib"] = promoted_path
    summary_file = _root_file(output_dir, context["id"], "summary.json")
    _write_json(summary_file, summary)
    summary["files"]["summary"] = summary_file
    return summary


def run_synthesis_pipeline(
    input_path: str,
    output_dir: str,
    func_name: Optional[str] = None,
    backend: str = "gold-example",
    replay_from: Optional[str] = None,
    response_file: Optional[str] = None,
    command: Optional[str] = None,
    few_shot_paths: Optional[List[str]] = None,
    run_check: bool = True,
    max_retries: int = 0,
    rel_c_path: Optional[str] = None,
    promote_rel_lib: bool = True,
    command_timeout: Optional[int] = DEFAULT_COMMAND_TIMEOUT_SECONDS,
    sibling_dirs: Optional[List[str]] = None,
    monad: str = "staterel",
    coq_lib_dir: Optional[str] = None,
    use_block_renderer: bool = False,
) -> Dict:
    os.makedirs(output_dir, exist_ok=True)

    if input_path.endswith(".json"):
        context = _load_json(input_path)
        context_file = input_path
    else:
        context = collect_synthesis_context(
            input_path, func_name=func_name, sibling_dirs=sibling_dirs
        )
        context_file = _root_file(output_dir, context["id"], "context.auto.json")
        write_synthesis_context(
            input_path, context_file, func_name=func_name, sibling_dirs=sibling_dirs
        )

    # Phase 2.0 — when the lib emits a concrete ``Definition fn_M`` for
    # a function (mechanized via use_block_renderer), the agent must NOT
    # be asked to fill it (it's already complete).  Filter must_define
    # against the freshly-regenerated skeleton so the prompt + workdir
    # validator agree.  No-op when use_block_renderer is False.
    _filter_must_define_against_emitted_lib(
        context, use_block_renderer=use_block_renderer,
        sibling_dirs=sibling_dirs, monad=monad,
    )

    examples = [_load_json(path) for path in (few_shot_paths or [])]
    base_prompt = render_prompt(context, examples)
    attempts: List[Dict] = []
    previous_response = ""
    previous_failure_kind = ""
    previous_failure_message = ""
    total_attempts = max_retries + 1

    for attempt_index in range(total_attempts):
        attempt_dir = _attempt_dir(output_dir, attempt_index)
        os.makedirs(attempt_dir, exist_ok=True)

        if attempt_index == 0:
            prompt = base_prompt
        else:
            prompt = render_repair_prompt(
                context,
                previous_response=previous_response,
                failure_kind=previous_failure_kind,
                failure_message=previous_failure_message,
                few_shot_examples=examples,
            )

        prompt_file = _attempt_file(attempt_dir, context["id"], "prompt.txt")
        prompt_payload_file = _attempt_file(attempt_dir, context["id"], "prompt.json")
        backend_response_file = _attempt_file(attempt_dir, context["id"], "backend-response.txt")
        response_out_file = _attempt_file(attempt_dir, context["id"], "response.txt")
        parsed_file = _attempt_file(attempt_dir, context["id"], "parsed.json")
        assembled_file = os.path.join(attempt_dir, f"{context['id']}_rel_lib.v")

        _write_text(prompt_file, prompt)
        _write_json(prompt_payload_file, prompt_payload(context, prompt, few_shot_paths))

        files = {
            "context": context_file,
            "prompt": prompt_file,
            "prompt_payload": prompt_payload_file,
            "response": response_out_file,
            "parsed": "",
            "assembled_rel_lib": "",
            "patched_rel_c": "",
        }

        check_result = _default_check_result()
        failure_kind = ""
        failure_message = ""
        status = "failed"

        try:
            response_text = generate_candidate_response(
                context,
                backend=backend,
                prompt_text=prompt,
                prompt_file=prompt_file,
                context_file=context_file,
                # Workdir-mode prepares ``output_dir/workdir/`` (shared
                # across attempts) — pass the per-function dir, not the
                # per-attempt one.
                output_dir=output_dir,
                backend_response_file=backend_response_file,
                replay_from=replay_from,
                response_file=response_file,
                command=command,
                command_timeout=command_timeout,
                sibling_dirs=sibling_dirs,
                monad=monad,
                coq_lib_dir=coq_lib_dir,
                use_block_renderer=use_block_renderer,
            )
        except PrerequisiteError as exc:
            # Pre-spawn environment failure — codex missing, _CoqProject
            # missing, callee lib missing.  Deterministic; retrying won't
            # change the answer.  Record one attempt and break the loop.
            response_text = ""
            failure_kind = "prerequisite"
            failure_message = str(exc)
            _write_text(response_out_file, response_text)
            previous_response, previous_failure_kind, previous_failure_message = _record_attempt(
                attempt_index, attempt_dir, context["id"], files, status,
                failure_kind, failure_message, check_result, attempts, response_text,
            )
            break
        except Exception as exc:
            response_text = ""
            failure_kind = "backend"
            failure_message = str(exc)
            _write_text(response_out_file, response_text)
            previous_response, previous_failure_kind, previous_failure_message = _record_attempt(
                attempt_index, attempt_dir, context["id"], files, status,
                failure_kind, failure_message, check_result, attempts, response_text,
            )
            continue

        _write_text(response_out_file, response_text)

        try:
            _validate_opaque_callee_usage(context, response_text)
            _validate_early_return_scaffold(context, response_text)
            _validate_guard_signature(context, response_text)
        except Exception as exc:
            failure_kind = "validation"
            failure_message = str(exc)
            previous_response, previous_failure_kind, previous_failure_message = _record_attempt(
                attempt_index, attempt_dir, context["id"], files, status,
                failure_kind, failure_message, check_result, attempts, response_text,
            )
            continue

        try:
            required = context.get("control_flow", {}).get("required_components")
            blocks = parse_synthesized_components(
                response_text,
                context["summary"]["func_name"],
                required=required,
            )
            _write_json(parsed_file, blocks)
            files["parsed"] = parsed_file
        except Exception as exc:
            failure_kind = "parse"
            failure_message = str(exc)
            previous_response, previous_failure_kind, previous_failure_message = _record_attempt(
                attempt_index, attempt_dir, context["id"], files, status,
                failure_kind, failure_message, check_result, attempts, response_text,
            )
            continue

        write_assembled_rel_lib(
            context["source"]["c_file"],
            context["summary"]["func_name"],
            blocks,
            assembled_file,
            sibling_dirs=sibling_dirs,
            monad=monad,
        )
        files["assembled_rel_lib"] = assembled_file

        if run_check:
            check_result = check_rocq_file(assembled_file)

        if not run_check or check_result.get("status") == "passed":
            residual_files = {}
            try:
                residual_files = _sync_residual_artifacts(
                    context, assembled_file, rel_c_path=rel_c_path
                )
            except Exception as exc:
                failure_kind = "residual_sync"
                failure_message = str(exc)
                previous_response, previous_failure_kind, previous_failure_message = _record_attempt(
                    attempt_index, attempt_dir, context["id"], files, status,
                    failure_kind, failure_message, check_result, attempts, response_text,
                )
                continue

            files["patched_rel_c"] = residual_files.get("rel_c", "")
            if run_check and residual_files.get("rel_lib"):
                check_result = check_rocq_file(assembled_file)
                if check_result.get("status") != "passed":
                    failure_kind = "rocq"
                    failure_message = (
                        check_result.get("stderr")
                        or check_result.get("stdout")
                        or "Rocq check failed after residual sync"
                    )
                    previous_response, previous_failure_kind, previous_failure_message = _record_attempt(
                        attempt_index, attempt_dir, context["id"], files, status,
                        failure_kind, failure_message, check_result, attempts, response_text,
                    )
                    continue

            status = "passed" if run_check else "assembled"
            _record_attempt(
                attempt_index, attempt_dir, context["id"], files, status,
                failure_kind, failure_message, check_result, attempts, response_text,
            )
            return _build_final_summary(
                input_path, output_dir, context, backend, max_retries,
                attempts, attempts[-1], status,
                coq_lib_dir=coq_lib_dir,
            )

        failure_kind = "rocq"
        failure_message = check_result.get("stderr") or check_result.get("stdout") or "Rocq check failed"
        previous_response, previous_failure_kind, previous_failure_message = _record_attempt(
            attempt_index, attempt_dir, context["id"], files, status,
            failure_kind, failure_message, check_result, attempts, response_text,
        )

    final_attempt = attempts[-1]
    return _build_final_summary(
        input_path, output_dir, context, backend, max_retries,
        attempts, final_attempt, _final_status_from_attempt(final_attempt),
        promote_rel_lib=promote_rel_lib,
        coq_lib_dir=coq_lib_dir,
    )
