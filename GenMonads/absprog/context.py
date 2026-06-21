import json
import os
import re
from typing import Dict, List, Optional

from GenMonads.addabstract import add_safeexec_predicate, process_funcspec_with_safeexec
from GenMonads.absprog.gen_rel_lib import needs_mretty
from GenMonads.absprog.loop_forest import build_loop_templates
from GenMonads.early_return import detect_early_return_shape
from GenMonads.transshape.process_and_translate import process_and_translate_file
from GenMonads.translate_c_file import _extract_function_body, collect_func_extern_info


def _normalize_block(text: str) -> str:
    lines = [line.rstrip() for line in text.strip().splitlines()]
    return "\n".join(lines)


def _tuple_type(types: List[str]) -> str:
    if len(types) == 1:
        return types[0]
    return "(" + " * ".join(types) + ")"


def _type_arg(type_expr: str) -> str:
    """Parenthesize ``type_expr`` if it would be mis-parsed as multiple
    tokens when used as an argument in a type application (``MONAD t``,
    ``CntOrBrk t s``, ``early_result t r``).  Single-token types and
    already-parenthesized types are returned unchanged."""
    expr = type_expr.strip()
    if not expr:
        return expr
    if expr.startswith("(") and expr.endswith(")"):
        return expr
    if " " in expr:
        return f"({expr})"
    return expr


def _curried_type(types: List[str]) -> str:
    if not types:
        return ""
    return " -> ".join(types) + " -> "


def _return_type_from_types(types: List[str]) -> str:
    if not types:
        return "unit"
    return _tuple_type(types)


def _require_var_types(info: Dict, key: str, count_key: str) -> List[str]:
    count = info[count_key]
    if count == 0:
        return []

    var_types = info.get(key)
    if var_types is None:
        raise ValueError(
            f"Missing {key} for function '{info.get('func_name', '<unknown>')}' with {count} generated variable(s)"
        )
    if len(var_types) != count:
        raise ValueError(
            f"{key} length mismatch for function '{info.get('func_name', '<unknown>')}': "
            f"expected {count}, got {len(var_types)}"
        )
    return list(var_types)


def _collect_functions(result: Dict) -> List[Dict]:
    if result.get("functions"):
        return result["functions"]
    return [result]


def _make_context_id(c_file: str, result: Dict, func_name: str) -> str:
    basename = os.path.splitext(os.path.basename(c_file))[0]
    functions = _collect_functions(result)
    if len(functions) > 1:
        return func_name
    return basename


def _select_function(
    result_or_functions, func_name: Optional[str], file_path: Optional[str] = None
) -> Dict:
    functions = (
        result_or_functions
        if isinstance(result_or_functions, list)
        else result_or_functions.get("functions") or [result_or_functions]
    )
    if file_path is None:
        file_path = (
            result_or_functions.get("file")
            if isinstance(result_or_functions, dict)
            else "<unknown>"
        )

    if func_name:
        for func_data in functions:
            name = func_data.get("func_name", func_data.get("function"))
            if name == func_name:
                return func_data
        raise ValueError(f"Function '{func_name}' not found in {file_path}")

    local_functions = [f for f in functions if not f.get("cross_file")]
    if len(local_functions) != 1:
        names = ", ".join(
            func.get("func_name", func.get("function")) for func in local_functions
        )
        raise ValueError(
            "Function name is required for multi-function files. "
            f"Available functions: {names}"
        )
    return local_functions[0]


def _extract_function_source(file_path: str, func_name: str) -> str:
    with open(file_path, "r", encoding="utf-8") as f:
        content = f.read()

    matches = re.finditer(rf"\b{re.escape(func_name)}\s*\(", content)
    for match in matches:
        depth = 0
        for ch in content[:match.start()]:
            if ch == "{":
                depth += 1
            elif ch == "}":
                depth -= 1
        if depth != 0:
            continue

        brace_start = content.find("{", match.end())
        if brace_start == -1:
            continue

        semicolon = content.find(";", match.end())
        if semicolon != -1 and semicolon < brace_start:
            continue

        start = content.rfind("\n", 0, match.start())
        start = 0 if start == -1 else start + 1
        break
    else:
        raise ValueError(f"Could not find function signature for '{func_name}' in {file_path}")

    depth = 0
    end = None
    for idx in range(brace_start, len(content)):
        ch = content[idx]
        if ch == "{":
            depth += 1
        elif ch == "}":
            depth -= 1
            if depth == 0:
                end = idx + 1
                break

    if end is None:
        raise ValueError(f"Could not find function body end for '{func_name}' in {file_path}")

    return _normalize_block(content[start:end])


def _infer_predicate_family(*texts: str) -> Optional[str]:
    predicate_order = ["sllseg", "dllseg", "lseg", "sll", "dll", "store_tree", "tree"]
    for predicate in predicate_order:
        needle = predicate + "("
        if any(needle in text for text in texts if text):
            return predicate
    return None


def _has_segment_predicate(*texts: str) -> bool:
    return any(
        token in text
        for token in ("sllseg(", "dllseg(", "lseg(")
        for text in texts
        if text
    )


def _strip_c_comments(text: str) -> str:
    text = re.sub(r"/\*.*?\*/", "", text, flags=re.DOTALL)
    return re.sub(r"//.*", "", text)


def _extract_body_from_source(c_source: str) -> str:
    brace_start = c_source.find("{")
    brace_end = c_source.rfind("}")
    if brace_start == -1 or brace_end == -1 or brace_end <= brace_start:
        return ""
    return c_source[brace_start + 1:brace_end]


def _collect_calls_for_source(c_source: str, function_names: List[str]) -> List[str]:
    body = _strip_c_comments(_extract_body_from_source(c_source))
    calls = []
    for name in function_names:
        if re.search(rf"\b{re.escape(name)}\s*\(", body):
            calls.append(name)
    return calls


def _collect_call_sites(c_source: str, callee_name: str) -> List[str]:
    body = _strip_c_comments(_extract_body_from_source(c_source))
    call_sites = []
    for line in body.splitlines():
        stripped = line.strip()
        if re.search(rf"\b{re.escape(callee_name)}\s*\(", stripped):
            call_sites.append(stripped)
    return call_sites


def _build_low_level_spec(funcspec: Dict, program: str) -> Dict:
    processed = process_funcspec_with_safeexec(funcspec, program) if funcspec else {}
    return {
        "with_clause": processed.get("with", {}).get("translated", ""),
        "require": processed.get("require", {}).get("with_safeexec", ""),
        "ensure": processed.get("ensure", {}).get("with_safeexec", ""),
    }


def _build_m_signature(info: Dict) -> str:
    require_types = _require_var_types(info, "require_var_types", "require_var_count")
    ensure_types = _require_var_types(info, "ensure_var_types", "ensure_var_count")
    return f"{_curried_type(require_types)}MONAD ({_return_type_from_types(ensure_types)})"


def _build_control_flow_template(
    func_name: str,
    require_types: List[str],
    inv_types: List[str],
    return_type: str,
    has_pre_loop_early_return: bool,
    has_loop_body_early_return: bool,
    guard_available: bool = True,
    loop_condition: str = "",
) -> Dict:
    state_type = _tuple_type(inv_types)
    state_arg = _type_arg(state_type)
    req_args = _curried_type(require_types)
    inv_args = _curried_type(inv_types)
    loop_ret_type = f"early_result MretTy ({return_type})" if has_loop_body_early_return else "MretTy"
    loop_before_type = (
        f"{req_args}MONAD (early_result {state_arg} ({return_type}))"
        if has_pre_loop_early_return
        else f"{req_args}MONAD {state_arg}"
    )
    loop_body_type = (
        f"{state_type} -> MONAD (CntOrBrk {state_arg} (early_result MretTy ({return_type})))"
        if has_loop_body_early_return
        else f"{state_type} -> MONAD (CntOrBrk {state_arg} MretTy)"
    )
    loop_type = f"{inv_args}program unit ({loop_ret_type})"
    after_loop_type = (
        f"early_result MretTy ({return_type}) -> MONAD ({return_type})"
        if has_loop_body_early_return
        else ""
    )
    loop_end_type = f"MretTy -> MONAD ({return_type})"
    top_level_type = f"{req_args}MONAD ({return_type})"

    after_loop_definition = ""
    if has_loop_body_early_return:
        after_loop_definition = "\n".join([
            f"Definition {func_name}_M_after_loop : early_result MretTy ({return_type}) -> MONAD ({return_type}) :=",
            "  fun re =>",
            "    match re with",
            f"    | Continue r => {func_name}_M_loop_end r",
            "    | ReturnNow r => return r",
            "    end.",
        ])

    if has_loop_body_early_return:
        loop_body_definition = "\n".join([
            f"Definition {func_name}_M_loop_body : {loop_body_type} :=",
            "  fun a =>",
            f"    choice (assume!! (~ ({func_name}_guardP a));; r <- {func_name}_M_loop_M1 a ;; break (Continue r))",
            f"           (assume!! (({func_name}_guardP a));;",
            f"            a' <- {func_name}_M_loop_M2 a ;;",
            "            match a' with",
            "            | Continue a'' => continue a''",
            "            | ReturnNow r' => break (ReturnNow r')",
            "            end).",
        ])
    else:
        loop_body_definition = "\n".join([
            f"Definition {func_name}_M_loop_body : {loop_body_type} :=",
            "  fun a =>",
            f"    choice (assume!! (~ ({func_name}_guardP a));; r <- {func_name}_M_loop_M1 a ;; break r)",
            f"           (assume!! (({func_name}_guardP a));; a' <- {func_name}_M_loop_M2 a ;; continue a').",
        ])

    if not has_pre_loop_early_return and not has_loop_body_early_return:
        top_level_definition = "\n".join([
            f"Definition {func_name}_M : {top_level_type} :=",
            "  fun ... =>",
            f"    s0 <- {func_name}_M_loop_before ...;;",
            f"    r <- {func_name}_M_loop s0;;",
            f"    {func_name}_M_loop_end r.",
        ])
    elif has_pre_loop_early_return and not has_loop_body_early_return:
        top_level_definition = "\n".join([
            f"Definition {func_name}_M : {top_level_type} :=",
            "  fun ... =>",
            f"    e <- {func_name}_M_loop_before ...;;",
            "    match e with",
            "    | Continue s =>",
            f"        r <- {func_name}_M_loop s;;",
            f"        {func_name}_M_loop_end r",
            "    | ReturnNow r =>",
            "        return r",
            "    end.",
        ])
    elif not has_pre_loop_early_return and has_loop_body_early_return:
        top_level_definition = "\n".join([
            f"Definition {func_name}_M : {top_level_type} :=",
            "  fun ... =>",
            f"    s0 <- {func_name}_M_loop_before ...;;",
            f"    re <- {func_name}_M_loop s0;;",
            f"    {func_name}_M_after_loop re.",
        ])
    else:
        top_level_definition = "\n".join([
            f"Definition {func_name}_M : {top_level_type} :=",
            "  fun ... =>",
            f"    e <- {func_name}_M_loop_before ...;;",
            "    match e with",
            "    | Continue s =>",
            f"        re <- {func_name}_M_loop s;;",
            f"        {func_name}_M_after_loop re",
            "    | ReturnNow r =>",
            "        return r",
            "    end.",
        ])

    m1_type = f"{state_type} -> MONAD MretTy"
    m2_type = (
        f"{state_type} -> MONAD (early_result {state_arg} ({return_type}))"
        if has_loop_body_early_return
        else f"{state_type} -> MONAD {state_arg}"
    )
    guard_type = f"{state_type} -> Prop"

    prompt_signatures = {
        "M_loop_before": loop_before_type,
        "M_loop_body": loop_body_type,
        "M_loop": loop_type,
        "M_loop_M1": m1_type,
        "M_loop_M2": m2_type,
        "M_loop_end": loop_end_type,
        "M_after_loop": after_loop_type,
        "M": top_level_type,
    }

    # When GuardGen could not produce a concrete guard, the skeleton emits a
    # `Parameter {fn}_guardP` placeholder.  Ask the LLM to fill it in, but pin
    # its signature so downstream scaffolding (M_loop_body) keeps type-checking.
    required_components = ["MretTy", "M_loop_before", "M_1", "M_2", "M_loop_end"]
    if not guard_available:
        required_components.append("guardP")
        prompt_signatures["guardP"] = guard_type

    return {
        "template_case": (
            "both"
            if has_pre_loop_early_return and has_loop_body_early_return
            else "pre_loop"
            if has_pre_loop_early_return
            else "loop_body"
            if has_loop_body_early_return
            else "none"
        ),
        "has_pre_loop_early_return": has_pre_loop_early_return,
        "has_loop_body_early_return": has_loop_body_early_return,
        "has_no_loop_early_return": False,
        "needs_early_result": has_pre_loop_early_return or has_loop_body_early_return,
        "state_type": state_type,
        "return_type": return_type,
        "prompt_signatures": prompt_signatures,
        # Component keys the LLM must supply; consumed by parser, assembler,
        # and prompt rendering.
        "required_components": required_components,
        "guard_available": guard_available,
        "guard_signature": guard_type,
        "loop_condition": loop_condition,
        "template": {
            "loop_body_definition": loop_body_definition,
            "top_level": top_level_definition,
            "after_loop_definition": after_loop_definition,
        },
    }


def _build_no_loop_control_flow_template(
    func_name: str,
    require_types: List[str],
    return_type: str,
    has_early_return: bool,
) -> Dict:
    """Build the control-flow template for a function with no loop.

    Two shapes:
    - has_early_return=True  -> split scaffold (`M_before` + `M_normal`).
    - has_early_return=False -> single opaque ``Parameter M`` (no MretTy).
    """
    req_args = _curried_type(require_types)

    if has_early_return:
        before_type = f"{req_args}MONAD (early_result MretTy ({return_type}))"
        normal_type = f"MretTy -> MONAD ({return_type})"
        top_level_type = f"{req_args}MONAD ({return_type})"
        top_level_definition = "\n".join([
            f"Definition {func_name}_M : {top_level_type} :=",
            "  fun ... =>",
            f"    e <- {func_name}_M_before ...;;",
            "    match e with",
            f"    | Continue s => {func_name}_M_normal s",
            "    | ReturnNow r => return r",
            "    end.",
        ])
        prompt_signatures = {
            "M_before": before_type,
            "M_normal": normal_type,
            "M": top_level_type,
        }
        return {
            "template_case": "no_loop_early_return",
            "has_pre_loop_early_return": False,
            "has_loop_body_early_return": False,
            "has_no_loop_early_return": True,
            "needs_early_result": True,
            "state_type": "",
            "return_type": return_type,
            "prompt_signatures": prompt_signatures,
            "required_components": ["MretTy", "M_before", "M_normal"],
            "template": {
                "loop_body_definition": "",
                "top_level": top_level_definition,
                "after_loop_definition": "",
            },
        }

    # Straight-line: just one opaque ``Parameter {fn}_M``.
    top_level_type = f"{req_args}MONAD ({return_type})"
    prompt_signatures = {"M": top_level_type}
    return {
        "template_case": "no_loop_simple",
        "has_pre_loop_early_return": False,
        "has_loop_body_early_return": False,
        "has_no_loop_early_return": False,
        "needs_early_result": False,
        "state_type": "",
        "return_type": return_type,
        "prompt_signatures": prompt_signatures,
        "required_components": ["M"],
        "template": {
            "loop_body_definition": "",
            "top_level": "",
            "after_loop_definition": "",
        },
    }


def _build_loop_templates(
    func_name: str,
    c_source: str,
    inv_assertions: List[Dict],
) -> List[Dict]:
    """Per-loop control-flow descriptors — thin wrapper over the canonical
    :func:`loop_forest.build_loop_templates` so context.py callers keep the
    historical entry-point name while consolidating the implementation."""
    return build_loop_templates(func_name, c_source, inv_assertions)


def _attach_per_loop_safeexec(func_name: str, loop_templates: List[Dict]) -> None:
    """Populate each template's ``loop_invariant_with_safeexec`` field — the
    translated invariant wrapped in
    ``safeExec(ATrue, bind(<M_loop{k}>(...), <M_loop{root}_end>), X)``.

    Single-loop functions use the legacy unsuffixed names
    (``{fn}_M_loop`` / ``{fn}_M_loop_end``); multi-loop functions use the
    forest per-loop / per-root names that match ``_rel.c`` and the lib.
    """
    if not loop_templates:
        return
    by_idx = {t["loop_index"]: t for t in loop_templates}

    def _root(loop_idx: int) -> int:
        cur = loop_idx
        while by_idx[cur]["parent"] is not None:
            cur = by_idx[cur]["parent"]
        return cur

    forest_mode = len(loop_templates) > 1
    for t in loop_templates:
        k = t["loop_index"] + 1
        root_k = _root(t["loop_index"]) + 1
        if forest_mode:
            program_loop = f"{func_name}_M_loop{k}"
            program_end = f"{func_name}_M_loop{root_k}_end"
        else:
            program_loop = f"{func_name}_M_loop"
            program_end = f"{func_name}_M_loop_end"
        translated = t.get("loop_invariant_translated", "")
        if not translated:
            t["loop_invariant_with_safeexec"] = ""
            continue
        t["loop_invariant_with_safeexec"] = add_safeexec_predicate(
            translated, t.get("inv_variables", []), program_loop, program_end,
        )


def _forest_required_components(
    func_name: str,
    require_types: List[str],
    return_type: str,
    loop_templates: List[Dict],
) -> tuple:
    """Compute the LLM-required component list + per-component Coq
    signatures for the forest scaffold (task #22).

    Mirrors the structure emitted by
    :func:`gen_rel_lib.generate_forest_func_block` so every Parameter the
    skeleton leaves open is paired with a required Definition the LLM must
    supply (and its expected type).  Component keys are the suffix portion
    (without ``{func_name}_``); :func:`parse_coq._component_parameter_name`
    re-prefixes them when extracting Definitions from the response.
    """
    if not loop_templates:
        return [], {}

    by_idx = {t["loop_index"]: t for t in loop_templates}
    top_levels = sorted(
        (t for t in loop_templates if t["parent"] is None),
        key=lambda t: t["loop_index"],
    )

    required: List[str] = ["MretTy"]
    sigs: Dict[str, str] = {"MretTy": "Type"}

    # Intermediate result types between sequential top-level loops.
    res_ty_for: Dict[int, str] = {}
    if len(top_levels) > 1:
        for t in top_levels[:-1]:
            k = t["loop_index"] + 1
            name = f"loop{k}_ResTy"
            required.append(name)
            sigs[name] = "Type"
            res_ty_for[t["loop_index"]] = f"{func_name}_loop{k}_ResTy"

    for t in loop_templates:
        k = t["loop_index"] + 1
        Sk = t["state_type"]
        Sk_arg = _type_arg(Sk)

        if not t.get("guard_available"):
            name = f"loop{k}_guardP"
            required.append(name)
            sigs[name] = f"{Sk} -> Prop"

        m1 = f"M_loop{k}_M1"
        required.append(m1)
        sigs[m1] = f"{Sk} -> MONAD MretTy"

        if not t.get("children"):
            m2 = f"M_loop{k}_M2"
            required.append(m2)
            sigs[m2] = f"{Sk} -> MONAD {Sk_arg}"
        else:
            for c_idx in t["children"]:
                ck = c_idx + 1
                Sc_arg = _type_arg(by_idx[c_idx]["state_type"])
                ti = f"M_loop{k}_to_inner_{ck}"
                required.append(ti)
                sigs[ti] = f"{Sk} -> MONAD {Sc_arg}"
                ai = f"M_loop{k}_after_inner_{ck}"
                required.append(ai)
                sigs[ai] = f"{Sk} -> MretTy -> MONAD {Sk_arg}"

    req_curried = _curried_type(require_types) if require_types else ""
    for i, t in enumerate(top_levels):
        k = t["loop_index"] + 1
        Sk_arg = _type_arg(t["state_type"])
        before = f"M_loop{k}_before"
        required.append(before)
        if i == 0:
            sigs[before] = f"{req_curried}MONAD {Sk_arg}"
        else:
            prev_res = res_ty_for[top_levels[i - 1]["loop_index"]]
            sigs[before] = f"{prev_res} -> MONAD {Sk_arg}"

    for i, t in enumerate(top_levels):
        k = t["loop_index"] + 1
        end = f"M_loop{k}_end"
        required.append(end)
        if i == len(top_levels) - 1:
            sigs[end] = f"MretTy -> MONAD ({return_type})"
        else:
            res = res_ty_for[t["loop_index"]]
            sigs[end] = f"MretTy -> MONAD {res}"

    return required, sigs


def _scoped_mretty_name(fn: str, manifest: Dict) -> str:
    """Return the actual ``MretTy`` Parameter name the skeleton emits for *fn*.

    Mirrors ``gen_rel_lib.generate_rel_lib``: when two or more functions in
    the file need a ``MretTy``, the skeleton scopes the name per-function as
    ``{fn}_MretTy`` to avoid collisions; otherwise the shared bare ``MretTy``
    is used.  The synthesis prompt's must_define list — and therefore the
    workdir validator — has to use the same name.

    Defensive: a manifest without function-list info collapses to bare
    ``MretTy``, matching the legacy single-function behaviour.

    Cross-file sibling entries (``cross_file=True``) are excluded from the
    count even when they themselves need a ``MretTy``.  Each cross-file lib
    is generated independently and makes its own scoping decision based on
    its own in-file function set; counting them here would diverge from
    ``generate_rel_lib``'s in-file-only logic and yield a ``must_define``
    name the skeleton doesn't actually emit.
    """
    funcs = manifest.get("functions") or []
    users = sum(
        1 for entry in funcs
        if not entry.get("cross_file", False) and needs_mretty(entry)
    )
    return f"{fn}_MretTy" if users > 1 else "MretTy"


def _loop_forest_summary(loop_templates: List[Dict]) -> List[Dict]:
    """Minimal topology view (just what callers need for prompt / codegen)."""
    return [
        {
            "loop_index": t["loop_index"],
            "parent": t["parent"],
            "children": list(t["children"]),
            "keyword": t["keyword"],
            "inv_index": t["inv_index"],
        }
        for t in loop_templates
    ]


def _collect_extern_info(func_data: Dict, include_helpers: bool = False) -> Optional[Dict]:
    try:
        return collect_func_extern_info(func_data, include_helpers=include_helpers)
    except TypeError:
        return collect_func_extern_info(func_data)


def _build_target_details(c_file: str, result: Dict, func_data: Dict) -> Dict:
    # Loop-less functions still produce an extern info dict when we pass
    # ``include_helpers=True``; that lets us synthesize an abstract program
    # for them (full opaque ``Parameter M`` or the Option-C split scaffold).
    info = _collect_extern_info(func_data, include_helpers=True)
    if info is None:
        raise ValueError(f"Function '{func_data['function']}' has no funcspec")

    funcspec = func_data.get("funcspec") or {}
    inv_assertions = [a for a in func_data.get("inner_assertions", []) if a.get("type") == "Inv"]
    first_inv = inv_assertions[0] if inv_assertions else {}
    program = f"{func_data['function']}_M"
    if funcspec:
        try:
            processed_funcspec = process_funcspec_with_safeexec(
                funcspec, program, return_type=func_data.get("return_type", "")
            )
        except TypeError:
            # Older callers / tests that monkeypatch with a 2-arg signature.
            processed_funcspec = process_funcspec_with_safeexec(funcspec, program)
    else:
        processed_funcspec = {}
    c_source = _extract_function_source(c_file, func_data["function"])

    has_loop_program = bool(inv_assertions)

    require_types = _require_var_types(info, "require_var_types", "require_var_count")
    inv_types = _require_var_types(info, "inv_var_types", "inv_var_count")
    ensure_types = _require_var_types(info, "ensure_var_types", "ensure_var_count")
    state_type = _tuple_type(inv_types) if inv_types else ""
    return_type = _return_type_from_types(ensure_types)
    early_return_shape = detect_early_return_shape(c_source)
    has_pre_loop_early_return = early_return_shape["has_pre_loop_early_return"]
    has_loop_body_early_return = early_return_shape["has_loop_body_early_return"]
    has_no_loop_early_return = early_return_shape.get("has_no_loop_early_return", False)

    # Self-recursive Option-C functions can't use the split scaffold: the
    # synthesized `M_normal` would need to call the entry-point `M` which is
    # defined further down in the lib, producing an unresolved reference.
    # Fall back to a single opaque `Parameter {fn}_M` so the LLM provides a
    # `Definition {fn}_M := ...` that can recurse via its own name.
    is_recursive = False
    try:
        with open(c_file, "r", encoding="utf-8") as f:
            file_content = f.read()
        body = _extract_function_body(file_content, func_data["function"])
        if body and re.search(
            rf"\b{re.escape(func_data['function'])}\s*\(", body
        ):
            is_recursive = True
    except (OSError, ValueError):
        pass

    if has_loop_program:
        control_flow = _build_control_flow_template(
            func_data["function"],
            require_types,
            inv_types,
            return_type,
            has_pre_loop_early_return,
            has_loop_body_early_return,
            guard_available=bool(first_inv.get("coq_guard")),
            loop_condition=first_inv.get("command_guard", ""),
        )
    else:
        effective_early_return = has_no_loop_early_return and not is_recursive
        control_flow = _build_no_loop_control_flow_template(
            func_data["function"],
            require_types,
            return_type,
            has_early_return=effective_early_return,
        )

    control_flow["has_top_level_loop"] = early_return_shape["has_top_level_loop"]
    control_flow["has_top_level_loop"] = early_return_shape["has_top_level_loop"]

    # Per-loop templates (one entry per `while` / `for` discovered in the
    # function body) — replaces the single-first_inv assumption for the
    # downstream nested-loop codegen.  For single-loop functions this list
    # has exactly one entry and the legacy `control_flow` block above stays
    # the source of truth.
    loop_templates = _build_loop_templates(
        func_data["function"], c_source, inv_assertions
    )
    # Per-loop safeExec-wrapped invariants: each loop's residual program uses
    # its OWN ``_M_loop{k}`` and its root ancestor's ``_M_loop{root_k}_end``
    # (mirrors what ``translate_c_file._build_per_inv_programs`` produces for
    # the ``_rel.c`` annotations).  Single-loop functions get the legacy
    # single-name pair, so the prompt-rendered invariant stays identical.
    if loop_templates:
        _attach_per_loop_safeexec(func_data["function"], loop_templates)
    control_flow["loop_templates"] = loop_templates
    control_flow["loop_forest"] = _loop_forest_summary(loop_templates)
    control_flow["has_nested_loops"] = any(
        t["parent"] is not None for t in loop_templates
    )
    control_flow["has_sequential_loops"] = (
        sum(1 for t in loop_templates if t["parent"] is None) > 1
    )

    # Block-tree-derived C ↔ scaffold-hole binding for the prompt.
    # Stored under ``prompt_context["scaffold_segments"]`` so the lib
    # ``.v`` stays a clean Coq template; the binding is synthesis-time
    # guidance only.  Each scaffold shape gets its own hole-name set:
    #
    #   * no-loop-early-return  → {"M_before", "M_normal"}
    #   * single-loop scaffold  → {"M_loop_before", "M_loop_M2",
    #                              "M_loop_end"}  (M_loop_M1 is
    #                              mechanical; no C segment)
    #
    # Multi-loop ``loop_forest`` libs aren't covered yet — they need a
    # per-loop binding that respects nesting.
    scaffold_segments: Dict[str, str] = {}
    if c_source:
        from GenMonads.absprog.partition import (
            partition_function_body,
            render_blocks_as_c_snippet,
            split_for_interleaved_early_return,
            split_for_loop_forest,
            split_for_loop_scaffold,
            split_for_no_loop_early_return,
        )
        try:
            blocks = partition_function_body(c_source)
        except Exception:
            blocks = None

        if blocks is not None:
            # Phase 3C — interleaved early-returns take precedence over
            # the single-decision no-loop-early-return scaffold when 2+
            # top-level decisions exist.
            interleaved = split_for_interleaved_early_return(blocks)
            if interleaved is not None and not has_loop_program and not is_recursive:
                # Insert in execution-narrative order: decision_1 → phase_1
                # → decision_2 → phase_2 → … → decision_N → M_final.
                # The prompt renderer preserves insertion order for
                # non-static keys, so this becomes the displayed order.
                decisions = interleaved["decisions"]
                phases = interleaved["phases"]
                for k, dec in enumerate(decisions, start=1):
                    scaffold_segments[f"M_decision_{k}"] = dec.raw_c_text
                    phase_blocks = phases[k - 1]   # work after decision k's Continue
                    snippet = render_blocks_as_c_snippet(phase_blocks)
                    if k < len(decisions):
                        scaffold_segments[f"M_phase_{k}"] = snippet
                    else:
                        # Terminal phase after the last decision.
                        scaffold_segments["M_final"] = snippet
            elif not has_loop_program and has_no_loop_early_return and not is_recursive:
                split = split_for_no_loop_early_return(blocks)
                if split is not None:
                    scaffold_segments = {
                        "M_before": render_blocks_as_c_snippet(split["m_before"]),
                        "M_normal": render_blocks_as_c_snippet(split["m_normal"]),
                    }
            elif has_loop_program and len(loop_templates) == 1:
                split = split_for_loop_scaffold(blocks)
                if split is not None:
                    scaffold_segments = {
                        "M_loop_before": render_blocks_as_c_snippet(split["M_loop_before"]),
                        "M_loop_M2": render_blocks_as_c_snippet(split["M_loop_M2"]),
                        "M_loop_end": render_blocks_as_c_snippet(split["M_loop_end"]),
                    }
                    # Phase 3B — when the loop body has an internal
                    # early-return, surface the sub-structure so the
                    # agent encodes ``early_result`` wrapping in M_loop_M2.
                    if "M_loop_M2_split" in split:
                        m2 = split["M_loop_M2_split"]
                        scaffold_segments["_M_loop_M2_pre_decision"] = (
                            render_blocks_as_c_snippet(m2["pre_decision"])
                        )
                        scaffold_segments["_M_loop_M2_decision"] = m2["decision"].raw_c_text
                        scaffold_segments["_M_loop_M2_decision_cond"] = m2["decision"].cond
                        scaffold_segments["_M_loop_M2_post_decision"] = (
                            render_blocks_as_c_snippet(m2["post_decision"])
                        )
            elif has_loop_program and len(loop_templates) > 1:
                # Multi-loop (forest) functions: per-loop segments keyed
                # by the existing forest scaffold's hole names
                # (M_loop{k}_before, M_loop{k}_M2 for leaves,
                # M_loop{k}_to_inner_{j}/_after_inner_{j} for parents,
                # M_loop{k}_end for top-level).
                forest_segs = split_for_loop_forest(blocks)
                if forest_segs is not None:
                    scaffold_segments = dict(forest_segs)

    # When the function has >1 loops the forest scaffold takes over: override
    # the LLM's required_components and prompt_signatures with per-loop holes.
    if len(loop_templates) > 1:
        forest_required, forest_sigs = _forest_required_components(
            func_data["function"], require_types, return_type, loop_templates,
        )
        control_flow["required_components"] = forest_required
        control_flow["prompt_signatures"] = forest_sigs
        control_flow["template_case"] = "forest"

    require_translated = funcspec.get("require", {}).get("translated", "")
    ensure_translated = funcspec.get("ensure", {}).get("translated", "")
    loop_invariant_translated = first_inv.get("translated", "")

    loop_invariant_with_safeexec = ""
    if first_inv.get("translated"):
        loop_end_program = (
            f"{func_data['function']}_M_after_loop"
            if has_loop_body_early_return
            else f"{func_data['function']}_M_loop_end"
        )
        loop_invariant_with_safeexec = add_safeexec_predicate(
            first_inv["translated"],
            first_inv.get("variables", []),
            f"{func_data['function']}_M_loop",
            loop_end_program,
        )

    return {
        "predicate_family": _infer_predicate_family(
            require_translated,
            ensure_translated,
            loop_invariant_translated,
        ),
        "summary": {
            "func_name": func_data["function"],
        },
        "features": {
            "loop_count": len(inv_assertions),
            "require_var_count": info["require_var_count"],
            "inv_var_count": info["inv_var_count"],
            "ensure_var_count": info.get("ensure_var_count", 1),
            "has_seg_predicate": _has_segment_predicate(
                require_translated,
                ensure_translated,
                loop_invariant_translated,
            ),
            "has_multi_return": info.get("ensure_var_count", 1) > 1,
        },
        "prompt_context": {
            "c_source": c_source,
            "with_clause": processed_funcspec.get("with", {}).get("translated", ""),
            "require_with_safeexec": processed_funcspec.get("require", {}).get("with_safeexec", ""),
            "ensure_with_safeexec": processed_funcspec.get("ensure", {}).get("with_safeexec", ""),
            "loop_invariant_with_safeexec": loop_invariant_with_safeexec,
            "loop_condition": first_inv.get("command_guard", ""),
            "guard_coq": first_inv.get("coq_guard", ""),
            "control_flow": control_flow,
            "scaffold_segments": scaffold_segments,
        },
        "signatures": {
            "M_loop_before": f"{_curried_type(require_types)}MONAD {_type_arg(state_type)}",
            "M_1": f"{state_type} -> MONAD MretTy",
            "M_2": f"{state_type} -> MONAD {_type_arg(state_type)}",
            "M_loop_end": f"MretTy -> MONAD ({return_type})",
            "M": f"{_curried_type(require_types)}MONAD ({return_type})",
        },
        "control_flow": control_flow,
        "loop_templates": loop_templates,
        "loop_forest": _loop_forest_summary(loop_templates),
    }


_IDENT_CALL_RE = re.compile(r"\b([A-Za-z_][A-Za-z0-9_]*)\s*\(")

_C_KEYWORDS_AND_BUILTINS = {
    "if", "else", "for", "while", "do", "switch", "case", "default",
    "return", "break", "continue", "goto", "sizeof", "typedef",
    "struct", "union", "enum", "static", "extern", "const", "volatile",
    "register", "auto", "inline", "void", "char", "short", "int",
    "long", "float", "double", "signed", "unsigned", "_Bool",
    "malloc", "free", "calloc", "realloc", "memcpy", "memset",
    "printf", "fprintf", "scanf", "assert",
}


def _candidate_callees_in_source(source: str) -> set[str]:
    body = _strip_c_comments(_extract_body_from_source(source))
    return {match.group(1) for match in _IDENT_CALL_RE.finditer(body)}


def _collect_sibling_manifest_entries(
    c_file: str,
    candidate_names: set[str],
    sibling_dirs: Optional[List[str]] = None,
) -> List[Dict]:
    """For each name in ``candidate_names``, if ``{name}.c`` exists as a
    sibling in one of the search directories, parse it and return a manifest
    entry tagged ``cross_file=True``.  Returns [] if no candidates resolve.

    Search directories default to ``[dirname(c_file)]``; when
    ``sibling_dirs`` is provided, those replace the default.
    """
    if not candidate_names:
        return []
    if sibling_dirs:
        search_dirs = [os.path.abspath(d) for d in sibling_dirs]
    else:
        search_dirs = [os.path.dirname(os.path.abspath(c_file))]
    own_stem = os.path.splitext(os.path.basename(c_file))[0]
    entries: List[Dict] = []
    seen: set[str] = set()
    for name in sorted(candidate_names):
        if name == own_stem or name in seen:
            continue
        sibling_path = None
        for d in search_dirs:
            candidate = os.path.join(d, f"{name}.c")
            if os.path.isfile(candidate):
                sibling_path = candidate
                break
        if sibling_path is None:
            continue
        try:
            sibling_result = process_and_translate_file(sibling_path, generate_guards=False)
        except Exception:
            continue
        if isinstance(sibling_result, dict) and "error" in sibling_result:
            continue
        for func_data in _collect_functions(sibling_result):
            fn_name = func_data.get("function")
            if not fn_name or fn_name not in candidate_names or fn_name in seen:
                continue
            seen.add(fn_name)
            helper_info = _collect_extern_info(
                func_data,
                include_helpers=func_data.get("funcspec") is not None,
            )
            externals = {}
            if helper_info is not None:
                externals["M"] = _build_m_signature(helper_info)
            sibling_has_loop = _collect_extern_info(func_data) is not None
            sibling_entry = {
                "func_name": fn_name,
                "has_body": True,
                "has_loop_invariants": sibling_has_loop,
                "has_loop_program": sibling_has_loop,
                # Sibling functions live in another file — we don't carry
                # their early-return classification across, which only
                # matters for the file-local mretty-scoping decision.
                "has_no_loop_early_return": False,
                "is_recursive": False,
                "called_by": [],
                "calls": [],
                "should_synthesize": False,
                "cross_file": True,
                "defined_in": sibling_path,
                "externals": externals,
            }
            if func_data.get("funcspec"):
                sibling_entry["spec"] = _build_low_level_spec(
                    func_data["funcspec"], f"{fn_name}_M"
                )
            entries.append(sibling_entry)
    return entries


def _build_file_manifest_from_result(
    c_file: str,
    result: Dict,
    sibling_dirs: Optional[List[str]] = None,
) -> Dict:
    if "error" in result:
        raise ValueError(result["error"])

    functions = _collect_functions(result)
    function_names = [func_data["function"] for func_data in functions]
    function_sources: Dict[str, str] = {}
    for name in function_names:
        try:
            function_sources[name] = _extract_function_source(c_file, name)
        except (ValueError, OSError):
            continue

    unresolved_candidates: set[str] = set()
    for source in function_sources.values():
        unresolved_candidates |= _candidate_callees_in_source(source)
    unresolved_candidates -= set(function_names)
    unresolved_candidates -= _C_KEYWORDS_AND_BUILTINS
    sibling_entries = _collect_sibling_manifest_entries(
        c_file, unresolved_candidates, sibling_dirs=sibling_dirs
    )
    sibling_names = [entry["func_name"] for entry in sibling_entries]
    callable_names = function_names + sibling_names

    call_graph: Dict[str, List[str]] = {}
    call_sites: Dict[str, Dict[str, List[str]]] = {}
    for name, source in function_sources.items():
        calls = _collect_calls_for_source(source, callable_names)
        call_graph[name] = sorted(calls)
        call_sites[name] = {
            callee: _collect_call_sites(source, callee)
            for callee in calls
        }

    called_by: Dict[str, List[str]] = {name: [] for name in function_names}
    for caller, callees in call_graph.items():
        for callee in callees:
            called_by.setdefault(callee, []).append(caller)

    manifest_functions = []
    targets = []
    for func_data in functions:
        func_name = func_data["function"]
        has_body = func_name in function_sources
        info = _collect_extern_info(func_data)
        has_loop_invariants = info is not None
        # A function is synthesizable if it has a body and a funcspec; loop
        # invariants are required for loop-bearing functions but not for
        # straight-line / early-return-only functions (Option C scaffolds).
        has_funcspec = func_data.get("funcspec") is not None
        should_synthesize = has_body and has_funcspec
        if should_synthesize:
            targets.append(func_name)

        helper_info = _collect_extern_info(
            func_data,
            include_helpers=func_data.get("funcspec") is not None,
        )
        externals = {}
        if helper_info is not None:
            externals["M"] = _build_m_signature(helper_info)

        # Flags driving the file-wide MretTy-scoping decision (shared with
        # gen_rel_lib via :func:`needs_mretty`).  We compute them eagerly
        # here — for helpers/cross-file decls we still know whether the
        # function has invariants AND whether its body (if available)
        # carries a no-loop early-return shape.
        entry_has_loop_program = has_loop_invariants
        entry_has_no_loop_early_return = False
        if has_body and not entry_has_loop_program:
            try:
                shape = detect_early_return_shape(function_sources[func_name])
                entry_has_no_loop_early_return = shape.get(
                    "has_no_loop_early_return", False
                )
            except (KeyError, ValueError):
                pass

        entry = {
            "func_name": func_name,
            "has_body": has_body,
            "has_loop_invariants": has_loop_invariants,
            "has_loop_program": entry_has_loop_program,
            "has_no_loop_early_return": entry_has_no_loop_early_return,
            "is_recursive": func_name in call_graph.get(func_name, []),
            "called_by": sorted(called_by.get(func_name, [])),
            "calls": call_graph.get(func_name, []),
            "should_synthesize": should_synthesize,
            "externals": externals,
        }

        if func_data.get("funcspec"):
            entry["spec"] = _build_low_level_spec(func_data["funcspec"], f"{func_name}_M")

        if should_synthesize:
            target_details = _build_target_details(c_file, result, func_data)
            entry["predicate_family"] = target_details["predicate_family"]
            entry["summary"] = target_details["summary"]
            entry["features"] = target_details["features"]
            entry["prompt_context"] = target_details["prompt_context"]
            entry["signatures"] = target_details["signatures"]
            entry["control_flow"] = target_details["control_flow"]
            entry["c_source"] = target_details["prompt_context"]["c_source"]

        if call_sites.get(func_name):
            entry["call_sites"] = call_sites[func_name]

        manifest_functions.append(entry)

    for sibling in sibling_entries:
        manifest_functions.append(sibling)

    return {
        "file_id": os.path.splitext(os.path.basename(c_file))[0],
        "version": 2,
        "source": {
            "c_file": c_file,
        },
        "functions": manifest_functions,
        "targets": targets,
    }


def collect_file_synthesis_manifest(
    c_file: str,
    sibling_dirs: Optional[List[str]] = None,
) -> Dict:
    result = process_and_translate_file(c_file, generate_guards=True)
    return _build_file_manifest_from_result(c_file, result, sibling_dirs=sibling_dirs)


def _context_from_manifest(manifest: Dict, result: Dict, func_name: Optional[str] = None) -> Dict:
    func_entry = _select_function(manifest["functions"], func_name, manifest["source"]["c_file"])
    if not func_entry["should_synthesize"]:
        raise ValueError(f"Function '{func_entry['func_name']}' has no funcspec to synthesize")

    available_callees = []
    for callee_name in func_entry.get("calls", []):
        callee_entry = next(
            (entry for entry in manifest["functions"] if entry["func_name"] == callee_name),
            None,
        )
        if callee_entry is None:
            continue
        opaque_program = callee_name + "_M"
        # Include the C body of the callee when it's available so the LLM
        # can match the call's semantics — not just its signature.  Bodies
        # are only included when ``has_body`` is set AND we can locate the
        # source: same-file callees use ``manifest["source"]["c_file"]``;
        # cross-file callees use ``defined_in``.  Truly external callees
        # (declaration-only, no defined_in) have no body to include —
        # we simply omit it.
        callee_c_source = None
        if callee_entry.get("has_body"):
            body_src_file = (
                callee_entry.get("defined_in")
                if callee_entry.get("cross_file")
                else manifest["source"]["c_file"]
            )
            if body_src_file:
                try:
                    callee_c_source = _extract_function_source(
                        body_src_file, callee_name
                    )
                except (ValueError, OSError):
                    callee_c_source = None
        entry = {
            "func_name": callee_name,
            "opaque_program": opaque_program,
            "has_body": callee_entry["has_body"],
            "should_synthesize_elsewhere": callee_entry["should_synthesize"],
            "externals": callee_entry.get("externals", {}),
            "spec": callee_entry.get("spec", {}),
            "call_sites": func_entry.get("call_sites", {}).get(callee_name, []),
            "cross_file": callee_entry.get("cross_file", False),
            "defined_in": callee_entry.get("defined_in"),
        }
        if callee_c_source:
            entry["c_source"] = callee_c_source
        available_callees.append(entry)

    opaque_call_obligations = []
    for callee in available_callees:
        for site in callee.get("call_sites", []):
            opaque_call_obligations.append({
                "callee": callee["opaque_program"],
                "call_site": site,
                "must_use_placeholder": True,
            })

    context_id = _make_context_id(
        manifest["source"]["c_file"],
        result,
        func_entry["func_name"],
    )
    fn = func_entry["func_name"]
    control_flow = func_entry.get("control_flow", {})
    required = control_flow.get("required_components", [
        "MretTy", "M_loop_before", "M_1", "M_2", "M_loop_end",
    ])
    mretty_name = _scoped_mretty_name(fn, manifest)
    must_define = []
    for component in required:
        if component == "MretTy":
            must_define.append(mretty_name)
        elif component == "M_1":
            must_define.append(f"{fn}_M_loop_M1")
        elif component == "M_2":
            must_define.append(f"{fn}_M_loop_M2")
        else:
            must_define.append(f"{fn}_{component}")
    generated_scaffolding = []
    if func_entry.get("control_flow", {}).get("has_loop_body_early_return"):
        generated_scaffolding.append(f"{func_entry['func_name']}_M_after_loop")

    file_overview = {
        "targets": list(manifest["targets"]),
        "functions": [
            {
                "func_name": entry["func_name"],
                "should_synthesize": entry["should_synthesize"],
                "calls": entry.get("calls", []),
                "called_by": entry.get("called_by", []),
            }
            for entry in manifest["functions"]
        ],
    }

    control_flow_dict = func_entry.get("control_flow", {})
    loop_templates = control_flow_dict.get("loop_templates", [])
    loop_forest = control_flow_dict.get("loop_forest", [])

    target = {
        "func_name": func_entry["func_name"],
        "has_body": func_entry["has_body"],
        "has_loop_invariants": func_entry["has_loop_invariants"],
        "is_recursive": func_entry["is_recursive"],
        "called_by": func_entry.get("called_by", []),
        "calls": func_entry.get("calls", []),
        "should_synthesize": True,
        "c_source": func_entry["c_source"],
        "predicate_family": func_entry["predicate_family"],
        "summary": func_entry["summary"],
        "features": func_entry["features"],
        "prompt_context": func_entry["prompt_context"],
        "signatures": func_entry["signatures"],
        "control_flow": control_flow_dict,
        "loop_templates": loop_templates,
        "loop_forest": loop_forest,
    }

    return {
        "id": context_id,
        "version": 2,
        "source": {
            "c_file": manifest["source"]["c_file"],
            "file_id": manifest["file_id"],
        },
        "file_overview": file_overview,
        "predicate_family": func_entry["predicate_family"],
        "summary": func_entry["summary"],
        "features": func_entry["features"],
        "prompt_context": func_entry["prompt_context"],
        "signatures": func_entry["signatures"],
        "control_flow": control_flow_dict,
        "loop_templates": loop_templates,
        "loop_forest": loop_forest,
        "target": target,
        "available_callees": available_callees,
        "opaque_call_obligations": opaque_call_obligations,
        "generation_policy": {
            "must_define": must_define,
            "generated_scaffolding": generated_scaffolding,
            "opaque_external_programs": [
                callee["opaque_program"]
                for callee in available_callees
                if callee.get("externals", {}).get("M")
            ],
        },
    }


def collect_synthesis_context(
    c_file: str,
    func_name: Optional[str] = None,
    sibling_dirs: Optional[List[str]] = None,
) -> Dict:
    result = process_and_translate_file(c_file, generate_guards=True)
    manifest = _build_file_manifest_from_result(c_file, result, sibling_dirs=sibling_dirs)
    return _context_from_manifest(manifest, result, func_name)


def collect_all_synthesis_contexts(
    c_file: str,
    sibling_dirs: Optional[List[str]] = None,
) -> List[Dict]:
    result = process_and_translate_file(c_file, generate_guards=True)
    manifest = _build_file_manifest_from_result(c_file, result, sibling_dirs=sibling_dirs)
    contexts = []
    for target_name in manifest["targets"]:
        contexts.append(_context_from_manifest(manifest, result, target_name))
    return contexts


def write_synthesis_context(
    c_file: str, output_path: str, func_name: Optional[str] = None,
    sibling_dirs: Optional[List[str]] = None
) -> Dict:
    context = collect_synthesis_context(c_file, func_name=func_name, sibling_dirs=sibling_dirs)
    output_dir = os.path.dirname(output_path)
    if output_dir:
        os.makedirs(output_dir, exist_ok=True)
    with open(output_path, "w", encoding="utf-8") as f:
        json.dump(context, f, indent=2)
        f.write("\n")
    return context
