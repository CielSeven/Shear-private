import json
import os
import re
from typing import Dict, List, Optional

from GenMonads.addabstract import add_safeexec_predicate, process_funcspec_with_safeexec
from GenMonads.early_return import detect_early_return_shape
from GenMonads.transshape.process_and_translate import process_and_translate_file
from GenMonads.translate_c_file import collect_func_extern_info


def _normalize_block(text: str) -> str:
    lines = [line.rstrip() for line in text.strip().splitlines()]
    return "\n".join(lines)


def _tuple_type(types: List[str]) -> str:
    if len(types) == 1:
        return types[0]
    return "(" + " * ".join(types) + ")"


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

    if len(functions) != 1:
        names = ", ".join(func.get("func_name", func.get("function")) for func in functions)
        raise ValueError(
            "Function name is required for multi-function files. "
            f"Available functions: {names}"
        )
    return functions[0]


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
) -> Dict:
    state_type = _tuple_type(inv_types)
    req_args = _curried_type(require_types)
    inv_args = _curried_type(inv_types)
    loop_ret_type = f"early_result MretTy ({return_type})" if has_loop_body_early_return else "MretTy"
    loop_before_type = (
        f"{req_args}MONAD (early_result {state_type} ({return_type}))"
        if has_pre_loop_early_return
        else f"{req_args}MONAD {state_type}"
    )
    loop_body_type = (
        f"{state_type} -> MONAD (CntOrBrk {state_type} (early_result MretTy ({return_type})))"
        if has_loop_body_early_return
        else f"{state_type} -> MONAD (CntOrBrk {state_type} MretTy)"
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
        f"{state_type} -> MONAD (early_result {state_type} ({return_type}))"
        if has_loop_body_early_return
        else f"{state_type} -> MONAD {state_type}"
    )

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
        "needs_early_result": has_pre_loop_early_return or has_loop_body_early_return,
        "state_type": state_type,
        "return_type": return_type,
        "prompt_signatures": prompt_signatures,
        "template": {
            "loop_body_definition": loop_body_definition,
            "top_level": top_level_definition,
            "after_loop_definition": after_loop_definition,
        },
    }


def _collect_extern_info(func_data: Dict, include_helpers: bool = False) -> Optional[Dict]:
    try:
        return collect_func_extern_info(func_data, include_helpers=include_helpers)
    except TypeError:
        return collect_func_extern_info(func_data)


def _build_target_details(c_file: str, result: Dict, func_data: Dict) -> Dict:
    info = collect_func_extern_info(func_data)
    if info is None:
        raise ValueError(f"Function '{func_data['function']}' has no loop invariants")

    funcspec = func_data.get("funcspec") or {}
    inv_assertions = [a for a in func_data.get("inner_assertions", []) if a.get("type") == "Inv"]
    first_inv = inv_assertions[0] if inv_assertions else {}
    program = f"{func_data['function']}_M"
    processed_funcspec = process_funcspec_with_safeexec(funcspec, program) if funcspec else {}
    c_source = _extract_function_source(c_file, func_data["function"])

    require_types = _require_var_types(info, "require_var_types", "require_var_count")
    inv_types = _require_var_types(info, "inv_var_types", "inv_var_count")
    ensure_types = _require_var_types(info, "ensure_var_types", "ensure_var_count")
    state_type = _tuple_type(inv_types)
    return_type = _return_type_from_types(ensure_types)
    early_return_shape = detect_early_return_shape(c_source)
    has_pre_loop_early_return = early_return_shape["has_pre_loop_early_return"]
    has_loop_body_early_return = early_return_shape["has_loop_body_early_return"]
    control_flow = _build_control_flow_template(
        func_data["function"],
        require_types,
        inv_types,
        return_type,
        has_pre_loop_early_return,
        has_loop_body_early_return,
    )
    control_flow["has_top_level_loop"] = early_return_shape["has_top_level_loop"]
    control_flow["has_top_level_loop"] = early_return_shape["has_top_level_loop"]

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
        },
        "signatures": {
            "M_loop_before": f"{_curried_type(require_types)}MONAD {state_type}",
            "M_1": f"{state_type} -> MONAD MretTy",
            "M_2": f"{state_type} -> MONAD {state_type}",
            "M_loop_end": f"MretTy -> MONAD ({return_type})",
            "M": f"{_curried_type(require_types)}MONAD ({return_type})",
        },
        "control_flow": control_flow,
    }


def _build_file_manifest_from_result(c_file: str, result: Dict) -> Dict:
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

    call_graph: Dict[str, List[str]] = {}
    call_sites: Dict[str, Dict[str, List[str]]] = {}
    for name, source in function_sources.items():
        calls = _collect_calls_for_source(source, function_names)
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
        should_synthesize = has_body and has_loop_invariants
        if should_synthesize:
            targets.append(func_name)

        helper_info = _collect_extern_info(
            func_data,
            include_helpers=func_data.get("funcspec") is not None,
        )
        externals = {}
        if helper_info is not None:
            externals["M"] = _build_m_signature(helper_info)

        entry = {
            "func_name": func_name,
            "has_body": has_body,
            "has_loop_invariants": has_loop_invariants,
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

    return {
        "file_id": os.path.splitext(os.path.basename(c_file))[0],
        "version": 2,
        "source": {
            "c_file": c_file,
        },
        "functions": manifest_functions,
        "targets": targets,
    }


def collect_file_synthesis_manifest(c_file: str) -> Dict:
    result = process_and_translate_file(c_file, generate_guards=True)
    return _build_file_manifest_from_result(c_file, result)


def _context_from_manifest(manifest: Dict, result: Dict, func_name: Optional[str] = None) -> Dict:
    func_entry = _select_function(manifest["functions"], func_name, manifest["source"]["c_file"])
    if not func_entry["should_synthesize"]:
        raise ValueError(f"Function '{func_entry['func_name']}' has no loop invariants")

    available_callees = []
    for callee_name in func_entry.get("calls", []):
        callee_entry = next(
            (entry for entry in manifest["functions"] if entry["func_name"] == callee_name),
            None,
        )
        if callee_entry is None:
            continue
        opaque_program = callee_name + "_M"
        available_callees.append({
            "func_name": callee_name,
            "opaque_program": opaque_program,
            "has_body": callee_entry["has_body"],
            "should_synthesize_elsewhere": callee_entry["should_synthesize"],
            "externals": callee_entry.get("externals", {}),
            "spec": callee_entry.get("spec", {}),
            "call_sites": func_entry.get("call_sites", {}).get(callee_name, []),
        })

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
    must_define = [
        "MretTy",
        f"{func_entry['func_name']}_M_loop_before",
        f"{func_entry['func_name']}_M_loop_M1",
        f"{func_entry['func_name']}_M_loop_M2",
        f"{func_entry['func_name']}_M_loop_end",
    ]
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
        "control_flow": func_entry.get("control_flow", {}),
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
        "control_flow": func_entry.get("control_flow", {}),
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


def collect_synthesis_context(c_file: str, func_name: Optional[str] = None) -> Dict:
    result = process_and_translate_file(c_file, generate_guards=True)
    manifest = _build_file_manifest_from_result(c_file, result)
    return _context_from_manifest(manifest, result, func_name)


def collect_all_synthesis_contexts(c_file: str) -> List[Dict]:
    result = process_and_translate_file(c_file, generate_guards=True)
    manifest = _build_file_manifest_from_result(c_file, result)
    contexts = []
    for target_name in manifest["targets"]:
        contexts.append(_context_from_manifest(manifest, result, target_name))
    return contexts


def write_synthesis_context(
    c_file: str, output_path: str, func_name: Optional[str] = None
) -> Dict:
    context = collect_synthesis_context(c_file, func_name=func_name)
    output_dir = os.path.dirname(output_path)
    if output_dir:
        os.makedirs(output_dir, exist_ok=True)
    with open(output_path, "w", encoding="utf-8") as f:
        json.dump(context, f, indent=2)
        f.write("\n")
    return context
