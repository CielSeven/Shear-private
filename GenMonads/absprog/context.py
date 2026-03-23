import json
import os
import re
from typing import Dict, List, Optional

from GenMonads.addabstract import add_safeexec_predicate, process_funcspec_with_safeexec
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


def _make_context_id(c_file: str, result: Dict, func_data: Dict) -> str:
    basename = os.path.splitext(os.path.basename(c_file))[0]
    functions = _collect_functions(result)
    if len(functions) > 1:
        return func_data["function"]
    return basename


def _select_function(result: Dict, func_name: Optional[str]) -> Dict:
    functions = _collect_functions(result)
    if func_name:
        for func_data in functions:
            if func_data["function"] == func_name:
                return func_data
        raise ValueError(f"Function '{func_name}' not found in {result['file']}")

    if len(functions) != 1:
        names = ", ".join(func["function"] for func in functions)
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
        # Only consider top-level signatures so we skip call sites inside bodies.
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


def collect_synthesis_context(c_file: str, func_name: Optional[str] = None) -> Dict:
    result = process_and_translate_file(c_file, generate_guards=True)
    return _collect_synthesis_context_from_result(c_file, result, func_name)


def _collect_synthesis_context_from_result(
    c_file: str, result: Dict, func_name: Optional[str] = None
) -> Dict:
    if "error" in result:
        raise ValueError(result["error"])

    func_data = _select_function(result, func_name)
    info = collect_func_extern_info(func_data)
    if info is None:
        raise ValueError(f"Function '{func_data['function']}' has no loop invariants")

    funcspec = func_data.get("funcspec") or {}
    inv_assertions = [a for a in func_data.get("inner_assertions", []) if a.get("type") == "Inv"]
    first_inv = inv_assertions[0] if inv_assertions else {}
    program = f"{func_data['function']}_M"
    program_loop = f"{func_data['function']}_M_loop"
    program_loop_end = f"{func_data['function']}_M_loop_end"
    processed_funcspec = process_funcspec_with_safeexec(funcspec, program) if funcspec else {}

    require_types = _require_var_types(info, "require_var_types", "require_var_count")
    inv_types = _require_var_types(info, "inv_var_types", "inv_var_count")
    ensure_types = _require_var_types(info, "ensure_var_types", "ensure_var_count")
    state_type = _tuple_type(inv_types)
    return_type = _return_type_from_types(ensure_types)

    require_translated = funcspec.get("require", {}).get("translated", "")
    ensure_translated = funcspec.get("ensure", {}).get("translated", "")
    loop_invariant_translated = first_inv.get("translated", "")
    require_with_safeexec = processed_funcspec.get("require", {}).get("with_safeexec", "")
    ensure_with_safeexec = processed_funcspec.get("ensure", {}).get("with_safeexec", "")
    loop_invariant_with_safeexec = ""
    if first_inv.get("translated"):
        loop_invariant_with_safeexec = add_safeexec_predicate(
            first_inv["translated"],
            first_inv.get("variables", []),
            program_loop,
            program_loop_end,
        )

    return {
        "id": _make_context_id(c_file, result, func_data),
        "version": 1,
        "source": {
            "c_file": c_file,
        },
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
            "c_source": _extract_function_source(c_file, func_data["function"]),
            "with_clause": processed_funcspec.get("with", {}).get("translated", ""),
            "require_with_safeexec": require_with_safeexec,
            "ensure_with_safeexec": ensure_with_safeexec,
            "loop_invariant_with_safeexec": loop_invariant_with_safeexec,
            "loop_condition": first_inv.get("command_guard", ""),
            "guard_coq": first_inv.get("coq_guard", ""),
        },
        "signatures": {
            "M_loop_before": f"{_curried_type(require_types)}MONAD {state_type}",
            "M_1": f"{state_type} -> MONAD MretTy",
            "M_2": f"{state_type} -> MONAD {state_type}",
            "M_loop_end": f"MretTy -> MONAD ({return_type})",
            "M": f"{_curried_type(require_types)}MONAD ({return_type})",
        },
    }


def collect_all_synthesis_contexts(c_file: str) -> List[Dict]:
    result = process_and_translate_file(c_file, generate_guards=True)
    functions = _collect_functions(result)
    contexts = []
    for func_data in functions:
        if collect_func_extern_info(func_data) is None:
            continue
        contexts.append(
            _collect_synthesis_context_from_result(c_file, result, func_data["function"])
        )
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
