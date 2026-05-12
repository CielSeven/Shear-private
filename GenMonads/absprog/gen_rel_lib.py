"""
Generate {funcname}_rel_lib.v skeleton files with abstract program segments
declared as Parameters (no concrete definitions), except function-scoped guard
definitions which are
generated concretely from the pipeline's GuardGen.

The generated file provides:
- MretTy (opaque type Parameter)
- {func}_guardP (concrete Definition from GuardGen)
- M1, M2 (Parameters with correct types)
- loop_body, loop_aux, loop (concrete scaffolding)
- M_loop_end, M (Parameters)
"""

import os
import re
from typing import Dict, List, Optional

from GenMonads.early_return import detect_early_return_shape
from GenMonads.transshape.process_and_translate import process_and_translate_file
from GenMonads.translate_c_file import (
    _extract_function_body,
    _strip_c_comments,
    collect_func_extern_info,
    collect_callee_functions,
)


_C_KEYWORDS_AND_BUILTINS = {
    "if", "else", "for", "while", "do", "switch", "case", "default",
    "return", "break", "continue", "goto", "sizeof", "typedef",
    "struct", "union", "enum", "static", "extern", "const", "volatile",
    "register", "auto", "inline", "void", "char", "short", "int",
    "long", "float", "double", "signed", "unsigned", "_Bool",
    "malloc", "free", "calloc", "realloc", "memcpy", "memset",
    "printf", "fprintf", "scanf", "assert",
}


def _collect_cross_file_callees(
    input_path: str,
    func_names: List[str],
    content: str,
) -> List[str]:
    """Return sorted callee names invoked by any of `func_names` whose
    definition lives in a sibling `.c` file in the same directory."""
    input_dir = os.path.dirname(os.path.abspath(input_path))
    own_basename = os.path.splitext(os.path.basename(input_path))[0]
    siblings = set()
    try:
        for entry in os.listdir(input_dir):
            if entry.endswith(".c"):
                stem = os.path.splitext(entry)[0]
                if stem != own_basename:
                    siblings.add(stem)
    except OSError:
        return []

    call_names = set()
    local_names = set(func_names)
    for caller in func_names:
        body = _extract_function_body(content, caller)
        if body is None:
            continue
        stripped = _strip_c_comments(body)
        for match in re.finditer(r"\b([A-Za-z_][A-Za-z0-9_]*)\s*\(", stripped):
            call_names.add(match.group(1))

    callees = call_names & siblings - local_names - _C_KEYWORDS_AND_BUILTINS
    return sorted(callees)


COQ_IMPORTS = """\
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import SetsClass.SetsClass. Import SetsNotation.
Local Open Scope Z_scope.
Local Open Scope sets.
Import ListNotations.
Local Open Scope string.
Local Open Scope list.

From MonadLib Require Import MonadLib.
Export StateRelMonad.
Export MonadNotation.
Local Open Scope monad.
"""


def _normalize_var_types(var_types: Optional[List[str]], count: int) -> List[str]:
    if count == 0:
        return []
    if var_types is None:
        raise ValueError(f"Missing variable types for {count} generated variable(s)")

    normalized = list(var_types)
    if len(normalized) != count:
        raise ValueError(
            f"Variable type count mismatch: expected {count}, got {len(normalized)}"
        )
    return normalized


def _tuple_type(types: List[str]) -> str:
    if not types:
        raise ValueError("Expected at least one type")
    if len(types) == 1:
        return types[0]
    return "(" + " * ".join(types) + ")"


def _return_type(types: List[str]) -> str:
    if not types:
        return "unit"
    return _tuple_type(types)


def _type_arg(type_expr: str) -> str:
    if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", type_expr):
        return type_expr
    if type_expr.startswith("(") and type_expr.endswith(")"):
        return type_expr
    return f"({type_expr})"


def _early_result_type(state_type: str, return_type: str) -> str:
    return f"early_result {_type_arg(state_type)} {_type_arg(return_type)}"


def _curried_args(types: List[str]) -> str:
    """Build curried argument types from a list of Coq types."""
    if not types:
        return ""
    return " -> ".join(types) + " -> "


def _lambda_vars(k: int) -> str:
    """Build lambda variable names: l1 l2 l3 ..."""
    return " ".join(f"l{i}" for i in range(1, k + 1))


def _tuple_vars(k: int) -> str:
    """Build tuple: (l1, l2, l3) or just l1 for k=1."""
    if k == 1:
        return "l1"
    return "(" + ", ".join(f"l{i}" for i in range(1, k + 1)) + ")"


def _extract_function_source(content: str, func_name: str) -> str:
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
        raise ValueError(f"Could not find function signature for '{func_name}'")

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
        raise ValueError(f"Could not find function body end for '{func_name}'")

    return content[start:end]


def collect_early_return_shape_for_function(content: str, func_name: str) -> Dict[str, bool]:
    """Detect whether a function has early-return points around its first loop."""
    try:
        source = _extract_function_source(content, func_name)
    except ValueError:
        return {
            "has_top_level_loop": False,
            "has_pre_loop_early_return": False,
            "has_loop_body_early_return": False,
            "has_no_loop_early_return": False,
            "needs_early_result": False,
        }
    return detect_early_return_shape(source)


def _enrich_func_info_with_early_return_shape(content: str, info: Dict) -> Dict:
    enriched = dict(info)
    func_name = enriched["func_name"]
    shape = collect_early_return_shape_for_function(content, func_name)
    enriched.update(shape)

    inv_var_types = enriched.get("inv_var_types", [])
    ensure_var_types = enriched.get("ensure_var_types", [])
    state_type = _tuple_type(inv_var_types) if inv_var_types else "unit"
    return_type = _return_type(ensure_var_types)
    enriched["state_type"] = state_type
    enriched["return_type"] = return_type
    enriched["loop_result_type"] = (
        _early_result_type("MretTy", return_type)
        if shape.get("has_loop_body_early_return")
        else "MretTy"
    )
    enriched["needs_early_result"] = shape.get("needs_early_result", False)
    return enriched


def generate_func_block(func_name: str, require_var_count: int,
                        inv_var_count: int, ensure_var_count: int = 1,
                        require_var_types: Optional[List[str]] = None,
                        inv_var_types: Optional[List[str]] = None,
                        ensure_var_types: Optional[List[str]] = None,
                        coq_guard: Optional[str] = None,
                        has_pre_loop_early_return: bool = False,
                        has_loop_body_early_return: bool = False,
                        mretty_name: str = "MretTy",
                        declare_mretty: bool = False) -> str:
    """Generate the abstract program skeleton for one function.

    Args:
        mretty_name: name of the MretTy type in this block (``"MretTy"`` for
            single-function libraries, ``f"{func_name}_MretTy"`` for
            multi-function libraries).
        declare_mretty: if True, emit ``Parameter {mretty_name} : Type.`` at
            the start of the block (used for per-function MretTy scoping).
    """
    fn = func_name
    k = inv_var_count
    m = require_var_count
    req_types = _normalize_var_types(require_var_types, require_var_count)
    inv_types = _normalize_var_types(inv_var_types, inv_var_count)
    ens_types = _normalize_var_types(ensure_var_types, ensure_var_count)
    st = _tuple_type(inv_types)
    ret = _return_type(ens_types)
    before_result = _early_result_type(st, ret) if has_pre_loop_early_return else st
    loop_result = (
        _early_result_type(mretty_name, ret) if has_loop_body_early_return else mretty_name
    )
    m2_result = _early_result_type(st, ret) if has_loop_body_early_return else st
    guard_name = f"{fn}_guardP"

    lines = []
    lines.append(f"(* ---- Abstract program segments for {fn} ---- *)")
    lines.append("")

    if declare_mretty:
        lines.append(f"Parameter {mretty_name} : Type.")
        lines.append("")

    st_arg = _type_arg(st)
    # Parameters: M1, M2, loop_end (LLM-generated components)
    lines.append(f"Parameter {fn}_M_loop_M1 : {st} -> MONAD {mretty_name}.")
    if has_loop_body_early_return:
        lines.append(f"Parameter {fn}_M_loop_M2 : {st} -> MONAD ({m2_result}).")
    else:
        lines.append(f"Parameter {fn}_M_loop_M2 : {st} -> MONAD {st_arg}.")
    lines.append("")

    # Function-scoped guard: concrete Definition from GuardGen, or Parameter as fallback
    if coq_guard:
        # coq_guard already includes "fun a => let '(...) := a in ..."
        lines.append(f"Definition {guard_name} : {st} -> Prop :=")
        # Indent each line of the guard body
        for guard_line in coq_guard.split('\n'):
            lines.append(f"  {guard_line}")
        # Replace trailing newline with period
        lines[-1] = lines[-1] + "."
    else:
        lines.append(f"(* Guard could not be generated — declare as Parameter *)")
        lines.append(f"Parameter {guard_name} : {st} -> Prop.")
    lines.append("")

    lines.append(f"Parameter {fn}_M_loop_end : {mretty_name} -> MONAD ({ret}).")
    lines.append("")

    if has_loop_body_early_return:
        lines.append(f"Definition {fn}_M_after_loop : ({loop_result}) -> MONAD ({ret}) :=")
        lines.append(f"  fun re =>")
        lines.append(f"    match re with")
        lines.append(f"    | Continue r => {fn}_M_loop_end r")
        lines.append(f"    | ReturnNow r => return r")
        lines.append(f"    end.")
        lines.append("")

    # Concrete scaffolding: loop_body using choice/assume/break/continue
    if has_loop_body_early_return:
        lines.append(
            f"Definition {fn}_M_loop_body : {st} -> MONAD (CntOrBrk {st_arg} ({loop_result})) :="
        )
    else:
        lines.append(f"Definition {fn}_M_loop_body : {st} -> MONAD (CntOrBrk {st_arg} {mretty_name}) :=")
    lines.append(f"  fun a =>")
    if has_loop_body_early_return:
        lines.append(
            f"    choice (assume!! (~ ({guard_name} a));; r <- {fn}_M_loop_M1 a ;; break (Continue r))"
        )
        lines.append(f"           (assume!! (({guard_name} a));;")
        lines.append(f"            a' <- {fn}_M_loop_M2 a ;;")
        lines.append(f"            match a' with")
        lines.append(f"            | Continue a'' => continue a''")
        lines.append(f"            | ReturnNow r' => break (ReturnNow r')")
        lines.append(f"            end).")
    else:
        lines.append(f"    choice (assume!! (~ ({guard_name} a));; r <- {fn}_M_loop_M1 a ;; break r)")
        lines.append(f"           (assume!! (({guard_name} a));; a' <- {fn}_M_loop_M2 a ;; continue a').")
    lines.append("")

    lines.append(f"Definition {fn}_M_loop_aux :=")
    lines.append(f"  repeat_break {fn}_M_loop_body.")
    lines.append("")

    # Curried wrapper
    lam = _lambda_vars(k)
    tup = _tuple_vars(k)
    curried = _curried_args(inv_types)
    if has_loop_body_early_return:
        lines.append(f"Definition {fn}_M_loop : {curried}program unit ({loop_result}) :=")
    else:
        lines.append(f"Definition {fn}_M_loop : {curried}program unit {mretty_name} :=")
    lines.append(f"  fun {lam} => {fn}_M_loop_aux {tup}.")
    lines.append("")

    # loop_before: Parameter (maps Require vars to initial invariant state)
    m_curried = _curried_args(req_types)
    if has_pre_loop_early_return:
        lines.append(f"Parameter {fn}_M_loop_before : {m_curried}MONAD ({before_result}).")
    else:
        lines.append(f"Parameter {fn}_M_loop_before : {m_curried}MONAD {st_arg}.")
    lines.append("")

    # M: concrete composition of loop_before → loop → loop_end
    m_lam = _lambda_vars(m)
    lines.append(f"Definition {fn}_M : {m_curried}MONAD ({ret}) :=")
    lines.append(f"  fun {m_lam} =>")
    if has_pre_loop_early_return:
        lines.append(f"    e <- {fn}_M_loop_before {m_lam};;")
        lines.append(f"    match e with")
        lines.append(f"    | Continue s =>")
        lines.append(f"        re <- {fn}_M_loop_aux s;;")
        if has_loop_body_early_return:
            lines.append(f"        {fn}_M_after_loop re")
        else:
            lines.append(f"        {fn}_M_loop_end re")
        lines.append(f"    | ReturnNow r =>")
        lines.append(f"        return r")
        lines.append(f"    end.")
    else:
        lines.append(f"    s0 <- {fn}_M_loop_before {m_lam};;")
        lines.append(f"    re <- {fn}_M_loop_aux s0;;")
        if has_loop_body_early_return:
            lines.append(f"    {fn}_M_after_loop re.")
        else:
            lines.append(f"    {fn}_M_loop_end re.")
    lines.append("")

    return "\n".join(lines)


def generate_simple_func_block(func_name: str,
                               require_var_count: int,
                               ensure_var_count: int = 1,
                               require_var_types: Optional[List[str]] = None,
                               ensure_var_types: Optional[List[str]] = None) -> str:
    """Generate a lightweight abstract-program declaration for callee-only functions."""
    fn = func_name
    req_types = _normalize_var_types(require_var_types, require_var_count)
    ens_types = _normalize_var_types(ensure_var_types, ensure_var_count)
    ret = _return_type(ens_types)
    m_curried = _curried_args(req_types)

    lines = []
    lines.append(f"(* ---- Abstract program declaration for {fn} ---- *)")
    lines.append("")
    lines.append(f"Parameter {fn}_M : {m_curried}MONAD ({ret}).")
    lines.append("")
    return "\n".join(lines)


def generate_no_loop_early_return_block(func_name: str,
                                        require_var_count: int,
                                        ensure_var_count: int = 1,
                                        require_var_types: Optional[List[str]] = None,
                                        ensure_var_types: Optional[List[str]] = None,
                                        mretty_name: str = "MretTy",
                                        declare_mretty: bool = False) -> str:
    """Generate the abstract-program scaffold for a function with no loop but
    at least one early-return branch.

    Splits the function into ``{fn}_M_before`` (initial dispatch returning
    ``early_result {mretty_name} {ret}``) and ``{fn}_M_normal``
    (the non-early-return continuation).  ``{fn}_M`` composes them.
    """
    fn = func_name
    m = require_var_count
    req_types = _normalize_var_types(require_var_types, require_var_count)
    ens_types = _normalize_var_types(ensure_var_types, ensure_var_count)
    ret = _return_type(ens_types)
    m_curried = _curried_args(req_types)
    m_lam = _lambda_vars(m)
    before_result = _early_result_type(mretty_name, ret)

    lines = []
    lines.append(f"(* ---- Abstract program segments for {fn} ---- *)")
    lines.append("")

    if declare_mretty:
        lines.append(f"Parameter {mretty_name} : Type.")
        lines.append("")

    lines.append(
        f"Parameter {fn}_M_before : {m_curried}MONAD ({before_result})."
    )
    lines.append(f"Parameter {fn}_M_normal : {mretty_name} -> MONAD ({ret}).")
    lines.append("")

    lines.append(f"Definition {fn}_M : {m_curried}MONAD ({ret}) :=")
    lines.append(f"  fun {m_lam} =>")
    lines.append(f"    e <- {fn}_M_before {m_lam};;")
    lines.append(f"    match e with")
    lines.append(f"    | Continue s => {fn}_M_normal s")
    lines.append(f"    | ReturnNow r => return r")
    lines.append(f"    end.")
    lines.append("")

    return "\n".join(lines)


def _collect_func_info_with_guard(func_data: Dict, include_helpers: bool = False) -> Optional[Dict]:
    """Like collect_func_extern_info but also extracts coq_guard."""
    info = collect_func_extern_info(func_data, include_helpers=include_helpers)
    if info is None:
        return None

    inner = func_data.get('inner_assertions', [])
    inv_assertions = [a for a in inner if a.get('type') == 'Inv' and 'variables' in a]

    # Take the first invariant's guard (for single-loop functions)
    coq_guard = None
    for a in inv_assertions:
        if 'coq_guard' in a:
            coq_guard = a['coq_guard']
            break

    info['coq_guard'] = coq_guard
    return info


def generate_rel_lib(
    basename: str,
    func_infos: List[Dict],
    imported_rel_libs: Optional[List[str]] = None,
) -> str:
    """Generate a complete _rel_lib.v skeleton file.

    Args:
        basename: e.g. "sll_copy" (without _rel_lib suffix)
        func_infos: list of dicts with func_name, require_var_count, inv_var_count, coq_guard
    """
    parts = []
    parts.append(COQ_IMPORTS)
    parts.append("")
    for callee in (imported_rel_libs or []):
        parts.append(f"Require Import {callee}_rel_lib.")
    if imported_rel_libs:
        parts.append("")
    if any(info.get('ensure_var_count', 1) > 1 for info in func_infos):
        parts.append("Definition maketuple {A B} (a : A) (b : B) : (A * B) := (a, b).")
        parts.append("")

    # A function "needs MretTy" if it has a loop, or if it has no loop but
    # uses the split early-return scaffold (which also needs an intermediate
    # type).  Scope MretTy per-function when more than one function in the
    # file needs it; otherwise keep a single shared `MretTy` parameter for
    # backward compatibility.
    def _needs_mretty(info: Dict) -> bool:
        if info.get('has_loop_program', info['inv_var_count'] > 0):
            return True
        if info.get('has_no_loop_early_return'):
            return True
        return False

    mretty_users = [info for info in func_infos if _needs_mretty(info)]
    scope_mretty_per_function = len(mretty_users) > 1

    if mretty_users and not scope_mretty_per_function:
        parts.append("Parameter MretTy : Type.")
        parts.append("")

    if any(
        info.get("needs_early_result")
        or info.get("has_pre_loop_early_return")
        or info.get("has_loop_body_early_return")
        or info.get("has_no_loop_early_return")
        for info in func_infos
    ):
        parts.append(
            "Inductive early_result (S Ret : Type) :=\n"
            "| Continue : S -> early_result S Ret\n"
            "| ReturnNow : Ret -> early_result S Ret."
        )
        parts.append("Arguments Continue {S Ret} _.")
        parts.append("Arguments ReturnNow {S Ret} _.")
        parts.append("")

    for info in func_infos:
        fn = info['func_name']
        has_loop = info.get('has_loop_program', info['inv_var_count'] > 0)
        has_no_loop_early_return = info.get('has_no_loop_early_return', False)
        mretty_name = f"{fn}_MretTy" if scope_mretty_per_function else "MretTy"

        if has_loop:
            parts.append(generate_func_block(
                fn,
                info['require_var_count'],
                info['inv_var_count'],
                info.get('ensure_var_count', 1),
                info.get('require_var_types'),
                info.get('inv_var_types'),
                info.get('ensure_var_types'),
                info.get('coq_guard'),
                has_pre_loop_early_return=info.get('has_pre_loop_early_return', False),
                has_loop_body_early_return=info.get('has_loop_body_early_return', False),
                mretty_name=mretty_name,
                declare_mretty=scope_mretty_per_function,
            ))
        elif has_no_loop_early_return:
            parts.append(generate_no_loop_early_return_block(
                fn,
                info['require_var_count'],
                info.get('ensure_var_count', 1),
                info.get('require_var_types'),
                info.get('ensure_var_types'),
                mretty_name=mretty_name,
                declare_mretty=scope_mretty_per_function,
            ))
        else:
            parts.append(generate_simple_func_block(
                fn,
                info['require_var_count'],
                info.get('ensure_var_count', 1),
                info.get('require_var_types'),
                info.get('ensure_var_types'),
            ))

    return "\n".join(parts)


def generate_rel_lib_for_file(input_path: str, output_dir: str) -> Optional[str]:
    """Run the pipeline on a C file and generate the _rel_lib.v skeleton.

    Args:
        input_path: path to source C file (e.g. shape_invdataset/sll/sll_copy.c)
        output_dir: directory to write the .v file into

    Returns:
        path to the generated .v file, or None on failure
    """
    try:
        result = process_and_translate_file(input_path, generate_guards=True)
    except Exception as e:
        print(f"Error processing {input_path}: {e}")
        return None

    if 'error' in result:
        print(f"Error: {result['error']}")
        return None

    func_infos = []
    with open(input_path, 'r', encoding='utf-8') as f:
        content = f.read()
    if 'functions' in result and result['functions']:
        for func_data in result['functions']:
            # Include any function with a funcspec; emit the appropriate
            # scaffold (loop, no-loop early-return, or simple Parameter).
            include_helpers = not func_data.get('inner_assertions')
            info = _collect_func_info_with_guard(
                func_data,
                include_helpers=include_helpers,
            )
            if info:
                info = _enrich_func_info_with_early_return_shape(content, info)
                func_infos.append(info)
    else:
        include_helpers = not result.get('inner_assertions')
        info = _collect_func_info_with_guard(
            result,
            include_helpers=include_helpers,
        )
        if info:
            info = _enrich_func_info_with_early_return_shape(content, info)
            func_infos.append(info)

    if not func_infos:
        print(f"No abstract program signatures found in {input_path}")
        return None

    src_basename = os.path.splitext(os.path.basename(input_path))[0]
    func_names = [info['func_name'] for info in func_infos]
    imported_rel_libs = _collect_cross_file_callees(input_path, func_names, content)
    content = generate_rel_lib(src_basename, func_infos, imported_rel_libs)

    os.makedirs(output_dir, exist_ok=True)
    out_path = os.path.join(output_dir, f"{src_basename}_rel_lib.v")
    with open(out_path, 'w', encoding='utf-8') as f:
        f.write(content)

    return out_path
