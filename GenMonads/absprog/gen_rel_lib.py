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
    sibling_dirs: Optional[List[str]] = None,
) -> List[str]:
    """Return sorted callee names invoked by any of ``func_names`` whose
    definition lives in a sibling ``.c`` file.

    By default the search directory is the directory containing
    ``input_path``.  When ``sibling_dirs`` is provided, those directories
    are used instead (replace, not extend).
    """
    if sibling_dirs:
        search_dirs = [os.path.abspath(d) for d in sibling_dirs]
    else:
        search_dirs = [os.path.dirname(os.path.abspath(input_path))]
    own_basename = os.path.splitext(os.path.basename(input_path))[0]
    siblings = set()
    for d in search_dirs:
        try:
            for entry in os.listdir(d):
                if entry.endswith(".c"):
                    stem = os.path.splitext(entry)[0]
                    if stem != own_basename:
                        siblings.add(stem)
        except OSError:
            continue
    if not siblings:
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


# Monad backends selectable via the ``monad`` argument / ``--monad`` CLI flag.
# The two backends emit byte-identical bodies; only the import/export header
# below differs (see TODO/staterr_monad_option.md).
MONAD_BACKENDS = ("staterel", "staterr")

# Per-backend monad header (everything after the shared prelude).
#   staterel: import the aggregated MonadLib and Export the relational monad.
#   staterr : import ONLY MonadErr.StateRelMonadErr.  Importing the aggregated
#             MonadLib here would pull in StateRelMonad too and make `program`,
#             `bind`, `MONAD`, ... ambiguous between the two monads.  We also use
#             Import (not Export) so the err monad is not re-exported downstream.
_MONAD_HEADERS = {
    "staterel": (
        "From MonadLib Require Import MonadLib.\n"
        "Export StateRelMonad.\n"
        "Export MonadNotation.\n"
        "Local Open Scope monad."
    ),
    "staterr": (
        "From FP Require Import PartialOrder_Setoid BourbakiWitt.\n"
        "From MonadLib.MonadErr Require Import StateRelMonadErr.\n"
        "Import MonadNotation.\n"
        "Local Open Scope monad."
    ),
}

_COQ_PRELUDE = """\
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
"""


def coq_imports(monad: str = "staterel") -> str:
    """Return the import/export header for the requested monad backend.

    ``staterel`` (default) targets ``StateRelMonad``; ``staterr`` targets the
    error-aware ``MonadErr`` (whose ``repeat_break`` is built on the
    Bourbaki-Witt fixpoint, hence the extra ``From FP`` import).  The combinator
    names (``MONAD``, ``program``, ``bind``, ``choice``, ``assume!!``,
    ``repeat_break``, ``safeExec`` ...) are identical in both, so only this
    header changes.
    """
    try:
        header = _MONAD_HEADERS[monad]
    except KeyError:
        raise ValueError(
            f"Unknown monad backend: {monad!r} "
            f"(expected one of {sorted(_MONAD_HEADERS)})"
        )
    return _COQ_PRELUDE + "\n" + header + "\n"


# Backward-compatible alias for the default (staterel) header.
COQ_IMPORTS = coq_imports("staterel")


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
    shape = detect_early_return_shape(source)
    # Self-recursive Option-C functions can't use the split (M_before/
    # M_normal) scaffold: the LLM's `M_normal` would need to call the
    # entry-point `M`, which the scaffold defines later in the file
    # (unresolved reference).  Demote such functions to the simple-Parameter
    # path so the LLM writes a single recursive `Definition {fn}_M`.
    if shape.get("has_no_loop_early_return"):
        body = _extract_function_body(content, func_name)
        if body and re.search(rf"\b{re.escape(func_name)}\s*\(", body):
            shape = dict(shape)
            shape["has_no_loop_early_return"] = False
            shape["needs_early_result"] = False
            shape["is_recursive"] = True
    return shape


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


def generate_forest_func_block(
    func_name: str,
    require_var_types: Optional[List[str]],
    return_type: str,
    loop_templates: List[Dict],
    mretty_name: str = "MretTy",
    declare_mretty: bool = False,
) -> str:
    """Generate a multi-loop scaffold for one function (task #20).

    Layout per loop, bottom-up (children before parents):

    * Every loop has ``M_loop{k}_M1 : S_k -> MONAD MretTy`` and a guard
      (``Definition`` when GuardGen produced one, ``Parameter`` otherwise).
    * Leaf loops add ``M_loop{k}_M2 : S_k -> MONAD S_k`` as a Parameter.
    * Parent loops add ``M_loop{k}_to_inner_{c}`` / ``M_loop{k}_after_inner_{c}``
      Parameters per child *c* and emit a mechanical ``M_loop{k}_M2``
      Definition that threads them around each child's ``M_loop{c}_aux``.
    * ``Definition`` for body / aux follows the same shape as the single-loop
      scaffold.

    Top-level composition:

    * Each top-level loop gets a ``before`` Parameter.  Subsequent top-level
      loops (sequential case) take the previous loop's intermediate result
      type ``f_loop{k}_ResTy`` introduced just after MretTy.
    * Each top-level loop gets a ``loop_end`` Parameter.  The last
      top-level's end returns ``MONAD ({return_type})``; earlier ones return
      ``MONAD {ResTy_k}``.
    * ``Definition {fn}_M`` mechanically sequences the top-level loops:
      ``before;; aux;; end;; (mid)*``.
    """
    if not loop_templates:
        return ""

    fn = func_name
    require_var_types = list(require_var_types or [])
    by_idx = {t["loop_index"]: t for t in loop_templates}
    top_levels = sorted(
        (t for t in loop_templates if t["parent"] is None),
        key=lambda t: t["loop_index"],
    )
    if not top_levels:
        raise ValueError(
            f"Forest scaffold for '{fn}' has no top-level loop (every loop "
            "has a parent — likely an upstream bug)."
        )

    # Intermediate result Parameter types between sequential top-level loops.
    res_ty_for: Dict[int, str] = {}
    if len(top_levels) > 1:
        for t in top_levels[:-1]:
            res_ty_for[t["loop_index"]] = f"{fn}_loop{t['loop_index']+1}_ResTy"

    lines: List[str] = []
    lines.append(
        f"(* ---- Abstract program segments for {fn} "
        f"(loop forest: {len(loop_templates)} loops, "
        f"{len(top_levels)} top-level) ---- *)"
    )
    lines.append("")

    if declare_mretty:
        lines.append(f"Parameter {mretty_name} : Type.")
        lines.append("")

    if res_ty_for:
        for name in res_ty_for.values():
            lines.append(f"Parameter {name} : Type.")
        lines.append("")

    # Bottom-up DFS post-order so each parent's mechanical M2 references
    # children defined above.
    visited: set = set()
    bottom_up: List[Dict] = []

    def _dfs(idx: int) -> None:
        if idx in visited:
            return
        visited.add(idx)
        for c in by_idx[idx]["children"]:
            _dfs(c)
        bottom_up.append(by_idx[idx])

    for t in top_levels:
        _dfs(t["loop_index"])

    for t in bottom_up:
        k = t["loop_index"] + 1
        Sk = t["state_type"]
        Sk_arg = _type_arg(Sk)
        children = t["children"]

        lines.append(f"Parameter {fn}_M_loop{k}_M1 : {Sk} -> MONAD {mretty_name}.")

        if not children:
            # Leaf loop: LLM-provided step.
            lines.append(f"Parameter {fn}_M_loop{k}_M2 : {Sk} -> MONAD {Sk_arg}.")
        else:
            # Parent loop: per-child boundary holes, mechanical M2.
            for c_idx in children:
                ck = c_idx + 1
                c_state = by_idx[c_idx]["state_type"]
                Sc_arg = _type_arg(c_state)
                lines.append(
                    f"Parameter {fn}_M_loop{k}_to_inner_{ck} : {Sk} -> MONAD {Sc_arg}."
                )
                lines.append(
                    f"Parameter {fn}_M_loop{k}_after_inner_{ck} : "
                    f"{Sk} -> {mretty_name} -> MONAD {Sk_arg}."
                )
            lines.append(
                f"Definition {fn}_M_loop{k}_M2 : {Sk} -> MONAD {Sk_arg} :="
            )
            lines.append("  fun a =>")
            if len(children) == 1:
                ck = children[0] + 1
                lines.append(f"    s' <- {fn}_M_loop{k}_to_inner_{ck} a;;")
                lines.append(f"    r  <- {fn}_M_loop{ck}_aux s';;")
                lines.append(f"    {fn}_M_loop{k}_after_inner_{ck} a r.")
            else:
                acc = "a"
                for i, c_idx in enumerate(children):
                    ck = c_idx + 1
                    s_var = f"s{i+1}"
                    r_var = f"r{i+1}"
                    lines.append(
                        f"    {s_var} <- {fn}_M_loop{k}_to_inner_{ck} {acc};;"
                    )
                    lines.append(f"    {r_var} <- {fn}_M_loop{ck}_aux {s_var};;")
                    if i == len(children) - 1:
                        lines.append(
                            f"    {fn}_M_loop{k}_after_inner_{ck} {acc} {r_var}."
                        )
                    else:
                        next_acc = f"a{i+1}"
                        lines.append(
                            f"    {next_acc} <- "
                            f"{fn}_M_loop{k}_after_inner_{ck} {acc} {r_var};;"
                        )
                        acc = next_acc

        guard_name = f"{fn}_loop{k}_guardP"
        if t.get("coq_guard"):
            lines.append(f"Definition {guard_name} : {Sk} -> Prop :=")
            for guard_line in t["coq_guard"].split("\n"):
                lines.append(f"  {guard_line}")
            lines[-1] += "."
        else:
            lines.append("(* Guard could not be generated — declare as Parameter *)")
            lines.append(f"Parameter {guard_name} : {Sk} -> Prop.")

        lines.append(
            f"Definition {fn}_M_loop{k}_body : "
            f"{Sk} -> MONAD (CntOrBrk {Sk_arg} {mretty_name}) :="
        )
        lines.append("  fun a =>")
        lines.append(
            f"    choice (assume!! (~ ({guard_name} a));; "
            f"r <- {fn}_M_loop{k}_M1 a ;; break r)"
        )
        lines.append(
            f"           (assume!! (({guard_name} a));; "
            f"a' <- {fn}_M_loop{k}_M2 a ;; continue a')."
        )
        lines.append(
            f"Definition {fn}_M_loop{k}_aux := repeat_break {fn}_M_loop{k}_body."
        )
        # Curried wrapper so the ``_rel.c`` invariant can write
        # ``M_loop{k}(l1, l2, ...)`` instead of unpacking the state tuple.
        # Mirrors the single-loop scaffold's ``M_loop`` Definition.
        inv_arg_types = t["inv_var_types"] or []
        if inv_arg_types:
            k_arity = len(inv_arg_types)
            curried = _curried_args(inv_arg_types)
            lam = _lambda_vars(k_arity)
            tup = _tuple_vars(k_arity)
            lines.append(
                f"Definition {fn}_M_loop{k} : {curried}program unit {mretty_name} :="
            )
            lines.append(f"  fun {lam} => {fn}_M_loop{k}_aux {tup}.")
        lines.append("")

    req_curried = _curried_args(require_var_types) if require_var_types else ""
    # Top-level `before` and `end` Parameters.
    for i, t in enumerate(top_levels):
        k = t["loop_index"] + 1
        Sk_arg = _type_arg(t["state_type"])
        if i == 0:
            lines.append(f"Parameter {fn}_M_loop{k}_before : {req_curried}MONAD {Sk_arg}.")
        else:
            prev_res = res_ty_for[top_levels[i - 1]["loop_index"]]
            lines.append(f"Parameter {fn}_M_loop{k}_before : {prev_res} -> MONAD {Sk_arg}.")

    for i, t in enumerate(top_levels):
        k = t["loop_index"] + 1
        if i == len(top_levels) - 1:
            lines.append(
                f"Parameter {fn}_M_loop{k}_end : {mretty_name} -> MONAD ({return_type})."
            )
        else:
            res = res_ty_for[t["loop_index"]]
            lines.append(
                f"Parameter {fn}_M_loop{k}_end : {mretty_name} -> MONAD {res}."
            )
    lines.append("")

    # Definition {fn}_M = sequential composition.
    m = len(require_var_types)
    lines.append(f"Definition {fn}_M : {req_curried}MONAD ({return_type}) :=")
    if m > 0:
        req_lam = _lambda_vars(m)
        lines.append(f"  fun {req_lam} =>")
        first_before_args = f" {req_lam}"
    else:
        # No Require args — the composition is a monadic value, no lambda.
        # ``before`` is applied without arguments (its signature is
        # ``MONAD <state>`` rather than ``... -> MONAD <state>``).
        first_before_args = ""
    indent = "    " if m > 0 else "  "
    for i, t in enumerate(top_levels):
        k = t["loop_index"] + 1
        if i == 0:
            lines.append(
                f"{indent}s{i+1} <- {fn}_M_loop{k}_before{first_before_args};;"
            )
        else:
            prev_k = top_levels[i - 1]["loop_index"] + 1
            lines.append(f"{indent}s{i+1} <- {fn}_M_loop{k}_before t{prev_k};;")
        lines.append(f"{indent}r{i+1} <- {fn}_M_loop{k}_aux s{i+1};;")
        if i == len(top_levels) - 1:
            lines.append(f"{indent}{fn}_M_loop{k}_end r{i+1}.")
        else:
            lines.append(f"{indent}t{k} <- {fn}_M_loop{k}_end r{i+1};;")
    lines.append("")

    return "\n".join(lines)


def _collect_func_info_with_guard(func_data: Dict, include_helpers: bool = False,
                                  c_source: Optional[str] = None) -> Optional[Dict]:
    """Like collect_func_extern_info but also extracts coq_guard and, when
    *c_source* is supplied, the per-loop templates needed by the forest
    scaffold (task #20)."""
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
    info['loop_templates'] = _build_func_loop_templates(c_source, inv_assertions) if c_source else []
    return info


def _build_func_loop_templates(c_source: Optional[str], inv_assertions: List[Dict]) -> List[Dict]:
    """Per-loop descriptors — delegates to the canonical
    :func:`loop_forest.build_loop_templates`.  The ``func_name`` field is
    populated with an empty string here; gen_rel_lib only needs the
    nesting/state/guard fields and ignores ``func_name``."""
    from GenMonads.absprog.loop_forest import build_loop_templates
    return build_loop_templates("", c_source, inv_assertions)


def needs_mretty(info: Dict) -> bool:
    """Whether *info* describes a function that introduces a ``MretTy`` Parameter.

    A function "needs MretTy" if it has a loop (the loop break-value type is
    ``MretTy``), or if it has no loop but uses the split early-return
    scaffold (which also needs an intermediate type).  ``context.py`` and
    :func:`generate_rel_lib` share this predicate so the file-wide
    MretTy-scoping decision (per-function vs shared) is consistent between
    the synthesis prompt and the generated skeleton.

    *info* is expected to expose ``has_loop_program``,
    ``inv_var_count``, and/or ``has_no_loop_early_return``.  Missing keys
    fall back to ``False``.
    """
    if info.get("has_loop_program", info.get("inv_var_count", 0) > 0):
        return True
    if info.get("has_no_loop_early_return"):
        return True
    return False


def _build_in_file_call_graph(content: str, func_names: List[str]) -> Dict[str, set]:
    """Per-caller call graph restricted to in-file function names.  Used to
    topologically sort targets so callees are defined before callers."""
    graph: Dict[str, set] = {name: set() for name in func_names}
    for caller in func_names:
        body = _extract_function_body(content, caller)
        if body is None:
            continue
        stripped = _strip_c_comments(body)
        for callee in func_names:
            if callee == caller:
                continue
            if re.search(rf"\b{re.escape(callee)}\s*\(", stripped):
                graph[caller].add(callee)
    return graph


def _topo_sort_targets(targets: List[Dict], call_graph: Optional[Dict[str, set]]) -> List[Dict]:
    """Return ``targets`` reordered so callees precede callers.  When
    ``call_graph`` is None or omitted, the original order is preserved."""
    if not call_graph or len(targets) <= 1:
        return list(targets)

    info_by_name = {info['func_name']: info for info in targets}
    names = list(info_by_name)
    visited: set = set()
    visiting: set = set()
    ordered: List[str] = []
    cycle = [False]

    def visit(name: str):
        if name in visited or name not in info_by_name:
            return
        if name in visiting:
            cycle[0] = True
            return
        visiting.add(name)
        for callee in sorted(call_graph.get(name, set())):
            if callee in info_by_name:
                visit(callee)
        visiting.discard(name)
        visited.add(name)
        ordered.append(name)

    for name in names:
        visit(name)
    if cycle[0]:
        return list(targets)
    return [info_by_name[name] for name in ordered]


def generate_rel_lib(
    basename: str,
    func_infos: List[Dict],
    imported_rel_libs: Optional[List[str]] = None,
    call_graph: Optional[Dict[str, set]] = None,
    monad: str = "staterel",
    coq_lib_dir: Optional[str] = None,
) -> str:
    """Generate a complete _rel_lib.v skeleton file.

    Args:
        basename: e.g. "sll_copy" (without _rel_lib suffix)
        func_infos: list of dicts with func_name, require_var_count, inv_var_count, coq_guard
        monad: monad backend, one of ``MONAD_BACKENDS`` (default ``staterel``)
        coq_lib_dir: where the skeleton (and its sibling callee libs) will
            live.  When supplied AND a ``_CoqProject`` is discoverable from
            it, cross-file ``Require Import`` lines are emitted with the
            canonical qualified logical name computed from the project's
            ``-Q`` / ``-R`` mappings.  When None, bare names are used —
            the historical behaviour for callers without a project.
    """
    # Late import — keeps callers that don't need project resolution
    # from pulling in check_rocq.
    from GenMonads.absprog.check_rocq import qualified_require_import_for_callee

    parts = []
    parts.append(coq_imports(monad))
    parts.append("")
    for callee in (imported_rel_libs or []):
        qualified = qualified_require_import_for_callee(callee, coq_lib_dir)
        parts.append(f"Require Import {qualified}.")
    if imported_rel_libs:
        parts.append("")
    if any(info.get('ensure_var_count', 1) > 1 for info in func_infos):
        parts.append("Definition maketuple {A B} (a : A) (b : B) : (A * B) := (a, b).")
        parts.append("")

    # Scope MretTy per-function when more than one function in the file
    # needs it; otherwise keep a single shared `MretTy` parameter for
    # backward compatibility.  The shared :func:`needs_mretty` predicate is
    # also imported by ``context.py`` so the prompt's must_define list
    # carries the same scoped/bare name the skeleton emits.
    mretty_users = [info for info in func_infos if needs_mretty(info)]
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

    # Coq is top-down: any block that references `<name>_M` must come after
    # the block that introduces `<name>_M` (whether by Parameter or
    # Definition).  Topologically sort by the in-file call graph so callees
    # appear before callers.  When `call_graph` is None or there's a cycle,
    # preserve the source order.
    ordered_infos = _topo_sort_targets(func_infos, call_graph)

    for info in ordered_infos:
        fn = info['func_name']
        has_loop = info.get('has_loop_program', info['inv_var_count'] > 0)
        has_no_loop_early_return = info.get('has_no_loop_early_return', False)
        mretty_name = f"{fn}_MretTy" if scope_mretty_per_function else "MretTy"

        if has_loop:
            loop_templates = info.get('loop_templates') or []
            if len(loop_templates) > 1:
                # Multi-loop function (nested / sequential) — use the forest
                # scaffold instead of the single-loop collapse.
                ens_types = _normalize_var_types(
                    info.get('ensure_var_types'), info.get('ensure_var_count', 1)
                )
                ret_type = _return_type(ens_types)
                req_types = _normalize_var_types(
                    info.get('require_var_types'), info['require_var_count']
                )
                parts.append(generate_forest_func_block(
                    fn,
                    req_types,
                    ret_type,
                    loop_templates,
                    mretty_name=mretty_name,
                    declare_mretty=scope_mretty_per_function,
                ))
            else:
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


def generate_rel_lib_for_file(
    input_path: str,
    output_dir: str,
    sibling_dirs: Optional[List[str]] = None,
    monad: str = "staterel",
    coq_lib_dir: Optional[str] = None,
) -> Optional[str]:
    """Run the pipeline on a C file and generate the _rel_lib.v skeleton.

    Args:
        input_path: path to source C file (e.g. shape_invdataset/sll/sll_copy.c)
        output_dir: directory to write the .v file into
        sibling_dirs: directories to scan for sibling callee ``.c`` files
            (replaces the default of ``dirname(input_path)``).
        monad: monad backend, one of ``MONAD_BACKENDS`` (default ``staterel``)
        coq_lib_dir: where peer callee libs live (typically the same as
            *output_dir*).  Forwarded to :func:`generate_rel_lib` so cross-
            file ``Require Import`` lines pick up the qualified logical
            path resolved from ``_CoqProject``.  Defaults to *output_dir*
            when omitted — the natural fallback for the common case where
            this same call's output is also the project's lib directory.
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
    def _safe_func_source(fn_name: str) -> Optional[str]:
        if not fn_name:
            return None
        try:
            return _extract_function_source(content, fn_name)
        except ValueError:
            # Forward-declared callees have no body — that's fine; the
            # loop-templates path simply won't fire for them.
            return None

    if 'functions' in result and result['functions']:
        for func_data in result['functions']:
            # Include any function with a funcspec; emit the appropriate
            # scaffold (loop, no-loop early-return, or simple Parameter).
            include_helpers = not func_data.get('inner_assertions')
            func_source = _safe_func_source(func_data.get('function', ''))
            info = _collect_func_info_with_guard(
                func_data,
                include_helpers=include_helpers,
                c_source=func_source,
            )
            if info:
                info = _enrich_func_info_with_early_return_shape(content, info)
                func_infos.append(info)
    else:
        include_helpers = not result.get('inner_assertions')
        func_source = _safe_func_source(result.get('function', ''))
        info = _collect_func_info_with_guard(
            result,
            include_helpers=include_helpers,
            c_source=func_source,
        )
        if info:
            info = _enrich_func_info_with_early_return_shape(content, info)
            func_infos.append(info)

    if not func_infos:
        print(f"No abstract program signatures found in {input_path}")
        return None

    src_basename = os.path.splitext(os.path.basename(input_path))[0]
    func_names = [info['func_name'] for info in func_infos]
    imported_rel_libs = _collect_cross_file_callees(
        input_path, func_names, content, sibling_dirs=sibling_dirs
    )
    call_graph = _build_in_file_call_graph(content, func_names)
    effective_lib_dir = coq_lib_dir or output_dir
    content = generate_rel_lib(
        src_basename, func_infos, imported_rel_libs, call_graph, monad=monad,
        coq_lib_dir=effective_lib_dir,
    )

    os.makedirs(output_dir, exist_ok=True)
    out_path = os.path.join(output_dir, f"{src_basename}_rel_lib.v")
    with open(out_path, 'w', encoding='utf-8') as f:
        f.write(content)

    return out_path
