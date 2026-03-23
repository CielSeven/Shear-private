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
from typing import Dict, List, Optional

from GenMonads.transshape.process_and_translate import process_and_translate_file
from GenMonads.translate_c_file import collect_func_extern_info


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


def generate_func_block(func_name: str, require_var_count: int,
                        inv_var_count: int, ensure_var_count: int = 1,
                        require_var_types: Optional[List[str]] = None,
                        inv_var_types: Optional[List[str]] = None,
                        ensure_var_types: Optional[List[str]] = None,
                        coq_guard: Optional[str] = None) -> str:
    """Generate the abstract program skeleton for one function."""
    fn = func_name
    k = inv_var_count
    m = require_var_count
    req_types = _normalize_var_types(require_var_types, require_var_count)
    inv_types = _normalize_var_types(inv_var_types, inv_var_count)
    ens_types = _normalize_var_types(ensure_var_types, ensure_var_count)
    st = _tuple_type(inv_types)
    ret = _return_type(ens_types)
    guard_name = f"{fn}_guardP"

    lines = []
    lines.append(f"(* ---- Abstract program segments for {fn} ---- *)")
    lines.append("")

    # Parameters: M1, M2, loop_end (LLM-generated components)
    lines.append(f"Parameter {fn}_M_loop_M1 : {st} -> MONAD MretTy.")
    lines.append(f"Parameter {fn}_M_loop_M2 : {st} -> MONAD {st}.")
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

    lines.append(f"Parameter {fn}_M_loop_end : MretTy -> MONAD ({ret}).")
    lines.append("")

    # Concrete scaffolding: loop_body using choice/assume/break/continue
    lines.append(f"Definition {fn}_M_loop_body : {st} -> MONAD (CntOrBrk {st} MretTy) :=")
    lines.append(f"  fun a =>")
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
    lines.append(f"Definition {fn}_M_loop : {curried}program unit MretTy :=")
    lines.append(f"  fun {lam} => {fn}_M_loop_aux {tup}.")
    lines.append("")

    # loop_before: Parameter (maps Require vars to initial invariant state)
    m_curried = _curried_args(req_types)
    lines.append(f"Parameter {fn}_M_loop_before : {m_curried}MONAD {st}.")
    lines.append("")

    # M: concrete composition of loop_before → loop → loop_end
    m_lam = _lambda_vars(m)
    lines.append(f"Definition {fn}_M : {m_curried}MONAD ({ret}) :=")
    lines.append(f"  fun {m_lam} =>")
    lines.append(f"    s0 <- {fn}_M_loop_before {m_lam};;")
    lines.append(f"    r <- {fn}_M_loop_aux s0;;")
    lines.append(f"    {fn}_M_loop_end r.")
    lines.append("")

    return "\n".join(lines)


def _collect_func_info_with_guard(func_data: Dict) -> Optional[Dict]:
    """Like collect_func_extern_info but also extracts coq_guard."""
    info = collect_func_extern_info(func_data)
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


def generate_rel_lib(basename: str, func_infos: List[Dict]) -> str:
    """Generate a complete _rel_lib.v skeleton file.

    Args:
        basename: e.g. "sll_copy" (without _rel_lib suffix)
        func_infos: list of dicts with func_name, require_var_count, inv_var_count, coq_guard
    """
    parts = []
    parts.append(COQ_IMPORTS)
    parts.append("")
    if any(info.get('ensure_var_count', 1) > 1 for info in func_infos):
        parts.append("Definition maketuple {A B} (a : A) (b : B) : (A * B) := (a, b).")
        parts.append("")
    parts.append("Parameter MretTy : Type.")
    parts.append("")

    for info in func_infos:
        parts.append(generate_func_block(
            info['func_name'],
            info['require_var_count'],
            info['inv_var_count'],
            info.get('ensure_var_count', 1),
            info.get('require_var_types'),
            info.get('inv_var_types'),
            info.get('ensure_var_types'),
            info.get('coq_guard'),
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
    if 'functions' in result and result['functions']:
        for func_data in result['functions']:
            info = _collect_func_info_with_guard(func_data)
            if info:
                func_infos.append(info)
    else:
        info = _collect_func_info_with_guard(result)
        if info:
            func_infos.append(info)

    if not func_infos:
        print(f"No functions with loop invariants found in {input_path}")
        return None

    src_basename = os.path.splitext(os.path.basename(input_path))[0]
    content = generate_rel_lib(src_basename, func_infos)

    os.makedirs(output_dir, exist_ok=True)
    out_path = os.path.join(output_dir, f"{src_basename}_rel_lib.v")
    with open(out_path, 'w', encoding='utf-8') as f:
        f.write(content)

    return out_path
