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


def _state_type(k: int) -> str:
    """Build the state type for k invariant list variables.

    k=1: list Z
    k=2: (list Z * list Z)
    k=3: (list Z * list Z * list Z)
    """
    if k == 1:
        return "list Z"
    return "(" + " * ".join(["list Z"] * k) + ")"


def _curried_args(n: int) -> str:
    """Build curried argument types: list Z -> list Z -> ... ->"""
    if n == 0:
        return ""
    return " -> ".join(["list Z"] * n) + " -> "


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
                        coq_guard: Optional[str] = None) -> str:
    """Generate the abstract program skeleton for one function."""
    fn = func_name
    k = inv_var_count
    m = require_var_count
    st = _state_type(k)
    ret = _state_type(ensure_var_count) if ensure_var_count > 1 else "list Z"
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
    curried = _curried_args(k)
    lines.append(f"Definition {fn}_M_loop : {curried}program unit MretTy :=")
    lines.append(f"  fun {lam} => {fn}_M_loop_aux {tup}.")
    lines.append("")

    # loop_before: Parameter (maps Require vars to initial invariant state)
    m_curried = _curried_args(m)
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
