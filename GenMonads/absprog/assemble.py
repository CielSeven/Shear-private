import os
import re
from typing import Dict, List, Optional

from GenMonads.absprog.gen_rel_lib import (
    _collect_cross_file_callees,
    collect_early_return_shape_for_function,
    generate_rel_lib,
)
from GenMonads.transshape.process_and_translate import process_and_translate_file
from GenMonads.translate_c_file import collect_callee_functions, collect_func_extern_info


def _collect_func_info_with_guard(func_data: Dict, include_helpers: bool = False) -> Optional[Dict]:
    info = collect_func_extern_info(func_data, include_helpers=include_helpers)
    if info is None:
        return None

    inner = func_data.get("inner_assertions", [])
    inv_assertions = [a for a in inner if a.get("type") == "Inv" and "variables" in a]
    coq_guard = None
    for assertion in inv_assertions:
        if "coq_guard" in assertion:
            coq_guard = assertion["coq_guard"]
            break
    info["coq_guard"] = coq_guard
    return info


def generate_rel_lib_skeleton_for_file(input_path: str) -> str:
    result = process_and_translate_file(input_path, generate_guards=True)
    if "error" in result:
        raise ValueError(result["error"])

    func_infos: List[Dict] = []
    with open(input_path, "r", encoding="utf-8") as f:
        content = f.read()
    if result.get("functions"):
        for func_data in result["functions"]:
            # Include any function with a funcspec: loop-bearing functions
            # get the full scaffold, no-loop functions get either the
            # early-return split or a single opaque Parameter declaration.
            include_helpers = not func_data.get("inner_assertions")
            info = _collect_func_info_with_guard(func_data, include_helpers=include_helpers)
            if info:
                info.update(collect_early_return_shape_for_function(content, info["func_name"]))
                func_infos.append(info)
    else:
        include_helpers = not result.get("inner_assertions")
        info = _collect_func_info_with_guard(result, include_helpers=include_helpers)
        if info:
            info.update(collect_early_return_shape_for_function(content, info["func_name"]))
            func_infos.append(info)

    if not func_infos:
        raise ValueError(f"No abstract program signatures found in {input_path}")

    func_names = [info["func_name"] for info in func_infos]
    imported_rel_libs = _collect_cross_file_callees(input_path, func_names, content)

    basename = os.path.splitext(os.path.basename(input_path))[0]
    return generate_rel_lib(basename, func_infos, imported_rel_libs)


def _replace_parameter_with_definition(content: str, parameter_name: str, definition: str) -> str:
    pattern = re.compile(rf"^Parameter {re.escape(parameter_name)} : [^\n]+\.$", re.MULTILINE)
    new_content, count = pattern.subn(definition, content, count=1)
    if count != 1:
        raise ValueError(f"Could not replace Parameter '{parameter_name}' in skeleton")
    return new_content


def _replace_mretty(content: str, definition: str, mretty_name: str = "MretTy") -> str:
    pattern = re.compile(
        rf"^Parameter {re.escape(mretty_name)} : Type\.$", re.MULTILINE
    )
    new_content, count = pattern.subn(definition, content, count=1)
    if count != 1:
        raise ValueError(f"Could not replace Parameter '{mretty_name}' in skeleton")
    return new_content


def _rename_mretty(text: str, new_name: str) -> str:
    """Rename the identifier ``MretTy`` (whole word) to *new_name*."""
    if new_name == "MretTy":
        return text
    return re.sub(r"\bMretTy\b", new_name, text)


_COMPONENT_PARAMETER_NAME = {
    "M_loop_before": "M_loop_before",
    "M_1": "M_loop_M1",
    "M_2": "M_loop_M2",
    "M_loop_end": "M_loop_end",
    "M_before": "M_before",
    "M_normal": "M_normal",
    "M": "M",
}


def assemble_rel_lib_from_blocks(c_file: str, func_name: str, blocks: Dict[str, str]) -> str:
    """Substitute LLM-provided Definitions into the rel_lib skeleton.

    Recognized keys in *blocks* (only those present are substituted):
    - ``MretTy``
    - ``M_loop_before``, ``M_1``, ``M_2``, ``M_loop_end`` (loop scaffold)
    - ``M_before``, ``M_normal`` (no-loop early-return scaffold)
    - ``M`` (no-loop straight-line scaffold; replaces ``Parameter {fn}_M``)
    """
    content = generate_rel_lib_skeleton_for_file(c_file)

    # Determine the MretTy name used by the skeleton for this function.
    # Multi-function skeletons use a scoped `{func}_MretTy`; single-function
    # skeletons keep the shared `MretTy` parameter for backward compatibility.
    scoped_name = f"{func_name}_MretTy"
    if re.search(rf"^Parameter {re.escape(scoped_name)} : Type\.$", content, re.MULTILINE):
        mretty_name = scoped_name
    else:
        mretty_name = "MretTy"

    if blocks.get("MretTy"):
        mretty_block = _rename_mretty(blocks["MretTy"], mretty_name)
        mretty_block = re.sub(
            r"\bDefinition MretTy\b", f"Definition {mretty_name}", mretty_block, count=1
        )
        content = _replace_mretty(content, mretty_block, mretty_name=mretty_name)

    for component, suffix in _COMPONENT_PARAMETER_NAME.items():
        block = blocks.get(component)
        if not block:
            continue
        renamed = _rename_mretty(block, mretty_name)
        content = _replace_parameter_with_definition(
            content, f"{func_name}_{suffix}", renamed
        )
    return content


def write_assembled_rel_lib(
    c_file: str, func_name: str, blocks: Dict[str, str], output_path: str
) -> str:
    content = assemble_rel_lib_from_blocks(c_file, func_name, blocks)
    output_dir = os.path.dirname(output_path)
    if output_dir:
        os.makedirs(output_dir, exist_ok=True)
    with open(output_path, "w", encoding="utf-8") as f:
        f.write(content)
    return output_path


# ---------------------------------------------------------------------------
# Merging per-function synthesis outputs into a single multi-function lib file.
# ---------------------------------------------------------------------------

_LLM_PARAMETER_SUFFIXES = (
    "_M_loop_before",
    "_M_loop_M1",
    "_M_loop_M2",
    "_M_loop_end",
)


_TOP_LEVEL_START_RE = re.compile(
    r"^(Definition|Parameter|Inductive|Fixpoint|Lemma|Theorem|Arguments|Notation|Require|From|Import|Export|Local|Open|Close|Reserved|Record|Structure|Class|Instance|Variable|Variables|Hypothesis|End|Section)\b",
    re.MULTILINE,
)


def _iter_top_level_blocks(content: str):
    """Yield (header_kind, name, block_text) for each top-level Coq statement.

    Blocks are delimited by the start of the next top-level keyword (handles
    back-to-back Definitions without blank lines between them) or end of file.
    """
    starts = list(_TOP_LEVEL_START_RE.finditer(content))
    for i, match in enumerate(starts):
        start = match.start()
        end = starts[i + 1].start() if i + 1 < len(starts) else len(content)
        block = content[start:end].rstrip()
        if not block:
            continue
        name_match = re.match(r"(\w+)\s+(\w+)", block)
        name = name_match.group(2) if name_match else ""
        yield match.group(1), name, block


def _extract_mretty_definitions(content: str) -> Dict[str, str]:
    """Return {name: block_text} for every ``Definition <name> : Type := ...``
    where ``<name>`` is ``MretTy`` or ends with ``_MretTy``.
    """
    result: Dict[str, str] = {}
    for kind, name, block in _iter_top_level_blocks(content):
        if kind != "Definition":
            continue
        if name == "MretTy" or name.endswith("_MretTy"):
            result[name] = block
    return result


def _extract_llm_definitions(content: str) -> Dict[str, str]:
    """Return {name: block_text} for LLM-replaceable Definitions (M_loop_*)."""
    result: Dict[str, str] = {}
    for kind, name, block in _iter_top_level_blocks(content):
        if kind != "Definition":
            continue
        if not any(name.endswith(suffix) for suffix in _LLM_PARAMETER_SUFFIXES):
            continue
        result[name] = block
    return result


def _owning_function(name: str, func_names: List[str]) -> Optional[str]:
    """Return the function name in *func_names* that owns identifier *name*."""
    best = None
    for func in func_names:
        if name.startswith(f"{func}_") and (best is None or len(func) > len(best)):
            best = func
    return best


def merge_rel_libs_into_file(
    c_file: str,
    per_function_assembled_paths: List[str],
    output_path: str,
) -> str:
    """Merge per-function assembled lib files into one multi-function file.

    Builds a fresh multi-function skeleton (each function already has its
    own ``{func}_MretTy`` for multi-function files), then substitutes in
    each function's LLM-provided Definitions from its per-function file.

    For robustness the merger also renames any unscoped ``MretTy`` in the
    extracted Definitions to ``{func}_MretTy`` (handles older per-function
    files assembled before skeleton scoping was introduced).
    """
    if not per_function_assembled_paths:
        raise ValueError("No per-function assembled lib files to merge")

    merged = generate_rel_lib_skeleton_for_file(c_file)

    # Gather function names from the skeleton by scanning its section headers.
    func_names = re.findall(
        r"^\(\* ---- Abstract program segments for (\w+) ---- \*\)$",
        merged,
        re.MULTILINE,
    )

    for path in per_function_assembled_paths:
        if not path or not os.path.isfile(path):
            continue
        with open(path, "r", encoding="utf-8") as f:
            content = f.read()

        # Determine which function this file belongs to by inspecting one of
        # its Definitions' prefix (e.g. sll_rotate_left_M_loop_M1 → sll_rotate_left).
        definitions = _extract_llm_definitions(content)
        owning = None
        for def_name in definitions:
            owning = _owning_function(def_name, func_names)
            if owning:
                break

        scoped_mretty = f"{owning}_MretTy" if owning else "MretTy"

        for name, definition in definitions.items():
            substituted = _rename_mretty(definition, scoped_mretty)
            try:
                merged = _replace_parameter_with_definition(merged, name, substituted)
            except ValueError:
                continue

        mretty_defs = _extract_mretty_definitions(content)
        for name, definition in mretty_defs.items():
            # If the file's MretTy is unscoped but the skeleton expects
            # a scoped name, rewrite the Definition's name + body references.
            if name == "MretTy" and owning and scoped_mretty != "MretTy":
                definition = re.sub(
                    r"^Definition MretTy\b",
                    f"Definition {scoped_mretty}",
                    definition,
                    count=1,
                )
                substituted_name = scoped_mretty
            else:
                substituted_name = name
            try:
                merged = _replace_parameter_with_definition(
                    merged, substituted_name, definition
                )
            except ValueError:
                continue

    output_dir = os.path.dirname(output_path)
    if output_dir:
        os.makedirs(output_dir, exist_ok=True)
    with open(output_path, "w", encoding="utf-8") as f:
        f.write(merged)
    return output_path
