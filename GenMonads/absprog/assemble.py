import os
import re
from typing import Dict, List, Optional

from GenMonads.absprog.gen_rel_lib import (
    _collect_cross_file_callees,
    _collect_func_info_with_guard,
    _extract_function_source,
    collect_early_return_shape_for_function,
    generate_rel_lib,
)
from GenMonads.transshape.process_and_translate import process_and_translate_file
from GenMonads.translate_c_file import collect_callee_functions


def generate_rel_lib_skeleton_for_file(
    input_path: str,
    sibling_dirs: Optional[List[str]] = None,
    monad: str = "staterel",
    coq_lib_dir: Optional[str] = None,
) -> str:
    result = process_and_translate_file(input_path, generate_guards=True)
    if "error" in result:
        raise ValueError(result["error"])

    func_infos: List[Dict] = []
    with open(input_path, "r", encoding="utf-8") as f:
        content = f.read()

    def _safe_func_source(fn_name: str) -> Optional[str]:
        if not fn_name:
            return None
        try:
            return _extract_function_source(content, fn_name)
        except ValueError:
            return None

    if result.get("functions"):
        for func_data in result["functions"]:
            # Include any function with a funcspec: loop-bearing functions
            # get the full scaffold, no-loop functions get either the
            # early-return split or a single opaque Parameter declaration.
            include_helpers = not func_data.get("inner_assertions")
            func_source = _safe_func_source(func_data.get("function", ""))
            info = _collect_func_info_with_guard(
                func_data, include_helpers=include_helpers, c_source=func_source,
            )
            if info:
                info.update(collect_early_return_shape_for_function(content, info["func_name"]))
                func_infos.append(info)
    else:
        include_helpers = not result.get("inner_assertions")
        func_source = _safe_func_source(result.get("function", ""))
        info = _collect_func_info_with_guard(
            result, include_helpers=include_helpers, c_source=func_source,
        )
        if info:
            info.update(collect_early_return_shape_for_function(content, info["func_name"]))
            func_infos.append(info)

    if not func_infos:
        raise ValueError(f"No abstract program signatures found in {input_path}")

    func_names = [info["func_name"] for info in func_infos]
    imported_rel_libs = _collect_cross_file_callees(
        input_path, func_names, content, sibling_dirs=sibling_dirs
    )
    from GenMonads.absprog.gen_rel_lib import _build_in_file_call_graph
    call_graph = _build_in_file_call_graph(content, func_names)

    basename = os.path.splitext(os.path.basename(input_path))[0]
    return generate_rel_lib(
        basename, func_infos, imported_rel_libs, call_graph,
        monad=monad, coq_lib_dir=coq_lib_dir,
    )


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
    "guardP": "guardP",
}


def assemble_rel_lib_from_blocks(
    c_file: str,
    func_name: str,
    blocks: Dict[str, str],
    sibling_dirs: Optional[List[str]] = None,
    monad: str = "staterel",
    coq_lib_dir: Optional[str] = None,
) -> str:
    """Substitute LLM-provided Definitions into the rel_lib skeleton.

    Recognized keys in *blocks* (only those present are substituted):
    - ``MretTy``
    - ``M_loop_before``, ``M_1``, ``M_2``, ``M_loop_end`` (loop scaffold)
    - ``M_before``, ``M_normal`` (no-loop early-return scaffold)
    - ``M`` (no-loop straight-line scaffold; replaces ``Parameter {fn}_M``)
    """
    content = generate_rel_lib_skeleton_for_file(
        c_file, sibling_dirs=sibling_dirs, monad=monad, coq_lib_dir=coq_lib_dir,
    )

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

    for component, block in blocks.items():
        if component == "MretTy" or not block:
            continue
        # Known single-loop / no-loop components have a fixed suffix mapping;
        # forest components (``M_loop2_M1``, ``loop1_guardP``,
        # ``M_loop1_to_inner_2``, …) are loop-indexed and pass through
        # verbatim — the LLM's Definition uses the same name as the skeleton's
        # Parameter so the replacement is a direct lookup.
        suffix = _COMPONENT_PARAMETER_NAME.get(component, component)
        renamed = _rename_mretty(block, mretty_name)
        content = _replace_parameter_with_definition(
            content, f"{func_name}_{suffix}", renamed
        )
    return content


def write_assembled_rel_lib(
    c_file: str, func_name: str, blocks: Dict[str, str], output_path: str,
    sibling_dirs: Optional[List[str]] = None,
    monad: str = "staterel",
) -> str:
    content = assemble_rel_lib_from_blocks(
        c_file, func_name, blocks, sibling_dirs=sibling_dirs, monad=monad
    )
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
    # Loop scaffold (the common case)
    "_M_loop_before",
    "_M_loop_M1",
    "_M_loop_M2",
    "_M_loop_end",
    # Option C no-loop early-return scaffold
    "_M_before",
    "_M_normal",
    # LLM-synthesized loop guard (when GuardGen could not produce one)
    "_guardP",
    # Straight-line function: single `Parameter {fn}_M` to fill in
    "_M",
)


# Forest scaffold (task #20) — loop-indexed components.  Names like
# ``f_M_loop1_M1``, ``f_M_loop2_to_inner_2``, ``f_loop1_guardP`` are
# recognised by suffix pattern instead of an exact literal.
_LLM_PARAMETER_SUFFIX_PATTERNS = (
    re.compile(r"_M_loop\d+_M[12]$"),
    re.compile(r"_M_loop\d+_(before|end)$"),
    re.compile(r"_M_loop\d+_(to_inner|after_inner)_\d+$"),
    re.compile(r"_loop\d+_guardP$"),
    re.compile(r"_loop\d+_ResTy$"),
)


def _is_llm_parameter_name(name: str) -> bool:
    if any(name.endswith(suffix) for suffix in _LLM_PARAMETER_SUFFIXES):
        return True
    return any(pat.search(name) for pat in _LLM_PARAMETER_SUFFIX_PATTERNS)


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
    """Return {name: block_text} for LLM-replaceable Definitions (M_loop_*
    and forest-scaffold ``M_loop\\d+_*`` / ``loop\\d+_guardP`` / ``ResTy``)."""
    result: Dict[str, str] = {}
    for kind, name, block in _iter_top_level_blocks(content):
        if kind != "Definition":
            continue
        if not _is_llm_parameter_name(name):
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
    sibling_dirs: Optional[List[str]] = None,
    monad: str = "staterel",
    coq_lib_dir: Optional[str] = None,
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

    merged = generate_rel_lib_skeleton_for_file(
        c_file, sibling_dirs=sibling_dirs, monad=monad, coq_lib_dir=coq_lib_dir,
    )

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

        # Only rename to the per-function scoped form when the skeleton
        # actually uses it.  Single-MretTy-user files keep the bare `MretTy`
        # name (the skeleton emits `Parameter MretTy : Type.`), so renaming
        # substituted definitions to `{owning}_MretTy` would introduce an
        # undeclared identifier.
        if owning:
            scoped_token = f"{owning}_MretTy"
            if re.search(
                rf"Parameter\s+{re.escape(scoped_token)}\s*:\s*Type\b",
                merged,
            ):
                scoped_mretty = scoped_token
            else:
                scoped_mretty = "MretTy"
        else:
            scoped_mretty = "MretTy"

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
