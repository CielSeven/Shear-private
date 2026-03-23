import os
import re
from typing import Dict, List, Optional

from GenMonads.absprog.gen_rel_lib import generate_rel_lib
from GenMonads.transshape.process_and_translate import process_and_translate_file
from GenMonads.translate_c_file import collect_func_extern_info


def _collect_func_info_with_guard(func_data: Dict) -> Optional[Dict]:
    info = collect_func_extern_info(func_data)
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
    if result.get("functions"):
        for func_data in result["functions"]:
            info = _collect_func_info_with_guard(func_data)
            if info:
                func_infos.append(info)
    else:
        info = _collect_func_info_with_guard(result)
        if info:
            func_infos.append(info)

    if not func_infos:
        raise ValueError(f"No functions with loop invariants found in {input_path}")

    basename = os.path.splitext(os.path.basename(input_path))[0]
    return generate_rel_lib(basename, func_infos)


def _replace_parameter_with_definition(content: str, parameter_name: str, definition: str) -> str:
    pattern = re.compile(rf"^Parameter {re.escape(parameter_name)} : [^\n]+\.$", re.MULTILINE)
    new_content, count = pattern.subn(definition, content, count=1)
    if count != 1:
        raise ValueError(f"Could not replace Parameter '{parameter_name}' in skeleton")
    return new_content


def _replace_mretty(content: str, definition: str) -> str:
    pattern = re.compile(r"^Parameter MretTy : Type\.$", re.MULTILINE)
    new_content, count = pattern.subn(definition, content, count=1)
    if count != 1:
        raise ValueError("Could not replace Parameter 'MretTy' in skeleton")
    return new_content


def assemble_rel_lib_from_blocks(c_file: str, func_name: str, blocks: Dict[str, str]) -> str:
    content = generate_rel_lib_skeleton_for_file(c_file)
    content = _replace_mretty(content, blocks["MretTy"])
    content = _replace_parameter_with_definition(
        content, f"{func_name}_M_loop_before", blocks["M_loop_before"]
    )
    content = _replace_parameter_with_definition(
        content, f"{func_name}_M_loop_M1", blocks["M_1"]
    )
    content = _replace_parameter_with_definition(
        content, f"{func_name}_M_loop_M2", blocks["M_2"]
    )
    content = _replace_parameter_with_definition(
        content, f"{func_name}_M_loop_end", blocks["M_loop_end"]
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
