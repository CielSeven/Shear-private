import json
import os
import re
from typing import Dict, List, Optional

from GenMonads.absprog.context import collect_synthesis_context


def _extract_definition_block(coq_source: str, name: str) -> str:
    lines = coq_source.splitlines()
    start = None
    for idx, line in enumerate(lines):
        if line.startswith(f"Definition {name} "):
            start = idx
            break

    if start is None:
        raise ValueError(f"Could not find Definition '{name}' in rel lib")

    block: List[str] = []
    for line in lines[start:]:
        block.append(line.rstrip())
        if line.strip().endswith("."):
            break
    else:
        raise ValueError(f"Definition '{name}' does not terminate with '.'")

    return "\n".join(block).strip()


def _extract_mretty(coq_source: str) -> str:
    match = re.search(r"^Definition MretTy : Type :=\s*(.+?)\.\s*$", coq_source, re.MULTILINE)
    if not match:
        raise ValueError("Could not extract MretTy from rel lib")
    return match.group(1).strip()


def build_auto_example(
    c_file: str,
    rel_lib_file: str,
    func_name: Optional[str] = None,
    verification_status: str = "unchecked",
    coqc_checked: bool = False,
) -> Dict:
    context = collect_synthesis_context(c_file, func_name=func_name)

    with open(rel_lib_file, "r", encoding="utf-8") as f:
        coq_source = f.read()

    func = context["summary"]["func_name"]
    example = dict(context)
    example["gold"] = {
        "rel_lib_file": rel_lib_file,
        "MretTy": _extract_mretty(coq_source),
        "components": {
            "M_loop_before": _extract_definition_block(
                coq_source, f"{func}_M_loop_before"
            ),
            "M_1": _extract_definition_block(
                coq_source, f"{func}_M_loop_M1"
            ),
            "M_2": _extract_definition_block(
                coq_source, f"{func}_M_loop_M2"
            ),
            "M_loop_end": _extract_definition_block(
                coq_source, f"{func}_M_loop_end"
            ),
        },
    }
    example["verification"] = {
        "coqc_checked": coqc_checked,
        "status": verification_status,
    }
    return example


def write_auto_example(
    c_file: str,
    rel_lib_file: str,
    output_path: str,
    func_name: Optional[str] = None,
    verification_status: str = "unchecked",
    coqc_checked: bool = False,
) -> Dict:
    example = build_auto_example(
        c_file,
        rel_lib_file,
        func_name=func_name,
        verification_status=verification_status,
        coqc_checked=coqc_checked,
    )

    os.makedirs(os.path.dirname(output_path), exist_ok=True)
    with open(output_path, "w", encoding="utf-8") as f:
        json.dump(example, f, indent=2)
        f.write("\n")

    return example
