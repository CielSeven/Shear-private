import re
from typing import Dict, List


def _extract_definition_block(coq_source: str, name: str) -> str:
    lines = coq_source.splitlines()
    start = None
    for idx, line in enumerate(lines):
        if re.match(rf"^Definition {re.escape(name)}\b", line):
            start = idx
            break

    if start is None:
        raise ValueError(f"Could not find Definition '{name}' in response")

    block: List[str] = []
    for line in lines[start:]:
        block.append(line.rstrip())
        if line.strip().endswith("."):
            break
    else:
        raise ValueError(f"Definition '{name}' does not terminate with '.'")

    return "\n".join(block).strip()


def parse_synthesized_components(response_text: str, func_name: str) -> Dict[str, str]:
    return {
        "MretTy": _extract_definition_block(response_text, "MretTy"),
        "M_loop_before": _extract_definition_block(response_text, f"{func_name}_M_loop_before"),
        "M_1": _extract_definition_block(response_text, f"{func_name}_M_loop_M1"),
        "M_2": _extract_definition_block(response_text, f"{func_name}_M_loop_M2"),
        "M_loop_end": _extract_definition_block(response_text, f"{func_name}_M_loop_end"),
    }
