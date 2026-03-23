import os
import shlex
import shutil
import subprocess
from typing import Dict, List, Optional


def _find_coq_project(start_dir: str) -> Optional[str]:
    current = os.path.abspath(start_dir)
    while True:
        if os.path.isfile(os.path.join(current, "_CoqProject")):
            return current
        parent = os.path.dirname(current)
        if parent == current:
            return None
        current = parent


def _load_coq_flags(project_root: str) -> List[str]:
    flags: List[str] = []
    coq_project = os.path.join(project_root, "_CoqProject")
    with open(coq_project, "r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            flags.extend(shlex.split(line))
    return flags


def check_rocq_file(file_path: str) -> Dict:
    coqc = shutil.which("coqc")
    if not coqc:
        return {
            "status": "skipped",
            "passed": False,
            "reason": "coqc not found",
            "stdout": "",
            "stderr": "",
        }

    project_root = _find_coq_project(os.path.dirname(file_path))
    if not project_root:
        return {
            "status": "skipped",
            "passed": False,
            "reason": "_CoqProject not found",
            "stdout": "",
            "stderr": "",
        }

    flags = _load_coq_flags(project_root)
    proc = subprocess.run(
        [coqc, *flags, os.path.abspath(file_path)],
        cwd=project_root,
        text=True,
        capture_output=True,
    )
    return {
        "status": "passed" if proc.returncode == 0 else "failed",
        "passed": proc.returncode == 0,
        "reason": "",
        "stdout": proc.stdout,
        "stderr": proc.stderr,
        "returncode": proc.returncode,
        "project_root": project_root,
    }
