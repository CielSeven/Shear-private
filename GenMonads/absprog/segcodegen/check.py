"""Optional Rocq type-check of a filled rel_lib (the ``--check`` flag).

Compiles the filled library with ``coqc`` against the project's Coq library
tree, first compiling any sibling ``*_rel_lib`` dependencies it ``Require``s.

This verifies the synthesized ``Definition``s are **well-typed Coq** (arities,
tuple shapes, notations, callee references, the ``repeat_break``/``choice``
scaffolding).  It does **not** prove the abstract program refines the data-VC —
that is the separate entailment-proof obligation.
"""

from __future__ import annotations

import os
import re
import shutil
import subprocess
from typing import Dict, List, Optional, Set

from ..check_rocq import _find_coq_project, _load_coq_flags
from ...cli_common import read_configure_value

_REQUIRE_RE = re.compile(r"^\s*Require\s+Import\s+([A-Za-z0-9_]+_rel_lib)\s*\.", re.M)


def _base_project(out_dir: str) -> Optional[str]:
    """Locate a ``_CoqProject`` for the library-tree (`-R`) flags."""
    root = _find_coq_project(out_dir)
    if root:
        return root
    lib_dir = read_configure_value("COQ_LIB_DIR")
    if lib_dir:
        for cand in (lib_dir, os.path.dirname(os.path.abspath(lib_dir))):
            if cand and os.path.isfile(os.path.join(cand, "_CoqProject")):
                return os.path.abspath(cand)
    return None


def _coqc(v_path: str, flags: List[str]) -> subprocess.CompletedProcess:
    return subprocess.run(["coqc", *flags, os.path.abspath(v_path)],
                          text=True, capture_output=True)


def _ensure_deps(v_path: str, out_dir: str, source_lib_dir: str,
                 flags: List[str], done: Set[str]) -> Optional[Dict]:
    """Compile (transitively) the ``*_rel_lib`` deps that *v_path* Requires,
    copying each from *source_lib_dir* into *out_dir* and building it there."""
    with open(v_path) as f:
        text = f.read()
    for dep in _REQUIRE_RE.findall(text):
        if dep in done:
            continue
        done.add(dep)
        src = os.path.join(source_lib_dir, dep + ".v")
        if not os.path.isfile(src):
            continue  # external lib already on the load path
        dst = os.path.join(out_dir, dep + ".v")
        if os.path.abspath(src) != os.path.abspath(dst):
            shutil.copyfile(src, dst)
        err = _ensure_deps(dst, out_dir, source_lib_dir, flags, done)
        if err:
            return err
        proc = _coqc(dst, flags)
        if proc.returncode != 0:
            return {"passed": False, "status": "dep-failed", "dep": dep,
                    "stderr": proc.stderr, "stdout": proc.stdout}
    return None


def check_lib(out_path: str, source_lib_dir: str,
              coq_project: Optional[str] = None) -> Dict:
    """Type-check the filled lib at *out_path*; *source_lib_dir* holds the
    sibling ``*_rel_lib.v`` dependencies (usually the template's directory)."""
    if not shutil.which("coqc"):
        return {"passed": False, "status": "skipped", "reason": "coqc not found"}
    out_dir = os.path.dirname(os.path.abspath(out_path)) or "."
    root: Optional[str] = None
    if coq_project:
        root = (coq_project if os.path.isdir(coq_project)
                else os.path.dirname(os.path.abspath(coq_project)))
    root = root or _base_project(out_dir)
    if not root:
        return {"passed": False, "status": "skipped", "reason": "_CoqProject not found"}

    flags = _load_coq_flags(root) + ["-Q", os.path.abspath(out_dir), ""]
    err = _ensure_deps(out_path, out_dir, source_lib_dir, flags, set())
    if err:
        return err
    proc = _coqc(out_path, flags)
    return {
        "passed": proc.returncode == 0,
        "status": "passed" if proc.returncode == 0 else "failed",
        "stderr": proc.stderr,
        "stdout": proc.stdout,
        "project_root": root,
    }
