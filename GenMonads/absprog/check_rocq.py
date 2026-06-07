import os
import shlex
import shutil
import subprocess
from typing import Dict, List, Optional, Tuple


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


def parse_coq_project_mappings(coq_project_path: str) -> List[Tuple[str, str]]:
    """Return ``[(physical_path, logical_prefix), ...]`` from each ``-Q`` /
    ``-R`` line in *coq_project_path*.

    Empty logical prefixes (``-Q DIR ""``) come through as the empty string;
    the caller decides how to fold them into a logical name (the convention
    here: skip the prefix segment when concatenating).
    """
    mappings: List[Tuple[str, str]] = []
    try:
        with open(coq_project_path, "r", encoding="utf-8") as f:
            content = f.read()
    except OSError:
        return mappings
    for line in content.splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        tokens = shlex.split(line)
        if len(tokens) < 3 or tokens[0] not in ("-Q", "-R"):
            continue
        physical = os.path.abspath(tokens[1])
        logical = tokens[2]
        mappings.append((physical, logical))
    return mappings


def resolve_lib_logical_path(
    coq_project_path: str, lib_file_path: str,
) -> Optional[str]:
    """Compute the canonical Coq logical path for *lib_file_path* under the
    ``-Q`` / ``-R`` mappings declared in *coq_project_path*.

    Picks the longest matching physical-path prefix (most specific binding),
    computes the relative path from that physical root to *lib_file_path*,
    and joins ``<logical_prefix>.<relative_dirs_with_dots>.<basename>``
    (skipping any empty segment).  Returns ``None`` when no mapping covers
    the file — the caller decides what to do with bare-name fallback.

    Examples (with ``-R /a/b/c LIB``):

    * ``/a/b/c/sub/foo_rel_lib.v`` → ``LIB.sub.foo_rel_lib``
    * ``/a/b/c/foo_rel_lib.v``    → ``LIB.foo_rel_lib``

    With ``-Q /a/b/c ""``:

    * ``/a/b/c/sub/foo_rel_lib.v`` → ``sub.foo_rel_lib``
    * ``/a/b/c/foo_rel_lib.v``    → ``foo_rel_lib``
    """
    mappings = parse_coq_project_mappings(coq_project_path)
    if not mappings:
        return None
    abs_file = os.path.abspath(lib_file_path)

    # Longest physical-path prefix wins.  ``os.path.commonpath`` enforces a
    # directory-boundary match — ``/foo/bar`` does NOT match
    # ``/foo/barbaz/...``, which a naive ``startswith`` would accept.
    candidates: List[Tuple[str, str]] = []
    for physical, logical in mappings:
        try:
            common = os.path.commonpath([physical, abs_file])
        except ValueError:
            continue
        if common != physical:
            continue
        candidates.append((physical, logical))
    if not candidates:
        return None
    candidates.sort(key=lambda pl: len(pl[0]), reverse=True)
    physical, logical = candidates[0]

    rel = os.path.relpath(abs_file, physical)
    base_dir, fname = os.path.split(rel)
    stem, _ext = os.path.splitext(fname)

    parts: List[str] = []
    if logical:
        parts.extend(logical.split("."))  # honor pre-dotted prefixes
    if base_dir and base_dir not in (".", ""):
        parts.extend(p for p in base_dir.split(os.sep) if p)
    parts.append(stem)
    return ".".join(parts)


def qualified_require_import_for_callee(
    callee_name: str,
    coq_lib_dir: Optional[str],
    coq_project_path: Optional[str] = None,
) -> str:
    """Return the ``Require Import`` token used in skeleton emission for a
    cross-file callee.  When *coq_lib_dir* and a discoverable ``_CoqProject``
    let us compute the canonical logical name, we return the qualified form;
    otherwise we fall back to the bare ``{callee_name}_rel_lib`` (current
    behaviour for callers that don't know the lib dir).
    """
    bare = f"{callee_name}_rel_lib"
    if not coq_lib_dir:
        return bare
    project_path = coq_project_path
    if project_path is None:
        project_root = _find_coq_project(coq_lib_dir)
        if not project_root:
            return bare
        project_path = os.path.join(project_root, "_CoqProject")
    lib_file = os.path.join(coq_lib_dir, f"{bare}.v")
    qualified = resolve_lib_logical_path(project_path, lib_file)
    return qualified or bare


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
