"""Workdir-mode synthesis backend support.

The synthesis pipeline used to invoke ``codex exec`` from the project root
with no working-directory isolation, no sandbox, and no contract between
what the agent could write and what we expected.  Workdir mode replaces
that with a per-function curated directory:

    output/gen/synth/<basename>/<func>/workdir/
    ├── AGENTS.md                    (rules + framework cheatsheet; static)
    ├── skeleton/
    │   └── {basename}_rel_lib.v     (writable — the agent edits this in place)
    ├── _CoqProject                  (read-only — points coqc at the
    │                                 project's external lib paths plus
    │                                 the existing output/gen/libs)
    └── out/
        └── transcript.txt           (codex --output-last-message lands here)

``codex exec -C <workdir>`` runs the agent with CWD = workdir, sandboxed to
``workspace-write`` so writes are confined to the workdir.  Reads outside
the workdir are allowed (necessary for coqc to resolve framework libs and
already-synthesized callee libs at the absolute paths in ``_CoqProject``).

Pre-spawn checks (hard errors) — :func:`check_prerequisites`:

* ``_CoqProject`` must exist somewhere in the project tree.
* Every ``Require Import {callee}_rel_lib`` referenced by the skeleton
  must have a corresponding file in ``COQ_LIB_DIR`` (already synthesized
  by an earlier topological-order pass).

Post-run checks — :func:`validate_workdir_filesystem` (Layer 2) and
:func:`validate_skeleton_diff` (Layer 3) — enforce the agent's contract.
"""

from __future__ import annotations

import hashlib
import os
import re
import shutil
from typing import Dict, List, Optional, Set, Tuple


# ---------------------------------------------------------------------------
# AGENTS.md template — the agent's operating manual + framework cheatsheet.
# Static across functions; only ``{basename}`` and ``{func_name}`` substituted.


_AGENTS_MD_TEMPLATE = """\
# Codex Agent — Coq Refinement Lib Synthesis

You are generating Coq monadic abstract programs for refinement-based formal
verification of C programs.  Your job in this workdir is to fill in the
``Parameter`` placeholders in ``skeleton/{basename}_rel_lib.v`` with concrete
``Definition``s that simulate the C function and pass type-checking.

## A2 — File-system contract

* Edit ONLY ``skeleton/{basename}_rel_lib.v``.  Do not create, rename, or
  delete any other file in this workdir.  (Compiled artifacts written by
  ``coqc`` — ``.vo``, ``.vok``, ``.vos``, ``.glob``, ``.aux`` — and codex's
  own ``.codex/`` directory are tolerated.)
* Your last message becomes ``out/transcript.txt``; keep it short and
  factual.

## A3 — Verification

{verification_section}

## A4 — Replacement contract (STRICT)

The skeleton already contains the complete library structure.  The only
edits you may make:

1. Replace each ``Parameter X : T.`` whose name ``X`` appears in the task's
   ``must_define`` list with a single ``Definition X : T := <body>.``  The
   declared type ``T`` must remain **exactly** as written in the skeleton.
2. Nothing else.  Imports, concrete ``Definition``s already in the
   skeleton (``_M_loop_body``, ``_M_loop_aux``, the mechanical
   ``_M_loop{{k}}_M2``, the top-level ``{{fn}}_M`` composition, etc.) must
   stay byte-identical.

A post-run validator computes a structural diff between the skeleton and
your output.  Foreign edits — even adding a blank line in the wrong place
— cause the attempt to be rejected.

## A5 — QCP Monad primitives

* ``return v`` / ``ret v`` — monadic return.
* ``bind m f`` / ``m >>= f`` — sequence m then f.
* ``assume!! P`` — lift a pure Coq proposition ``P : Prop`` into the
  monadic assumption form.  Use for branch conditions and pure facts such
  as ``x <= y``, ``l = nil``, guard checks.
* ``assume P`` — use only when ``P`` is already in the library's expected
  state-predicate form.  Prefer ``assume!!`` for synthesis tasks.
* ``any A`` — return an arbitrary value of type ``A``.
* ``choice m1 m2`` — nondeterministic branching (the two branches of the
  loop body's break/continue split).
* ``repeat_break`` — loop construct already used by ``_M_loop_aux``.
* List operations: ``app`` / ``++``, ``cons`` / ``::``, ``nil``, ``length``.

## A6 — Style rules

* Use plain ``return EXPR`` for monadic returns; NEVER ``@ret _ T x`` with
  placeholder underscores (Coq cannot infer MONAD's implicit args).
* Destructure state tuples with ``fun a => let '(...) := a in ...``.
* Do not introduce ``Definition``s of names that shadow existing
  top-level identifiers (Coq will reject the duplicate).

## A7 — Naming conventions

* ``MretTy`` is a ``Parameter`` type the LLM defines once per function.
* Single-loop scaffold names: ``{{fn}}_M_loop_before``, ``{{fn}}_M_loop_M1``,
  ``{{fn}}_M_loop_M2``, ``{{fn}}_M_loop_end``, ``{{fn}}_guardP``.
* Forest scaffold (multi-loop) names: ``{{fn}}_M_loop{{k}}_M1``,
  ``{{fn}}_M_loop{{k}}_before`` / ``_end`` (top-level loops only),
  ``{{fn}}_M_loop{{k}}_to_inner_{{c}}`` / ``_after_inner_{{c}}`` (parent
  loops; per child ``c``), ``{{fn}}_loop{{k}}_guardP``.

## A8 — Forest mechanics

A "forest" lib has multiple ``while`` loops.  Each loop has its own
scaffold block.  For a PARENT loop, the skeleton already contains a
``Definition {{fn}}_M_loop{{k}}_M2`` that mechanically sequences
``to_inner_{{c}}``, the child's ``_aux``, and ``after_inner_{{c}}``.  Do
not redefine it.  Your job for parent loops is the ``M1`` exit step plus
the ``to_inner_{{c}}`` (outer state → inner init state) and
``after_inner_{{c}}`` (outer state + inner break-value → next outer state)
holes per child.  LEAF loops require ``M1`` (exit) and ``M2`` (step);
no ``to_inner``/``after_inner``.

## A9 — Guard signature rule

Any ``loop{{k}}_guardP`` or ``guardP`` ``Definition`` you provide must use
the signature exactly as declared in the skeleton's ``Parameter`` line.
The post-run validator rejects changed guard signatures because the
pre-generated ``_M_loop_body`` scaffolding applies the guard at a
specific type.

## A10 — Opaque-call obligations

The task brief lists call sites of helper functions that must be modeled
via the helper's opaque ``_M`` program.  In your generated body:

* Bind the call's result to a NAMED variable: ``r <- callee_M(args);;``
* Use ``r`` in the rest of the body.
* NEVER bind to ``_``.
* NEVER substitute the callee's behavior by hand-computing a replacement.

## A11 — Sandbox + tool limits

* Network access is disabled.  Do NOT try to install packages or fetch
  external documentation.
* ``coqc`` is on PATH.  The framework libs (``MonadLib``, ``FP``,
  ``SetsClass``, ``Coq.*``) and already-synthesized peer libs in
  ``output/gen/libs/`` are resolvable via ``_CoqProject``.
* Reads outside this workdir are permitted; writes are not.

## A12 — Failure semantics

* "Done" means ``coqc`` exited 0 on ``skeleton/{basename}_rel_lib.v``.
* If after multiple coqc iterations you cannot make it compile, emit the
  closest-to-correct lib you can manage and explain in the transcript
  what blocks compilation.
* Do NOT leave ``Admitted`` or stray ``Parameter`` placeholders for any
  name in the task's ``must_define`` list — those guarantee rejection.

---

The dynamic task brief (function summary, holes to fill, loop forest,
callees, examples, repair feedback) arrives on stdin.  Read it first,
then read ``skeleton/{basename}_rel_lib.v``, then edit.
"""


# A3 — verification command variants.  Picked by ``prepare_workdir`` based on
# whether ``rocq-mcp`` is available on the host PATH.

_A3_COQC_ONLY = """\
After each edit, run:

```
coqc -arg-file _CoqProject skeleton/{basename}_rel_lib.v
```

Iterate edits + coqc until the exit code is 0.  Use Rocq vernacular
(``Show.``, ``Search``, ``Check``, ``Print``, ``About``) inside the lib file
as scratch lemmas when you need to inspect proof state; remove the debug
commands before declaring the lib complete.  Do not stop until coqc
succeeds, or until you are convinced the spec is unsolvable as given."""


_A3_ROCQ_MCP = """\
The ``rocq-mcp`` MCP server is configured (see ``.codex/config.toml``).
Prefer it over invoking ``coqc`` repeatedly: step through Definitions
interactively, inspect intermediate types via ``Check``/``Search``/
``Print``, and iterate.  When you believe the lib is complete, run

```
coqc -arg-file _CoqProject skeleton/{basename}_rel_lib.v
```

as the final check — exit code 0 is the success condition.  Do not stop
until coqc succeeds, or until you are convinced the spec is unsolvable as
given."""


# ---------------------------------------------------------------------------
# Public entry points


def render_agents_md(basename: str, use_rocq_mcp: bool = False) -> str:
    """Return the rendered ``AGENTS.md`` content for *basename*.

    *use_rocq_mcp* swaps the A3 verification guidance: when True the agent
    is pointed at the ``rocq-mcp`` MCP server (configured by
    :func:`prepare_workdir` in ``.codex/config.toml``); when False the
    agent is told to drive ``coqc`` directly.
    """
    verification_section = (_A3_ROCQ_MCP if use_rocq_mcp else _A3_COQC_ONLY).format(
        basename=basename
    )
    return _AGENTS_MD_TEMPLATE.format(
        basename=basename,
        verification_section=verification_section,
    )


def prepare_workdir(
    parent_dir: str,
    basename: str,
    skeleton_text: str,
    coq_project_src: Optional[str] = None,
    use_rocq_mcp: Optional[bool] = None,
) -> Dict[str, str]:
    """Lay down a fresh workdir for one synthesis attempt.

    Idempotent: if ``parent_dir/workdir`` already exists, the skeleton is
    reset to *skeleton_text*, ``AGENTS.md`` is re-rendered, ``out/`` is
    cleared, and ``_CoqProject`` is re-linked.  The workdir is reusable
    across retries because the AGENTS.md / _CoqProject are static.

    Args:
        parent_dir: Directory under which ``workdir/`` is created.  Typical
            value is ``output/gen/synth/<basename>/<func>/``.
        basename: Output library basename (without ``_rel_lib`` suffix).
            Used to name the skeleton file inside ``workdir/skeleton/``.
        skeleton_text: The unfilled lib content (Parameters to be replaced).
        coq_project_src: Path to the existing ``_CoqProject`` to expose
            inside the workdir.  If ``None``, :func:`locate_coq_project` is
            used to find one.
        use_rocq_mcp: ``True`` ⇒ generate ``.codex/config.toml`` for the
            rocq-mcp MCP server and tell the agent to use it; ``False`` ⇒
            agent drives ``coqc`` directly.  ``None`` (default) ⇒
            auto-detect: enable rocq-mcp iff ``shutil.which("rocq-mcp")``
            finds it on PATH.

    Returns:
        Paths the synthesis backend needs:

        ``{"workdir", "agents_md", "skeleton_path", "coq_project",
        "out_dir", "transcript", "use_rocq_mcp"}``.

    Raises:
        ValueError: when no ``_CoqProject`` is available (pre-spawn hard
            error — synthesis without verification is not supported in
            workdir mode).
    """
    if coq_project_src is None:
        coq_project_src = locate_coq_project(start_dir=parent_dir)
    if coq_project_src is None or not os.path.isfile(coq_project_src):
        raise ValueError(
            "_CoqProject not found.  Workdir-mode synthesis requires a "
            "_CoqProject the agent can use with coqc; place one in the "
            "project tree or pass coq_project_src explicitly."
        )

    workdir = os.path.abspath(os.path.join(parent_dir, "workdir"))
    skeleton_dir = os.path.join(workdir, "skeleton")
    out_dir = os.path.join(workdir, "out")
    os.makedirs(skeleton_dir, exist_ok=True)
    # Reset out/ each call so transcripts from prior attempts don't linger.
    if os.path.isdir(out_dir):
        shutil.rmtree(out_dir)
    os.makedirs(out_dir, exist_ok=True)

    # Auto-detect rocq-mcp unless the caller pinned it explicitly.
    if use_rocq_mcp is None:
        use_rocq_mcp = shutil.which("rocq-mcp") is not None
    if use_rocq_mcp:
        _write_rocq_mcp_config(workdir, coq_project_src)
    else:
        # If a prior attempt configured rocq-mcp but the host no longer
        # has it, clear the stale config so the agent isn't confused.
        stale = os.path.join(workdir, ".codex", "config.toml")
        if os.path.isfile(stale):
            os.remove(stale)

    agents_md = os.path.join(workdir, "AGENTS.md")
    with open(agents_md, "w", encoding="utf-8") as f:
        f.write(render_agents_md(basename, use_rocq_mcp=use_rocq_mcp))

    skeleton_path = os.path.join(skeleton_dir, f"{basename}_rel_lib.v")
    with open(skeleton_path, "w", encoding="utf-8") as f:
        f.write(skeleton_text)

    coq_project_path = os.path.join(workdir, "_CoqProject")
    # Replace any prior copy/symlink so retries pick up a moved source.
    if os.path.islink(coq_project_path) or os.path.exists(coq_project_path):
        os.remove(coq_project_path)
    try:
        os.symlink(os.path.abspath(coq_project_src), coq_project_path)
    except OSError:
        # Filesystems that disallow symlinks (rare) — fall back to a copy.
        shutil.copy2(coq_project_src, coq_project_path)

    return {
        "workdir": workdir,
        "agents_md": agents_md,
        "skeleton_path": skeleton_path,
        "coq_project": coq_project_path,
        "out_dir": out_dir,
        "transcript": os.path.join(out_dir, "transcript.txt"),
        "use_rocq_mcp": use_rocq_mcp,
    }


def _write_rocq_mcp_config(workdir: str, coq_project_src: str) -> str:
    """Write ``workdir/.codex/config.toml`` registering the rocq-mcp MCP
    server so the agent can drive Coq interactively (Search, Check, Print,
    apply tactics, inspect proof state) instead of round-tripping through
    ``coqc``.  The CWD for rocq-mcp is the directory holding the
    ``_CoqProject`` we exposed — that's where rocq-mcp resolves project
    paths from."""
    rocq_mcp = shutil.which("rocq-mcp")
    if not rocq_mcp:  # pragma: no cover — caller checks first
        return ""
    codex_dir = os.path.join(workdir, ".codex")
    os.makedirs(codex_dir, exist_ok=True)
    cwd = os.path.dirname(os.path.abspath(coq_project_src))
    config_path = os.path.join(codex_dir, "config.toml")
    with open(config_path, "w", encoding="utf-8") as f:
        f.write(
            "[mcp_servers.rocq-mcp]\n"
            f'command = "{rocq_mcp}"\n'
            f'cwd = "{cwd}"\n'
            "startup_timeout_sec = 20\n"
            "tool_timeout_sec = 120\n"
        )
    return config_path


def locate_coq_project(start_dir: str) -> Optional[str]:
    """Walk upward from *start_dir* looking for a ``_CoqProject``.

    Returns the absolute path of the first match or ``None``.  Mirrors
    ``check_rocq._find_coq_project`` so workdir prep uses the same source
    of truth as post-hoc verification.
    """
    current = os.path.abspath(start_dir)
    while True:
        candidate = os.path.join(current, "_CoqProject")
        if os.path.isfile(candidate):
            return candidate
        parent = os.path.dirname(current)
        if parent == current:
            return None
        current = parent


# ---------------------------------------------------------------------------
# Pre-spawn prerequisite checks


_REQUIRE_IMPORT_RE = re.compile(
    r"^\s*Require\s+(?:Import|Export)\s+([\w\d_.]+)\s*\.\s*$",
    re.MULTILINE,
)


def required_callee_libs(skeleton_text: str) -> List[str]:
    """Return the list of ``Require Import``-d names ending in
    ``_rel_lib`` — these are project-internal cross-file callee libs that
    must exist (already synthesized) before the agent's coqc can succeed.

    External framework libs (``MonadLib``, ``Coq.ZArith.ZArith`` etc.) are
    excluded; only ``*_rel_lib`` names are returned.
    """
    out: List[str] = []
    seen: Set[str] = set()
    for match in _REQUIRE_IMPORT_RE.finditer(skeleton_text):
        name = match.group(1)
        if not name.endswith("_rel_lib") or name in seen:
            continue
        seen.add(name)
        out.append(name)
    return out


def check_prerequisites(
    skeleton_text: str,
    coq_lib_dir: Optional[str],
) -> None:
    """Hard-error pre-spawn if any prerequisite is missing.

    * ``coq_lib_dir`` must be set (callers normally pass
      ``read_configure_value("COQ_LIB_DIR")``).
    * For each ``Require Import {callee}_rel_lib`` in the skeleton, the
      file ``{callee}_rel_lib.v`` must exist inside ``coq_lib_dir`` —
      i.e. the callee has been synthesized in an earlier topo-ordered
      pass.

    Raises ValueError on any missing prerequisite.  The intent matches the
    design call: synthesis cannot proceed without verifiable references.
    """
    callees = required_callee_libs(skeleton_text)
    if not callees:
        return
    if not coq_lib_dir:
        raise ValueError(
            "Skeleton requires sibling callee libs "
            f"({', '.join(callees)}) but COQ_LIB_DIR is unset."
        )
    # When skeletons use the qualified Coq logical name
    # (``LIB.sub.callee_rel_lib``), only the final dot-separated segment is
    # the actual filename — that's what lives on disk inside ``coq_lib_dir``.
    missing = [
        callee
        for callee in callees
        if not os.path.isfile(os.path.join(coq_lib_dir, f"{callee.rsplit('.', 1)[-1]}.v"))
    ]
    if missing:
        raise ValueError(
            "Cross-file callee libs missing from COQ_LIB_DIR — synthesize "
            f"them first.  Missing in {coq_lib_dir}: "
            + ", ".join(f"{name.rsplit('.', 1)[-1]}.v" for name in missing)
        )


# ---------------------------------------------------------------------------
# Post-run validators


def snapshot_sha(path: str) -> str:
    """SHA-256 hex of a file's content — for the file-system whitelist."""
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


_TOLERATED_EXTENSIONS = (".vo", ".vok", ".vos", ".glob", ".aux")


def _is_tolerated_path(rel: str) -> bool:
    """Paths that the Layer-2 file-system whitelist deliberately ignores.

    The agent's own actions per ``AGENTS.md`` A3 (run ``coqc``) and the
    codex CLI's own bookkeeping (``.codex/`` history + config) create files
    that aren't part of our contract.  Filtering them out at snapshot time
    keeps the whitelist focused on what the agent shouldn't touch — AGENTS.md,
    _CoqProject, foreign source files — rather than what every well-behaved
    attempt unavoidably produces.
    """
    rel = rel.replace(os.sep, "/")
    # Codex internals — history, config, MCP cache.  All inside `.codex/`.
    if rel == ".codex" or rel.startswith(".codex/"):
        return True
    # coqc compiled artifacts produced next to the source they compiled.
    # Some Coq versions also emit dotfiles like ``.{name}.aux``; tolerate
    # those too by checking the basename rather than the full rel path.
    base = os.path.basename(rel)
    for ext in _TOLERATED_EXTENSIONS:
        if base.endswith(ext):
            return True
    return False


def snapshot_workdir(workdir: str) -> Dict[str, str]:
    """Map relative-path → SHA-256 for every regular file under *workdir*.

    Symlinks are followed; non-regular files are skipped.  Files matched by
    :func:`_is_tolerated_path` (coqc byproducts, codex internals) are
    omitted entirely so the Layer-2 whitelist neither requires nor rejects
    them.
    """
    out: Dict[str, str] = {}
    workdir_abs = os.path.abspath(workdir)
    for root, _dirs, files in os.walk(workdir_abs):
        for name in files:
            full = os.path.join(root, name)
            if not os.path.isfile(full):
                continue
            rel = os.path.relpath(full, workdir_abs)
            if _is_tolerated_path(rel):
                continue
            out[rel] = snapshot_sha(full)
    return out


def validate_workdir_filesystem(
    workdir: str,
    before: Dict[str, str],
    expected_modified: Set[str],
    expected_created: Set[str],
) -> None:
    """Layer-2 check — confirm the agent only touched whitelisted files.

    Args:
        workdir: Absolute path of the workdir.
        before: SHA snapshot taken with :func:`snapshot_workdir` before the
            agent ran.
        expected_modified: Relative paths whose SHA *may* differ after the
            run (typically ``{"skeleton/{basename}_rel_lib.v"}``).
        expected_created: Relative paths the agent is allowed to create
            (typically ``{"out/transcript.txt"}``).

    Raises ValueError on any unexpected modification, deletion, or extra
    file.
    """
    after = snapshot_workdir(workdir)
    after_set = set(after)
    before_set = set(before)

    extra = after_set - before_set - expected_created
    if extra:
        raise ValueError(
            "Agent created unexpected file(s) in workdir: "
            + ", ".join(sorted(extra))
        )

    missing = before_set - after_set
    if missing:
        raise ValueError(
            "Agent deleted expected file(s) from workdir: "
            + ", ".join(sorted(missing))
        )

    for rel, sha in before.items():
        if rel in expected_modified:
            continue
        if after.get(rel) != sha:
            raise ValueError(
                f"Agent modified a file outside the allowed set: {rel}"
            )


# ---------------------------------------------------------------------------
# Layer-3 — structural skeleton diff
#
# Top-level Coq block iteration mirrors what ``assemble._iter_top_level_blocks``
# already does for the multi-function merger.  We re-implement here to avoid
# importing assemble.py (which carries many heavy transitive deps).


_TOP_LEVEL_START_RE = re.compile(
    r"^(Definition|Parameter|Inductive|Fixpoint|Lemma|Theorem|Arguments|"
    r"Notation|Require|From|Import|Export|Local|Open|Close|Reserved|Record|"
    r"Structure|Class|Instance|Variable|Variables|Hypothesis|End|Section)\b",
    re.MULTILINE,
)


def _iter_top_level_blocks(content: str):
    starts = list(_TOP_LEVEL_START_RE.finditer(content))
    for i, match in enumerate(starts):
        start = match.start()
        end = starts[i + 1].start() if i + 1 < len(starts) else len(content)
        block = content[start:end].rstrip()
        if not block:
            continue
        kw = match.group(1)
        name_match = re.match(r"(\w+)\s+(\w+)", block)
        name = name_match.group(2) if name_match else ""
        yield kw, name, block


def _normalize_coq_type(text: str) -> str:
    """Collapse internal whitespace; strip balanced outer parens."""
    text = re.sub(r"\s+", " ", text).strip()
    while text.startswith("(") and text.endswith(")"):
        depth = 0
        balanced = True
        for i, ch in enumerate(text):
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0 and i != len(text) - 1:
                    balanced = False
                    break
        if balanced:
            text = text[1:-1].strip()
        else:
            break
    return text


_PARAMETER_HEADER_RE = re.compile(
    # Parameter X : T.   — T is single-line in every skeleton we emit.
    # ``_iter_top_level_blocks`` greedily folds following non-keyword text
    # (e.g. ``(* ---- section banner ---- *)``) into the block, so we don't
    # anchor at end of block, only at end of the Parameter line.
    r"^Parameter\s+(\w+)\s*:\s*([^\n]+?)\s*\.\s*(?:\n|$)",
)
_DEFINITION_HEADER_RE = re.compile(
    r"^Definition\s+(\w+)\s*:\s*(.+?)\s*:=", re.DOTALL,
)
_DEFINITION_NO_TYPE_RE = re.compile(
    r"^Definition\s+(\w+)\s*:=",
)


def _resolve_mretty_in_skeleton(
    skeleton_text: str, must_define: List[str],
) -> List[str]:
    """Backstop that reconciles ``must_define`` against what the skeleton
    actually emits when the two disagree on MretTy scoping.

    ``context.py`` is supposed to compute the same name the skeleton emits
    (see :func:`context._scoped_mretty_name`).  This helper exists so the
    validator stays correct when invoked from elsewhere (tests, future
    callers, manual debugging) without that expansion — or when a refactor
    flips one side of the count logic and breaks the invariant silently.

    Behaviour — symmetric on both directions of drift:

    * If both sides agree on the MretTy name, no change.
    * If ``must_define`` has bare ``"MretTy"`` but the skeleton emits
      exactly one ``Parameter <fn>_MretTy``, rewrite must_define to that
      scoped name.
    * If ``must_define`` has a scoped ``<fn>_MretTy`` but the skeleton
      emits bare ``Parameter MretTy``, rewrite must_define to bare
      ``"MretTy"``.  Without this case, a single in-file function whose
      cross-file siblings need MretTy gets a scoped must_define from a
      buggy counter, the skeleton uses bare, and the validator falsely
      rejects the agent's correct ``Definition MretTy``.
    * If the skeleton declares multiple ``_MretTy`` Parameters and
      ``must_define`` doesn't pick one, raise — the validator can't
      disambiguate.
    """
    skel_names = {name for _kw, name, _ in _iter_top_level_blocks(skeleton_text)}
    has_bare = "MretTy" in skel_names
    skel_scoped = [n for n in skel_names if n.endswith("_MretTy")]

    must_has_bare = "MretTy" in must_define
    must_scoped = [n for n in must_define if n.endswith("_MretTy")]

    # Direction 1 (legacy): must_define bare, skeleton scoped.
    if must_has_bare and not has_bare:
        if len(skel_scoped) == 0:
            return must_define   # let the strict diff complain coherently
        if len(skel_scoped) > 1:
            raise ValueError(
                "Ambiguous MretTy scoping: skeleton declares multiple "
                "*_MretTy Parameters ("
                + ", ".join(sorted(skel_scoped))
                + ") but must_define has the unscoped \"MretTy\".  Pass "
                "the concrete scoped name in must_define."
            )
        target = skel_scoped[0]
        return [target if name == "MretTy" else name for name in must_define]

    # Direction 2 (new): must_define scoped, skeleton bare.
    if has_bare and must_scoped and not must_has_bare:
        # Replace each scoped name with the bare one.  Use list-comprehension
        # not set logic — preserve must_define ordering for stable prompts.
        scoped_set = set(must_scoped)
        return ["MretTy" if name in scoped_set else name for name in must_define]

    return must_define


def validate_skeleton_diff(
    skeleton_text: str,
    filled_text: str,
    must_define: List[str],
) -> None:
    """Layer-3 check — enforce the strict replacement contract.

    For every top-level block in *skeleton_text*:

    * If it is a ``Parameter X : T.`` whose ``X`` is in *must_define*, the
      filled lib's corresponding block must be a ``Definition X : T :=
      <body>.`` with the **same** declared ``T`` (whitespace-normalized).
      An untyped ``Definition X := <body>.`` is rejected — the type must
      remain explicit and match.
    * If it is any OTHER kind of block (imports, concrete ``Definition``,
      mechanical ``M_loop{k}_M2``, ``Inductive early_result``, ...) the
      filled lib's block at the same position must be byte-identical.

    Extra blocks the agent added that didn't exist in the skeleton are
    rejected (they drift the lib's meaning).

    Raises ValueError describing the first violation found.
    """
    # Defense-in-depth: if the caller passed bare "MretTy" but the skeleton
    # uses a scoped name, rewrite must_define so the validator agrees.  The
    # primary fix lives in :func:`context._scoped_mretty_name`.
    must_define = _resolve_mretty_in_skeleton(skeleton_text, list(must_define))
    skel_blocks = list(_iter_top_level_blocks(skeleton_text))
    fill_blocks = list(_iter_top_level_blocks(filled_text))
    must_set = set(must_define)

    skel_names = [name for _kw, name, _b in skel_blocks]
    fill_names = [name for _kw, name, _b in fill_blocks]

    skel_name_set = set(skel_names)
    fill_name_set = set(fill_names)

    foreign = fill_name_set - skel_name_set
    if foreign:
        raise ValueError(
            "Agent added top-level block(s) not present in skeleton: "
            + ", ".join(sorted(foreign))
        )
    missing = skel_name_set - fill_name_set
    if missing:
        raise ValueError(
            "Agent removed top-level block(s) from skeleton: "
            + ", ".join(sorted(missing))
        )

    skel_by_name = {name: (kw, block) for kw, name, block in skel_blocks}
    fill_by_name = {name: (kw, block) for kw, name, block in fill_blocks}

    for name, (skel_kw, skel_block) in skel_by_name.items():
        fill_kw, fill_block = fill_by_name[name]
        if name in must_set and skel_kw == "Parameter":
            _validate_parameter_to_definition(name, skel_block, fill_kw, fill_block)
        else:
            if skel_block.strip() != fill_block.strip():
                raise ValueError(
                    f"Top-level block '{name}' was modified outside the "
                    "agreed contract.  Only Parameters listed in "
                    "must_define may change."
                )


def _validate_parameter_to_definition(
    name: str, skel_block: str, fill_kw: str, fill_block: str,
) -> None:
    skel_m = _PARAMETER_HEADER_RE.match(skel_block)
    if not skel_m:
        raise ValueError(
            f"Skeleton's '{name}' block is not a well-formed Parameter "
            "declaration; cannot validate replacement."
        )
    expected_type = _normalize_coq_type(skel_m.group(2))

    if fill_kw == "Parameter":
        # The agent left it as a Parameter — that's a stub, not a fill.
        raise ValueError(
            f"'{name}' is still declared as a Parameter in the filled "
            "lib.  must_define names must be replaced with Definitions."
        )

    if fill_kw != "Definition":
        raise ValueError(
            f"'{name}' was replaced with a {fill_kw}; must be a Definition."
        )

    fill_m = _DEFINITION_HEADER_RE.match(fill_block)
    if not fill_m:
        if _DEFINITION_NO_TYPE_RE.match(fill_block):
            raise ValueError(
                f"'{name}' Definition omits the type annotation.  Keep "
                "the signature from the skeleton's Parameter line."
            )
        raise ValueError(
            f"'{name}' Definition is not well-formed (could not parse "
            "type signature)."
        )
    actual_type = _normalize_coq_type(fill_m.group(2))
    if expected_type != actual_type:
        raise ValueError(
            f"'{name}' signature must not change.\n"
            f"Required: {expected_type}\n"
            f"Got:      {actual_type}"
        )


# ---------------------------------------------------------------------------
# Convenience: combined post-run check used by the synthesis pipeline.


def validate_attempt(
    workdir: str,
    before: Dict[str, str],
    skeleton_before_text: str,
    filled_text: str,
    must_define: List[str],
    basename: str,
) -> Tuple[bool, Optional[str]]:
    """Run Layer-2 + Layer-3 checks in one call.

    Returns ``(passed, message)`` — *message* is the failure description on
    rejection, ``None`` on success.  The synthesis pipeline forwards
    *message* into the next attempt's repair feedback.
    """
    expected_modified = {f"skeleton/{basename}_rel_lib.v"}
    expected_created = {"out/transcript.txt"}
    try:
        validate_workdir_filesystem(
            workdir, before, expected_modified, expected_created,
        )
    except ValueError as exc:
        return False, f"file-system whitelist: {exc}"

    try:
        validate_skeleton_diff(skeleton_before_text, filled_text, must_define)
    except ValueError as exc:
        return False, f"skeleton diff: {exc}"

    return True, None
