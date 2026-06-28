"""CLI: fill a rel_lib template from its data-VC file.

    python -m GenMonads.absprog.segcodegen.cli TEMPLATE.v AUTOVC.c [-o OUT.v] [--check]

With ``--check`` the filled library is type-checked with ``coqc`` (compiling its
sibling ``*_rel_lib`` dependencies first).  This proves the synthesized terms are
well-typed Coq, not that they refine the data-VC.
"""

from __future__ import annotations

import argparse
import os
import sys
import tempfile

from . import fill_from_paths
from .check import check_lib


def main(argv=None) -> int:
    p = argparse.ArgumentParser(prog="segcodegen", description=__doc__)
    p.add_argument("template", help="path to the *_rel_lib.v template")
    p.add_argument("autovc", help="path to the *_data_autovc.c proof file")
    p.add_argument("-o", "--output", help="output path (default: stdout)")
    p.add_argument("--check", action="store_true",
                   help="type-check the filled lib with coqc")
    p.add_argument("--coq-project",
                   help="_CoqProject providing the library-tree flags (for --check)")
    args = p.parse_args(argv)

    # --check needs the result on disk (with deps resolvable); use a temp dir if
    # no explicit output was requested.
    tmpdir = None
    out_path = args.output
    if args.check and not out_path:
        tmpdir = tempfile.mkdtemp(prefix="segcodegen_check_")
        out_path = os.path.join(tmpdir, os.path.basename(args.template))

    result = fill_from_paths(args.template, args.autovc, out_path)
    if not args.output and not args.check:
        sys.stdout.write(result)

    rc = 0
    if args.check:
        res = check_lib(out_path, os.path.dirname(os.path.abspath(args.template)),
                        coq_project=args.coq_project)
        status = res.get("status")
        if status == "passed":
            sys.stderr.write(f"[check] PASS  {args.template}\n")
        elif status == "skipped":
            sys.stderr.write(f"[check] SKIP  {args.template} ({res.get('reason')})\n")
        else:
            rc = 1
            where = f" (dep {res['dep']})" if status == "dep-failed" else ""
            sys.stderr.write(f"[check] FAIL  {args.template}{where}\n")
            sys.stderr.write((res.get("stderr") or res.get("stdout") or "").strip()[:1500] + "\n")
    return rc


if __name__ == "__main__":
    raise SystemExit(main())
