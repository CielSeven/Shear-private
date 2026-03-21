# GenMonads and Scripts Reference

This folder contains a source-oriented reference for the repository code under `GenMonads/` and `scripts/`.

Scope:
- Documents source, test, data, and reference files under `GenMonads/`
- Documents runnable utilities under `scripts/`
- Excludes generated `__pycache__/` artifacts

Generated from repository inspection on 2026-03-20.

## Document Map

- `genmonads.md`: package layout, pipeline overview, and file-by-file notes for `GenMonads/`
- `scripts.md`: operational notes and file-by-file summaries for `scripts/`

## High-Level Flow

The main translation pipeline in this repository is:

1. `GenMonads/transshape/preprocess.py`
   Extract function specifications and loop invariants from annotated C files.
2. `GenMonads/transshape/translator.py`
   Convert shape predicates into data predicates and introduce existential variables.
3. `GenMonads/guardgen/`
   Turn translated invariants plus loop conditions into Coq guard formulas.
4. `GenMonads/addabstract/addexec.py`
   Wrap translated assertions with `safeExec(...)`.
5. `GenMonads/translate_c_file.py`
   Rewrite C annotations, insert Coq declarations, and emit `_rel.c` files.
6. `GenMonads/absprog/gen_rel_lib.py`
   Generate `_rel_lib.v` skeletons for the abstract program side.

## Recommended Reading Order

If you are new to the codebase, read in this order:

1. `GenMonads/README.md`
2. `GenMonads/transshape/README.md`
3. `GenMonads/guardgen/README.md`
4. `document/genmonads_and_scripts/genmonads.md`
5. `document/genmonads_and_scripts/scripts.md`
