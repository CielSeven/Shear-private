# Functional Correctness — Architecture (final)

Deriving functional correctness from a refinement proof is split across
two skills, joined by an `Admitted.` Hoare triple. The key decoupling:
the spec-derivation VC's proof only needs the Hoare triple's
**statement**, not its proof — so VC solving and triple proving are
independent (they can even run in parallel).

## Stage 1 — `refinement-vc-solver` (fc_* stage + normal pipeline)

See "Functional-correctness derivation" in
`.codex/skills/refinement-vc-solver/SKILL.md`.

1. `fc_snapshot.py <base>` — backups + audit baselines (lib def hashes,
   C annotation comments, function bodies, header counts) into a work
   dir (ephemeral by default; `--work-dir` to pin).
2. `proof_archive.py archive-file` — save the solved manual proofs
   (content-hash keyed, survives wit renumbering).
3. Calling agent edits `<base>_rel.c`: name the implementation spec
   `low_level_spec` in place; add one `high_level_spec <= low_level_spec`
   forward declaration; add needed `Extern Coq` symbols. Function header
   appears exactly twice afterwards (enforced).
4. Calling agent appends to `<base>_rel_lib.v` (append-only, enforced):
   helper defs + the Hoare triple statement with a natural-language
   proof-sketch comment and `Proof. Admitted.`; recompile lib.
5. `fc_symexec.py <base>` — regenerate VCs.
6. Normal vc-solver Steps 1–5 with Step 1.5 proof reuse: old VCs are
   reused via the exact-match gate (no LLM spend); the new derivation VC
   is proved by the sandboxed agent citing the admitted triple.
7. `fc_verify.py <base>` — gate: coqc clean, zero `Admitted.` in
   `_manual.v`, lib append-only, C protected regions, header counts.
   Appended lib lemmas still `Admitted.` are reported as **deferred**.

## Stage 2 — `monadic-hoare-prover`

See `.codex/skills/monadic-hoare-prover/SKILL.md`.

1. `snapshot_lib.py <lib.v>` — baseline hashes; target set = lemmas
   containing `Admitted.`.
2. Prove the targets (agent mechanism TBD: inline orchestrator for now;
   sandboxed codex worker as a future option). Helper lemmas may be
   inserted; target statements are frozen.
3. `verify_lib.py <lib.v>` — gate: pre-existing blocks byte-stable,
   target statements unchanged, zero `Admitted.`, coqc clean.

Functional correctness is **complete** when stage 2's gate passes and
downstream `.vo`s are rebuilt.

## History

Earlier iterations of this plan had a standalone `functional-correctness`
skill with its own `diff_goals.py` / `patch_old_proofs.py`. Those were
deleted: they duplicated (worse — name-keyed matching breaks under wit
renumbering) what `proof_archive.py` + `apply_proof_reuse.py` already do
in the vc-solver.
