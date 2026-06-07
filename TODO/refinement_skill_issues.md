# Refinement VC Solver Skill — Issues & Solutions

## Do not let AI choose witness at the first time 

## List-rewrite section belongs in a shared appendix, not in `spatial_proof_tutorial.md`

The "List-shape rewrites for `++` and `+::`" section currently lives in
`.codex/skills/refinement-vc-solver/tutorial/spatial_proof_tutorial.md`. It
got placed there because the motivating example (merging two `sllseg`
segments via `sllseg_sllseg`) is spatial, but the actual rewriting work
happens on pure `list Z` arguments — it's not a spatial-entailment topic
and safeExec-side proofs hit the same pitfalls.

Action: move the section into either

- a new `list_rewrite_tutorial.md` appendix under `tutorial/`, or
- a subsection inside `refinement_proof_tutorial.md`,

and leave a one-line pointer in `spatial_proof_tutorial.md` near the
`sllseg_sllseg` discussion so readers still find it in context ("after
`sllseg_sllseg`, the combined list has shape `(l ++ _ :: nil) ++ _ :: nil`;
see the list-rewrite appendix").
