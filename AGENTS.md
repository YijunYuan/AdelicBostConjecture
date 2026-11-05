# BostConjecture

The target is Theorem 1.1 of the workspace-root
`bost_specht_manuscript.pdf`: maximal slopes are additive under Hilbert tensor
products of positive-rank Hermitian vector bundles over the ring of integers
of every number field, with the finite-family consequence. `Bost.pdf` is an
expository reference for the Euclidean case, not a substitute for the
number-field statement.

- Formalize only the definitions and results actually needed by the target.
  Reuse checked mathlib results; do not reproduce an entire cited theory when
  a smaller proved special case suffices. The effective rate, weighted
  Harder–Narasimhan compatibility and appendices are outside the initial target
  unless a verified dependency requires them.
- The manuscript is a proposed proof. Check its load-bearing steps before
  encoding them; record genuine gaps and repair them mathematically. Never
  weaken the target, assume tensor semistability, or introduce a target-shaped
  certificate merely to obtain a compiling theorem.
- Completion requires kernel-checked Lean for the target and all dependencies,
  no `sorry`/`admit` or `sorryAx`, and no new axioms replacing mathematical
  proofs. Audit the target with `#print axioms`; distinguish Lean's standard
  foundational axioms from additional assumptions. No main-theorem completion
  claim is justified by a clean build of prerequisites alone.
- Maintain the mathematical blueprint before or alongside Lean and keep its
  statements, dependencies and completion markers faithful to checked code.
- Reuse suitable external formalizations by pinned dependency, selective copy,
  or adaptation. For each reuse record the repository, exact revision, original
  path/declarations, license, modifications and project consumers in
  `CONTRIBUTIONS.md`; preserve license and attribution notices. Check the reused
  dependency cone for unproved assumptions and toolchain compatibility.
- Keep source Lean and imports small; avoid unused abstractions and duplicate
  representations. Search available libraries before adding infrastructure.

The user has authorized the setup batches, necessary edits and checks, and
continued work toward the target without repeated approval questions. This is
not authorization to publish, push to a remote, or run unrelated work.
