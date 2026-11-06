# BostConjecture

The target is Theorem 1.1 of this paper: maximal slopes are additive under
Hilbert tensor products of positive-rank Hermitian vector bundles over the
ring of integers of every number field, with the finite-family consequence.
Refer to the manuscript as "this paper" in documentation. The Euclidean case
is not a substitute for the number-field statement.

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
- Keep source documentation and README statements, dependencies and completion
  claims faithful to checked code. The user has removed `blueprint/` and
  `verification/`; do not recreate or depend on those directories. Run proof
  and axiom checks using temporary files when needed.
- Reuse suitable external formalizations by pinned dependency, selective copy,
  or adaptation. For each reuse record the repository, exact revision, original
  path/declarations, license, modifications and project consumers in
  `CONTRIBUTIONS.md`; preserve license and attribution notices. Check the reused
  dependency cone for unproved assumptions and toolchain compatibility.
- Place selectively copied source under `BostConjecture/ExternalCode/`, grouped
  by origin, with source documentation and upstream namespaces preserved.
  Compile it within the single `BostConjecture` library. Original code uses
  Apache-2.0; retain external licenses and attribution.
- Keep source Lean and imports small; avoid unused abstractions and duplicate
  representations. Search available libraries before adding infrastructure.

The user has authorized the setup batches, necessary edits and checks, and
continued work toward the target without repeated approval questions. This is
not authorization to publish, push to a remote, or run unrelated work.
