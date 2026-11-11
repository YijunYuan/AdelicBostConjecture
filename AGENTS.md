# BostConjecture

The target is Theorem 1.1 of `bost.pdf` (revised 10 November 2026): maximal
slopes are additive under orthogonal tensor products of positive-rank Hermitian
adelic vector bundles on a proper adelic curve over any countable field of
characteristic zero, with the finite-family and semistability consequences.
Archimedean absolute values are the usual real/complex ones; tensor norms are
Hilbert at Archimedean places and epsilon norms at other places. `old.pdf` is
the previous number-field target; its implementation is reusable infrastructure,
not a proof of the new target. Refer to the current manuscript as "this paper".

- Formalize only the definitions and results actually needed by the target.
  Reuse mathlib, the pinned HarderNarasimhan and ArakelovGeometry libraries, and
  existing project code before writing replacements. Search other suitable
  formalizations for genuine missing producers. Do not reproduce an entire
  cited theory when a proved special case suffices. Weighted tensor HN
  compatibility is in scope as the simultaneous rank-induction invariant.
  The effective rate and appendices remain outside scope unless needed.
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
  claims faithful to checked code. Maintain the mathematical blueprint in
  `blueprint/src/` and synchronize its actual Lean attachments and dependencies
  to the dashboard DAG. The user explicitly restored blueprint and DAG support;
  the previous prohibition on recreating blueprint is obsolete. Keep proofs
  complete and mathematical, and distinguish pending from kernel-checked nodes.
  Run proof and axiom checks using temporary files; do not recreate `verification/`.
- Reuse suitable external formalizations by pinned dependency, selective copy,
  or adaptation. For each reuse record the repository, exact revision, original
  path/declarations, license, modifications and project consumers in
  `CONTRIBUTIONS.md`; preserve license and attribution notices. Check the reused
  dependency cone for unproved assumptions and toolchain compatibility.
- Prefer ArakelovGeometry's exports when external declarations are duplicated.
  Check actual statements and adaptation differences before removing a local copy.
  Place new selectively copied source under `BostConjecture/ExternalResults/`,
  grouped by origin, with source documentation and upstream namespaces preserved.
  Existing `ExternalCode/` ports remain available until their consumers have
  been migrated or shown unnecessary for the new target.
  Compile it within the single `BostConjecture` library. Original code uses
  Apache-2.0; retain external licenses and attribution.
- Keep source Lean and imports small; avoid unused abstractions and duplicate
  representations. Search available libraries before adding infrastructure.

The user has authorized the setup batches, necessary edits and checks, and
continued work toward the target without repeated approval questions. This is
not authorization to publish, push to a remote, or run unrelated work.

## Parallel execution

The interactive coordinator schedules at most six Horizon runs and monitors
memory. Worker runs must not launch further runs. Work only in the task's
assigned paths; others are editing the same tree, so never revert their work.
Coordinate shared interfaces through the inbox before changing another scope.
Use `horizon check` for kernel checks, with `LEAN_NUM_THREADS=2`; do not start
independent broad builds. Release unused LSP sessions. The coordinator owns
the root import, dependency pins, project instructions and final integration.
Use explicit pathspec ledger commits. Do not edit `.lake/packages/` dependencies.
