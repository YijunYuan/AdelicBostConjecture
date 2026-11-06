# Restriction-of-scalars covolume

## Exact boundary

The endpoint remains `lem:restriction-covolume`, consumed by
`lem:arithmetic-compactness`: the Euclidean Haar covolume of the actual
trace-metric integer lattice must equal
`abs(discriminant K)^(a/2) * exp(-[K:ℚ] * h.degree)` for every finite
projective module over the ring of integers, including rank zero.
The covolume identity is not yet formalized.

## Constructed real space and lattice

`Arithmetic.RestrictionCovolume.TraceSpace` constructs the real span of
the simultaneous integral sections in the product of all complex fibers.
`HermitianMetric.traceCore` sums the real parts of the given pairings over
all embeddings. The induced metric therefore satisfies
`traceSection_norm_sq`, and each individual section norm is bounded by the
trace norm. Bounded-section finiteness proves discreteness of the actual
image `traceLattice`; fullness follows from the span construction.

`realTensorEquiv` is proved bijective using Mathlib's lattice-basis theorem
and agrees with `r ⊗ x ↦ r • traceSection x`. It is thus the canonical real
scalar extension, not an assumed comparison. `traceSpace_finrank` gives
the dimension `[K:ℚ] * a`. No integral freeness over `𝓞 K` is assumed.
The new blueprint node `lem:real-trace-lattice` supplies this producer to
the existing restriction-covolume node.

Kernel check: workspace-root serialized Horizon check of
`BostConjecture.Arithmetic.RestrictionCovolume.TraceSpace` passed, 3353 jobs,
fingerprint `95819e0a2a987609`. The dedicated axiom probe lists the actual
construction and all exported lattice/tensor bridges.

## Remaining calculation

Prove conjugation on the full real span and the equivalent weighted-place
norm formula. Define covolume using the Euclidean Haar volume of this
metric. Relate its Gram determinant to Mathlib's mixed-embedding
discriminant formula, including the complex factor cancellation. Prove the
finite-index passage agrees with the existing intrinsic determinant degree.
No source-facing completion is claimed for any of these remaining steps.

## Reuse

This unit imports existing project arithmetic results and Mathlib's
`Module.Basis.ofZLatticeBasis`, `ZLattice.rank`, and scalar-extension APIs;
it copies no external source. Mathlib is the unchanged pinned dependency
`leanprover-community/mathlib4` at
`56a005855ea17e0b0958f73ec801ae140b0a1679` (Apache-2.0).
The original Mathlib lattice APIs are in
`Mathlib/Algebra/Module/ZLattice/Basic.lean`; the tensor maps are in
`Mathlib/LinearAlgebra/TensorProduct/{Lift,Basis}.lean`.
The existing project imports retain their own recorded provenance.
