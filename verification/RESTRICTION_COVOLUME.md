# Restriction-of-scalars covolume

## Exact boundary

The endpoint remains `lem:restriction-covolume`, consumed by
`lem:arithmetic-compactness`: the Euclidean Haar covolume of the actual
trace-metric integer lattice must equal
`abs(discriminant K)^(a/2) * exp(-[K:ℚ] * h.degree)` for every finite
projective module over the ring of integers, including rank zero.
The positive-rank covolume identity is not yet formalized. The exact
rank-zero instance is proved for the actual lattice and intrinsic degree.

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
fingerprint `95819e0a2a987609`. The dedicated 14-declaration axiom probe
passed (fingerprint `2bec001e17d69f56`); every listed construction and
lattice/tensor bridge uses only `propext`, `Classical.choice`, and `Quot.sound`.

## Remaining calculation

`Conjugation.lean` now proves conjugation on every vector of the real
trace space and both weighted-place pairing and squared-norm formulas.
`Covolume.lean` defines `traceCovolume` using Mathlib's actual Euclidean
Haar volume of `TraceSpace`, proves positivity and its trace Gram
determinant formula for any integer basis, and proves the exact
discriminant/degree formula when the generic rank is zero.
The module checks passed 3354 and 3609 jobs respectively (fingerprints
`d54fe514bd33c398`, `4654fd507b6b48db`).

Remaining: relate the Gram determinant to Mathlib's mixed-embedding
discriminant formula, including the complex factor cancellation. Prove the
finite-index passage agrees with the existing intrinsic determinant degree.
No source-facing completion is claimed for any of these remaining steps.

The fixed TraceSpace producer received independent honesty review:
**honest/proved producer**, no actionable defect; metric and lattice data
are constructed and bounded-section finiteness is used substantively.
Root integration is delegated to GEOM in I-0092. The first source files
were captured by ARITH's lifecycle integration `21ba17f` just before the
explicit owned-path commit `cafb32d`, which contains only the audit-doc
delta. Authorship of those files is BOST-COVOLUME/run0008; no manual ARITH
source edits occurred.

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
The Gram computation reuses `BostConjecture.Lattice.Covolume` directly;
that existing module already records its TauCeti adaptation and license.
No duplicate lattice or Gram implementation was introduced.
