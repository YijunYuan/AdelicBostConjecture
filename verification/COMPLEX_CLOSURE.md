# Complex polynomial-image closure comparison

The required endpoint is exactly `closure_polynomial_image_zeroLocus` from
`BALANCED.md` (I-0072, f9e8974), in namespace
`BostConjecture.InvariantTheory`. It remains **unproved**. Constructible
images on complex points and finite-normalization density remain open;
neither the reverse closure inclusion nor Lemma 7.2 is claimed here.

## Checked coordinate bridge

`ComplexClosure.Coordinates` proves evaluation compatibility using the
existing `SymmetricAlgebra.equivMvPolynomial b.dualBasis`, and
`polynomialZariskiClosure_eq_preimage_zeroLocus` identifies the canonical
intrinsic closure with the preimage of the canonical coordinate zero locus
of `MvPolynomial.vanishingIdeal`. It also proves continuity, Euclidean
closedness and `closure_subset_polynomialZariskiClosure` for every set.
The finite basis can have an empty index type; the set can be empty.

Explicit-root serialized kernel build on 2026-11-06:

```
horizon --root /home/yijunyuan/bc-workspace check BostConjecture.InvariantTheory.ComplexClosure.Coordinates --json
```

Passed **2,833 jobs**, warning-free, fingerprint `17abe5da09ac8892`.
The serialized `--lean verification/ComplexClosureAxioms.lean` check passed
all **7 transitive probes**, fingerprint `a726d36eda1f8d27`. Each reports only
`propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or custom axiom.
Final guarded LSP diagnostics are clear. Intermediate missing decidable
equality and `aeval`/`eval` rewriting issues were fixed before checking.

Independent read-only `honesty-reviewer` accepted the canonical objects,
evaluation proof, empty/zero-dimensional cases, source-facing statement and
honest partial status. The coordinate blueprint node alone carries `leanok`;
the two inherited constructibility/closure nodes remain `notready`.
Shared root integration is delegated to GEOM and is not yet claimed.

## Reuse provenance for shared integration

Imported, unmodified Mathlib at
`56a005855ea17e0b0958f73ec801ae140b0a1679`, Apache-2.0:

- `Mathlib/LinearAlgebra/SymmetricAlgebra/Basis.lean`:
  `equivMvPolynomial`, `equivMvPolynomial_symm_X` (Raphael Douglas Giles,
  Zhixuan Dai, Zhenyan Fu, Yiming Fu, Jingting Wang, Eric Wieser).
- `Mathlib/RingTheory/Nullstellensatz.lean`: `zeroLocus`, `vanishingIdeal`
  (Devon Tuma); no Nullstellensatz conclusion is needed for this bridge.
- `Mathlib/Topology/Algebra/MvPolynomial.lean`: `continuous_eval`.
- `Mathlib/Topology/Algebra/Module/FiniteDimension.lean`:
  `continuous_equivFun_basis`, via the normed finite-dimension import.

Consumer: the pending exact polynomial-image endpoint, then BALANCED's
actual Plücker orbit closure comparison. No library source was copied or
modified and no dependency or toolchain was changed.

## Checked root persistence and bounds

`ComplexClosure.Roots` proves the nearest-root product inequality, persistence
for arbitrary filters and fixed positive monic degree, its application to
polynomial specialization, and a uniform Cauchy bound for every root over
every term of a converging parameter sequence. Repeated roots are included;
degree-zero root bounds are vacuous because a monic constant is one.

The explicit-root serialized Roots build passed **2,996 jobs**, warning-free,
at 2026-11-06 00:16:02 UTC. The expanded axiom audit passed all **13 probes**
at 00:16:48 UTC, again with only the three foundational axioms. A first Roots
build failed because `zero_le` resolved in the polynomial namespace; the
explicit nonnegative-real proof fixed it. Final guarded LSP diagnostics are
clear. Independent honesty review inspected both the proof and actual check
logs and accepted these two producers; their two blueprint nodes carry `leanok`.

Further unmodified imports from the same pinned Apache-2.0 Mathlib revision:
`Analysis/Complex/Polynomial/Basic.lean` (`Complex.isAlgClosed`, Chris Hughes,
Junyan Xu, Yury Kudryashov), `Algebra/Polynomial/Splits.lean`
(`Splits.eval_eq_prod_roots_of_monic`, `Splits.natDegree_eq_card_roots`),
`Analysis/Polynomial/CauchyBound.lean` (`IsRoot.norm_lt_cauchyBound`, Daniel
Weber), `Data/Finset/Max.lean` (`Multiset.exists_min_image`), and
`Topology/Order/LiminfLimsup.lean` (`Tendsto.bddAbove_range`). No source was
copied. The intended consumer is the pending finite-normalization openness
proof, not a semistability certificate.

## Operational boundary

The read-only ground review accepted the finite-normalization blueprint
and checked the registered Milne statement excerpt. It did not inspect the
original PDF or certify a Lean implementation of that argument. The roadmap
active-count warning reflects ancestors and separate authorized proof lanes;
review found no cross-lane status change warranted. Indexed Horizon search
stalled and was stopped; guarded local search and LeanSearch supplied the
checked library declarations. Four proof writers remain the authorized cap.
