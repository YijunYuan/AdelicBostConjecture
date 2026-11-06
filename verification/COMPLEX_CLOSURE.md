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

## Checked integral lifting and finite fibers

`ComplexClosure.IntegralLifting` proves extension of a closed point of a
subalgebra through an integral finite-type algebra, then lifts a root of
the actual specialized minimal polynomial. The latter proof uses
`minpoly.ker_eval` to descend evaluation and the former extension theorem
to finish. It assumes only the normalization setting: a domain over an
integrally closed domain, an injective (torsion-free) integral inclusion,
and finite type over an algebraically closed ground field.

`ComplexClosure.FiniteFiber` constructs the coordinate-product separator
and proves monic coordinate equations on the canonical `zeroLocus`.
Those equations feed both actual fiber finiteness and a coordinatewise
uniform bound on all lifts of a converging base sequence. No root lifting,
constructibility, openness or density conclusion is an assumed certificate.

Explicit-root serialized builds passed warning-free:
IntegralLifting **2,047 jobs** at 00:20:53 UTC; FiniteFiber **3,005 jobs** at
00:24:03 UTC (2026-11-06). The expanded audit passed **19 transitive probes**
at 00:24:38 UTC with only the three foundational axioms. Final source LSP
diagnostics are clear; the audit LSP reported stale imports before the
FiniteFiber build, while the subsequent serialized audit passed. Independent
honesty/mathematical review inspected these checks and accepted the exact
minimal-polynomial use, hypotheses, empty cases and substantive consumers.
Its coordinatewise-bound precision edit is incorporated in the blueprint.

Additional imported, unmodified producers at the same pinned Mathlib revision:
`FieldTheory/Minpoly/IsIntegrallyClosed.lean` (`minpoly.ker_eval`, Riccardo
Brasca, Paul Lezeau, Junyan Xu), `RingTheory/Ideal/GoingUp.lean`
(`exists_ideal_over_maximal_of_isIntegral`, Anne Baanen, Yongle Hu),
`RingTheory/Jacobson/Ring.lean` (`finite_of_finite_type_of_isJacobsonRing`),
`FieldTheory/IsAlgClosed/Basic.lean` (`IsAlgClosed.lift`), and
`RingTheory/Ideal/Quotient/Operations.lean` (`AlgHom.liftOfSurjective`).
The dependency cones are covered by the transitive probes. Consumer:
finite-normalization openness below, then density, still unproved. No copied source.

## Checked normalization openness

`ComplexClosure.Normalization` proves point detection for quotient characters,
realization of every specialized root of the actual minimal polynomial, and
subsequence lifting to a chosen point. It combines the coordinate-product
separator, root persistence, uniform coordinate bounds and compactness to
prove `isOpenMap_polynomial_normalization`. The hypotheses are a prime ideal
and an integral injective polynomial coordinate map; construction of such a
map by Noether normalization is the next obligation.

The explicit-root kernel build passed **3,332 jobs**, warning-free, at
00:32:21 UTC on 2026-11-06 (fingerprint `6a59255ca0121606`). The expanded
audit passed **23 transitive probes** at 00:33:43 UTC, all foundational-only.
The audit waited 28.717 seconds for the shared slot. Guarded LSP diagnostics
are clear. Independent honesty/mathematical review accepted the proof and
empty arities; its two blueprint precision corrections are incorporated:
the proof uses a convergent subsequence, and only its two stated conclusions
are attached to the new `leanok` node. Full constructible closure equality
remains open.

Additional unmodified Mathlib imports at the pinned revision:
`RingTheory/Polynomial/UniqueFactorization.lean` (multivariate polynomial UFD),
`RingTheory/Polynomial/RationalRoot.lean` (UFDs are integrally closed),
`Topology/Sequences.lean` (`IsCompact.tendsto_subseq`, `IsSeqClosed.isClosed`),
and `Topology/Compactness/Compact.lean` (`isCompact_univ_pi`). No source copied.

## Operational boundary

The read-only ground review accepted the finite-normalization blueprint
and checked the registered Milne statement excerpt. It did not inspect the
original PDF or certify a Lean implementation of that argument. The roadmap
active-count warning reflects ancestors and separate authorized proof lanes;
review found no cross-lane status change warranted. Indexed Horizon search
stalled and was stopped; guarded local search and LeanSearch supplied the
checked library declarations. Four proof writers remain the authorized cap.
