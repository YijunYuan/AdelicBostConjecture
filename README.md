# BostConjecture

This project formalizes Theorem 1.1 of the manuscript `bost.tex` and deduces
the classical number-field Bost conjecture from it. The adelic theorem states
that maximal slopes are additive under orthogonal tensor products of
positive-rank Hermitian adelic vector bundles on proper adelic curves over
countable fields of characteristic zero. Archimedean norms are the usual
real/complex ones; tensor norms are Hilbert at Archimedean places and epsilon
at the other places. The target includes finite families and semistability.

**Status:** the unconditional binary and finite-family theorems are formalized
in [Adelic/Induction/Bost.lean](BostConjecture/Adelic/Induction/Bost.lean), together
with tensor semistability and tensor-product HN compatibility. The proofs use
the actual completed Hilbert/epsilon norms and discharge the geometric slope
and smaller-rank induction hypotheses.
The classical conjecture is formalized in
[Classical/Bost.lean](BostConjecture/Classical/Bost.lean), using that adelic
theorem as its theoretical input.

ArakelovGeometry is an unmodified remote dependency pinned to
`df942e19748f3ab6c41cce7827af7607e2934735`. The reformulated variation
argument and the HN compatibility adapters are local to BostConjecture.
HarderNarasimhan remains pinned at
`14b3090e1e169b77fe381102a1289f24c2b08a11`.
Source reuse is recorded in [CONTRIBUTIONS.md](CONTRIBUTIONS.md).

The public adelic declarations are in namespace
`ArakelovGeometry.AdelicVectorBundle`:

| Declaration | Conclusion |
| --- | --- |
| `maximalSlope_orthogonalTensorPair` | Binary maximal-slope additivity |
| `maximalSlope_orthogonalTensorOfNormMeasurability` | Additivity for any finite family, including the empty family |
| `isSemistable_orthogonalTensorPair` | Binary tensor semistability |
| `isSemistable_orthogonalTensorOfNormMeasurability` | Finite-family tensor semistability |
| `hermitianHNFiltration_orthogonalTensorPair` | Weighted tensor HN compatibility |

The measurability instance `S.NormMeasurabilityHypotheses` follows from countability of the
field through `ArakelovGeometry.AdelicStructure.hasCommonCountableDenseSubfield_of_countable`
in [Adelic/Basic.lean](BostConjecture/Adelic/Basic.lean). Archimedean normalization
is supplied by `S.IsArchimedeanNormalized`. The finite-family conclusions include
empty and singleton families. The empty orthogonal tensor is a semistable line of slope zero.

An `AdelicVectorBundle S` bundles its underlying finite-dimensional vector space
and coerces to that space. The field and the two factors may have independent
universes. Hermitian and `.IsSemistable` hypotheses are instance arguments.
For Hermitian bundles, `isSemistable_iff_isMeanSlopeSemistable` connects the public
HN semistability predicate to the mean-slope criterion used inside the proof.
For example, with `[V.IsHermitian]`, `[W.IsHermitian]`, `[Nontrivial V]` and `[Nontrivial W]`,
`maximalSlope_orthogonalTensorPair V W` proves
`(V ⊗ʰ W).maximalSlope = V.maximalSlope + W.maximalSlope`.
The notation `⊗ʰ` is supplied by ArakelovGeometry for both norm families and
adelic bundles under `open scoped TensorProduct`. Binary and finite-family
tensor semistability are registered instances, so their conclusions can be
obtained with `inferInstance` from the factor instances.

The classical declaration is
`BostConjecture.Arithmetic.HermitianMetric.maxSlope_tensor`. For a number field
`K`, finite projective `𝓞 K`-modules `M` and `N` with nontrivial generic fibres,
and Hermitian metrics `h` and `g`, it proves

```lean
(h ⊗[𝓞 K] g).maxSlope = h.maxSlope + g.maxSlope
```

The statement, metric, tensor notation and maximal-slope definition agree with
commit `81cf08a874039fde5d23c0fbf3970f7d28c3beca`. The proof constructs the
associated adelic bundles, compares their determinant degrees and tensor norms,
and identifies adelic maximal slope with `[K : ℚ]` times the original normalized
maximal slope. Applying Theorem 1.1 and cancelling this positive factor gives
the classical equality, including for nonfree projective modules.
The comparison reuses ArakelovGeometry's rank-zero degree theorem, fractional-ideal
cyclic quotient index formula and generic-fibre spanning theorem.

The local properties `RowStandard`, `ColumnStandard`, `IsStandard` and
`IsCenteredFiltration` are proposition-valued classes. Standardness propagates
through prefixes, extensions and rectangular gluing; a standard tableau also
supplies row and column standardness. Constructors such as `prefixTableau t m hm`
take the tableau as data and infer its standardness. Chosen bases, lifts and
filtrations remain explicit data.

The paper and implementation use the same proof route: hook-length counting,
the full integral Specht lattice with a standard-sublattice Gram upper bound,
and componentwise HN functoriality in the rank induction. The Bost-specific
variation upper/lower bounds and their unstable-case assembly are local to
`Adelic/Induction/{GradedVariation,OptimalVariation,HNVariation}`.
Substantive revisions in `bost.tex`
are blue; setting `\showrevisionsfalse` gives a monochrome reading copy.

The entry point [BostConjecture.lean](BostConjecture.lean) exports both the
adelic theorem module and `Classical.Bost`. The restored number-field definitions
and the adelic comparison proofs are contained in `Classical`; its main theorem
imports the existing Theorem 1.1 directly. Shared tensor, scalar-extension and
representation constructions remain in their existing modules.

## Organization

| Directory | Retained content |
| --- | --- |
| `Adelic` | Actual normed bundles, auxiliary semistability, contractions, geometric slope inequalities, HN variation and the main induction |
| `Classical` | Original integral Hermitian metrics, degrees and maximal slopes, their adelic comparisons, and the classical Bost conjecture |
| `Specht` | Integral orbit lattice, standard basis, seminormal norms, hook counts, prefix probabilities and the covolume limit |
| `Geometry` | Projective tensor constructions, determinant maps, invariant tensors, polynomial polarization and nonvanishing |
| `Arithmetic` | Shared dual base change and representation theory; the restored number-field metrics and slopes are in `Classical` |
| `Tensor` | Tensor regrouping, duality and scalar-extension compatibility |
| `InvariantTheory/Polynomial` | Polynomial actions and homogeneous components used by the geometric argument |
| `ExternalCode`, `ExternalResults` | Selected upstream proofs required by these modules, with provenance and licenses |

File paths organize source modules; they do not change mathematical namespaces.
External sources are grouped by donor. Their namespaces, copyright notices and
licenses are preserved. [CONTRIBUTIONS.md](CONTRIBUTIONS.md) records exact
revisions, selected declarations, adaptations and consumers. All local Lean
modules belong to the single `BostConjecture` library.

## Build and check

Lean and mathlib are pinned to `v4.35.0`. Install Lean through `elan`, then run:

```sh
lake exe cache get
lake build
```

Use `lake --wfail build` to require a build with no warnings. To build the
classical entry point directly, run `lake build BostConjecture.Classical.Bost`.
After building, run the adelic public API and axiom regression checks with:

```sh
lake env lean -j2 Tests/Universes.lean
```

These checks require warning-free elaboration with the same inference-depth
limit as the library. They verify semistability inference, binary and finite-family results, reindexing
across distinct universes, and the axioms of the main results.

The classical statement is also available through the root import. Its axiom
dependencies can be checked in a Lean file with:

```lean
import BostConjecture

#print axioms BostConjecture.Arithmetic.HermitianMetric.maxSlope_tensor
```

The remote dependency revisions are recorded in
[lake-manifest.json](lake-manifest.json). The package enables the mathlib
standard linter set, `relaxedAutoImplicit = false` and
`maxSynthPendingDepth = 3`. The default proof limits are 200,000 heartbeats and
recursion depth 512. Two finite-place determinant comparison lemmas in
[Classical/Adelic/Determinant.lean](BostConjecture/Classical/Adelic/Determinant.lean)
locally use 800,000 heartbeats.

The expected dependencies are Lean's standard foundational axioms
`propext`, `Classical.choice` and `Quot.sound`; no `sorryAx` or additional
mathematical axiom is permitted. The proof does not assume tensor semistability.

Effective asymptotic rates and the appendices remain supplementary manuscript
results outside the formal Theorem 1.1 target and its classical deduction.

## Conventions and license

Code follows the mathlib [style](https://leanprover-community.github.io/contribute/style.html),
[naming](https://leanprover-community.github.io/contribute/naming.html) and
[documentation](https://leanprover-community.github.io/contribute/doc.html)
guidelines. Use existing library results and typeclass inference before adding
local infrastructure. Enumeration needed only inside a proof uses `Finite`
with a local `Fintype.ofFinite`. Use instances for canonical algebraic properties,
such as nontriviality of the integral Specht lattice and its scalar extensions.
Norm families chosen as data remain explicit arguments.

Original code is released under [Apache-2.0](LICENSE). External code retains
its upstream licenses and attribution as recorded in
[CONTRIBUTIONS.md](CONTRIBUTIONS.md).
