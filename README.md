# BostConjecture

The current target is Theorem 1.1 of [this paper](bost.pdf), with the current source in [bost.tex](bost.tex), revised 11 November
2026: maximal slopes are additive under orthogonal tensor products of
positive-rank Hermitian adelic vector bundles on proper adelic curves over
countable fields of characteristic zero. Archimedean norms are the usual
real/complex ones; tensor norms are Hilbert at Archimedean places and epsilon
at the other places. The target includes finite families and semistability.

**Status:** the unconditional binary and finite-family theorems are formalized
in [Adelic/Induction/Bost.lean](BostConjecture/Adelic/Induction/Bost.lean), together
with tensor semistability and tensor-product HN compatibility. The proofs use
the actual completed Hilbert/epsilon norms and discharge the geometric slope
and smaller-rank induction hypotheses.

ArakelovGeometry is an unmodified remote dependency pinned to
`0a608c4f219c4de669be8b6b1a1bc47f996d8d72`. The reformulated variation
argument and the HN compatibility adapters are local to BostConjecture;
see [the dependency record](docs/remote-ag-dependency.md).
HarderNarasimhan remains pinned at
`14b3090e1e169b77fe381102a1289f24c2b08a11`.
Source reuse is recorded in [CONTRIBUTIONS.md](CONTRIBUTIONS.md).

The public adelic declarations are in namespace
`ArakelovGeometry.AdelicVectorBundle`:

| Declaration | Conclusion |
| --- | --- |
| `maximalSlope_orthogonalTensorPair` | Binary maximal-slope additivity |
| `maximalSlope_orthogonalTensorOfMeasurableBase` | Additivity for any finite family, including the empty family |
| `isMeanSlopeSemistable_orthogonalTensorPair` | Binary tensor semistability |
| `isMeanSlopeSemistable_orthogonalTensorOfMeasurableBase` | Finite-family tensor semistability |
| `hermitianHNFiltration_orthogonalTensorPair` | Weighted tensor HN compatibility |

The explicit measurability argument `hS` follows from countability of the field
by `ArakelovGeometry.AdelicStructure.hasCommonCountableDenseSubfield_of_countable`
in [Adelic/Basic.lean](BostConjecture/Adelic/Basic.lean). It adds no assumption to
the paper's theorem. The finite-family conclusions include empty and singleton
families. The empty orthogonal tensor is a semistable line of slope zero.

The paper and implementation use the same proof route: hook-length counting,
the full integral Specht lattice with a standard-sublattice Gram upper bound,
and componentwise HN functoriality in the rank induction. The Bost-specific
variation upper/lower bounds and their unstable-case assembly are local to
`Adelic/Induction/{GradedVariation,OptimalVariation,HNVariation}`.
The [alignment notes](docs/paper-code-alignment.md) record the agreed changes;
the [Chen–Moriwaki interface review](docs/chen-moriwaki-interfaces.md) records
the book statements and their actual uses. Substantive revisions in `bost.tex`
are blue; setting `\showrevisionsfalse` gives a monochrome reading copy.

The entry point [BostConjecture.lean](BostConjecture.lean) imports only the
main adelic theorem module. The local source tree contains its transitive
module dependencies. The separate number-field proof, metric-variation and
compactness branches have been removed. Shared tensor, scalar-extension and
representation constructions remain where the adelic proof uses them.
See [the scope record](docs/main-theorem-scope.md) for the deletion inventory
and the separate discussion of supplementary material in the manuscript.

## Organization

| Directory | Retained content |
| --- | --- |
| `Adelic` | Actual normed bundles, auxiliary semistability, contractions, geometric slope inequalities, HN variation and the main induction |
| `Specht` | Integral orbit lattice, standard basis, seminormal norms, hook counts, prefix probabilities and the covolume limit |
| `Geometry` | Projective tensor constructions, determinant maps, invariant tensors, polynomial polarization and nonvanishing |
| `Arithmetic` | Shared dual base change and representation theory; the old number-field metrics and slope development have been removed |
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

The remote dependency revisions are recorded in
[lake-manifest.json](lake-manifest.json). The package enables the mathlib
standard linter set, `relaxedAutoImplicit = false` and
`maxSynthPendingDepth = 3`. Local proofs use Lean's default limits of
200,000 heartbeats and recursion depth 512 unless a declaration sets a scoped limit.

To audit the final statements after building, check a temporary Lean file containing:

```lean
import BostConjecture

#print axioms ArakelovGeometry.AdelicVectorBundle.maximalSlope_orthogonalTensorPair
#print axioms ArakelovGeometry.AdelicVectorBundle.maximalSlope_orthogonalTensorOfMeasurableBase
#print axioms ArakelovGeometry.AdelicVectorBundle.isMeanSlopeSemistable_orthogonalTensorPair
#print axioms ArakelovGeometry.AdelicVectorBundle.isMeanSlopeSemistable_orthogonalTensorOfMeasurableBase
#print axioms ArakelovGeometry.AdelicVectorBundle.hermitianHNFiltration_orthogonalTensorPair
```

The expected dependencies are Lean's standard foundational axioms
`propext`, `Classical.choice` and `Quot.sound`; no `sorryAx` or additional
mathematical axiom is permitted. The proof does not assume tensor semistability.

The validation records are in [the alignment notes](docs/paper-code-alignment.md)
and [the main-theorem scope record](docs/main-theorem-scope.md). Effective asymptotic rates
and the appendices remain supplementary manuscript results outside the formal
Theorem 1.1 target.

## Conventions and license

Code follows the mathlib [style](https://leanprover-community.github.io/contribute/style.html),
[naming](https://leanprover-community.github.io/contribute/naming.html) and
[documentation](https://leanprover-community.github.io/contribute/doc.html)
guidelines. Use existing library results and typeclass inference before adding
local infrastructure. Enumeration needed only inside a proof uses `Finite`
with a local `Fintype.ofFinite`. Canonical tensor and dual Hermitian cores have
scoped instances; metrics chosen as explicit data remain explicit arguments.
Write their type as `HermitianMetric K M`: the base field is an explicit
parameter because it cannot be recovered from the module type alone.
Operations on an existing metric infer the field from that metric.

Original code is released under [Apache-2.0](LICENSE). External code retains
its upstream licenses and attribution as recorded in
[CONTRIBUTIONS.md](CONTRIBUTIONS.md).
