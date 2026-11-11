# BostConjecture

The current target is Theorem 1.1 of [this paper](bost.pdf), revised 10 November
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

The development reuses ArakelovGeometry at
`0a608c4f219c4de669be8b6b1a1bc47f996d8d72`, HarderNarasimhan at
`14b3090e1e169b77fe381102a1289f24c2b08a11`, and applicable existing modules.
New source reuse is recorded in [CONTRIBUTIONS.md](CONTRIBUTIONS.md).

The public adelic declarations are in namespace
`ArakelovGeometry.AdelicVectorBundle`:

| Declaration | Conclusion |
| --- | --- |
| `maximalSlope_orthogonalTensorPair` | Binary maximal-slope additivity |
| `maximalSlope_orthogonalTensorOfMeasurableBase` | Additivity for a finite nonempty family |
| `isMeanSlopeSemistable_orthogonalTensorPair` | Binary tensor semistability |
| `isMeanSlopeSemistable_orthogonalTensorOfMeasurableBase` | Finite-family tensor semistability |
| `hermitianHNFiltration_orthogonalTensorPair` | Weighted tensor HN compatibility |

The explicit measurability argument `hS` follows from countability of the field
by `ArakelovGeometry.AdelicStructure.hasCommonCountableDenseSubfield_of_countable`
in [Adelic/Basic.lean](BostConjecture/Adelic/Basic.lean). It adds no assumption to
the paper's theorem. The finite-family conclusion includes singleton families.

The current mathematical blueprint starts at
[blueprint/src/content.tex](blueprint/src/content.tex). Its chapters follow
the six adelic proof branches and link to actual Lean declarations and
visually transcribed source pages in the workspace `references/` library.
Each checked attachment is supported by a matching mathematical statement,
kernel check and transitive axiom audit. The source-facing dependency graph
distinguishes explicitly conditional helper statements from the unconditional
main theorem.

Before synchronizing the dashboard DAG, run from the workspace root:

```sh
python3 tools/blueprint_sources.py
horizon graph -p BostConjecture sync
```

Then publish the refreshed DAG with the live dashboard's blueprint sync
action. The generated [graph configuration](blueprint/hgraph-config.yaml)
lists only modules containing blueprint attachments, including the pinned
ArakelovGeometry exports. It avoids scanning the entire dependency tree.

The implementation of [the previous number-field manuscript](old.pdf) remains
available. Its underlying modules are finite
projective and need not be free.

Its principal declarations, in namespace
`BostConjecture.Arithmetic.HermitianMetric`, are:

- `maxSlope_tensor`: the binary maximal-slope identity.
- `maxSlope_piTensor`: the finite-family identity.
- `IsSemistable.tensor`: semistability of a binary tensor product.
- `isSemistable_piTensor`: semistability for a finite family.

The entry point is [BostConjecture.lean](BostConjecture.lean).
The final proofs are in [Main/MaxSlope](BostConjecture/Main/MaxSlope) and
[Main/TensorSemistability](BostConjecture/Main/TensorSemistability).
Effective rates and the appendices remain outside the new target unless needed
by its proof.

`maxSlope` is defined in
[HN/MaxSlope.lean](BostConjecture/Arithmetic/HN/MaxSlope.lean) as
`((BostConjecture.Subspace.slope h.subspaceDegree).max ⊤).toReal`.
Arithmetic degree finiteness bounds this cut above by `principal h.maxDegree`,
and the ambient slope bounds it below. `subspaceSlope_max_eq` identifies the
cut with `principal h.maxSlope`, independently of the Hermitian HN flag.
The later theorem `slope_hnSubmodule_one` proves that the first saturated HN
term attains it.

## Organization

`Adelic/` contains the adelic development: constant Specht bundles,
group semistability, geometric nonvanishing, completed contractions,
geometric slope bounds, and tensor HN induction. `ExternalResults/` contains
new selectively adapted external producers. The legacy directory map
below describes the number-field implementation of `old.pdf`. File paths
organize modules; they do not add layers to the mathematical namespaces.

| Directory | Content | Connection to this paper |
| --- | --- | --- |
| `Arithmetic/Bundle`, `Line`, `Exterior`, `Determinant` | Intrinsic fibers, Hermitian metrics and determinant lines | Section 2 |
| `Arithmetic/Degree`, `Submodule`, `Tensor`, `Dual`, `HN`, `Representation` | Degree calculus, HN filtrations and auxiliary semistability | Section 2 |
| `Specht/Tableau`, `Lattice`, `Branching`, `Seminormal` | Integral polytabloids, branching and normalized Gram formulas | Sections 3–4 |
| `Specht/Counting`, `Asymptotics` | Hook counts, prefix distributions and the covolume limit | Section 5 |
| `Geometry/Tensor`, `Determinant`, `Descent`, `Invariants`, `Polynomial`, `Plucker`, `Contraction` | Integral equivariant determinant contractions | Section 6 |
| `Arithmetic/Specht`, `Slope/Geometric` | Arithmetic realization and the geometric slope bound | Section 6 |
| `Arithmetic/RestrictionCovolume`, `Compactness` | Restriction of scalars, frame compactness and maximizing metrics | Section 7 |
| `Balanced`, `InvariantTheory` | Metric variation, balanced subspaces and the invariant criterion | Sections 6–7 |
| `Main/LineTwist`, `StrictReduction`, `TensorSemistability`, `MaxSlope` | Reduction to the balanced case and final assembly | Section 7 and Theorem 1.1 |
| `Tensor`, `Slope` | Shared tensor and finite-length slope constructions | Supporting APIs |
| `ExternalCode` | Selective upstream ports grouped by source | Standard external inputs |

`Arithmetic/Compactness` is further divided into `Topology`, `Frames`, `Action`
and `Maximum`. `Tensor` separates `Algebra`, `Metric` and `Dual` constructions;
`InvariantTheory` separates polynomials, special-linear groups, Plücker actions
and complex orbit closures.

External sources are grouped under `ExternalCode/OAI`, `Etingof`, `TauCeti`,
`Stacks` and `MathlibPRs`. Their namespaces, copyright notices and licenses
are preserved. Substantially adapted Specht bridge lemmas retain the
project's `BostConjecture.Specht` API. Every external module documents its
source; [CONTRIBUTIONS.md](CONTRIBUTIONS.md) records exact revisions, selected
declarations, adaptations and consumers. All local Lean modules belong to
the single `BostConjecture` library. HarderNarasimhan remains a pinned dependency.

## Build and check

Lean and mathlib are pinned to `v4.35.0`. Install Lean through `elan`, then run:

```sh
lake exe cache get
lake build
```

The exact dependency commits are recorded in
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

On 11 November 2026, `lake build BostConjecture` passed without warnings
(5232 jobs), including the public adelic and legacy entry points. The five
adelic declarations above, the simultaneous rank-induction theorem and the
completed tensor isometry all passed transitive axiom audits with exactly the
three foundational axioms above. Independent source reviews checked the
geometric slope route and the final assembly against the revised manuscript.
Effective asymptotic rates and the appendices are outside this theorem's scope.

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
