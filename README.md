# BostConjecture

Lean formalization of Theorem 1.1 of this paper: for positive-rank Hermitian
vector bundles over the ring of integers of any number field, maximal slopes
are additive under the Hilbert tensor product. The project also proves the
finite-family equality and the corresponding semistability statements.
The underlying modules are finite projective; they need not be free.

The principal declarations, in namespace
`BostConjecture.Arithmetic.HermitianMetric`, are:

- `maxSlope_tensor`: the binary maximal-slope identity.
- `maxSlope_piTensor`: the finite-family identity.
- `IsSemistable.tensor`: semistability of a binary tensor product.
- `isSemistable_piTensor`: semistability for a finite family.

The entry point is [BostConjecture.lean](BostConjecture.lean).
The final proofs are in [Main/MaxSlope](BostConjecture/Main/MaxSlope) and
[Main/TensorSemistability](BostConjecture/Main/TensorSemistability).
Weighted Harder–Narasimhan compatibility, effective rates and the appendices
of this paper are outside this formalization's target.

`maxSlope` is defined in
[HN/MaxSlope.lean](BostConjecture/Arithmetic/HN/MaxSlope.lean) as
`((BostConjecture.Subspace.slope h.subspaceDegree).max ⊤).toReal`.
Arithmetic degree finiteness bounds this cut above by `principal h.maxDegree`,
and the ambient slope bounds it below. `subspaceSlope_max_eq` identifies the
cut with `principal h.maxSlope`, independently of the Hermitian HN flag.
The later theorem `slope_hnSubmodule_one` proves that the first saturated HN
term attains it.

## Organization

Directories follow the mathematical dependencies of this paper. File paths
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
200,000 heartbeats and recursion depth 512.

To audit the final statements after building, create a temporary Lean file:

```sh
cat > /tmp/bost-axioms.lean <<'LEAN'
import BostConjecture

#print axioms BostConjecture.Arithmetic.HermitianMetric.maxSlope_tensor
#print axioms BostConjecture.Arithmetic.HermitianMetric.maxSlope_piTensor
#print axioms BostConjecture.Arithmetic.HermitianMetric.IsSemistable.tensor
#print axioms BostConjecture.Arithmetic.HermitianMetric.isSemistable_piTensor
LEAN
lake env lean /tmp/bost-axioms.lean
```

The expected dependencies are Lean's standard foundational axioms
`propext`, `Classical.choice` and `Quot.sound`; no `sorryAx` or additional
mathematical axiom is permitted. The proof does not assume tensor semistability.

The refactored source passes `lake build` with **4,240 jobs and no warnings**.
Transitive axiom probes covering the real-cut conversion, the arithmetic
finiteness bound and the four principal declarations report only the three
foundational axioms above. The root import cone covers all 353 local Lean
modules; source checks find no proof
placeholders or additional axiom declarations.

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
