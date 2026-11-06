# Reused formalizations

The target is manuscript Theorem 1.1 for arbitrary number fields and positive
ranks. The results below are prerequisites; none proves that theorem by itself.
No claim of authorship is made for upstream code. Only needed module closures
are imported. Each copied file retains upstream notices and identifies local
changes. The installed mathlib revision is pinned in `lake-manifest.json`.

## Hilbert tensors, regrouping and orthogonalization — Mathlib

- Repository: <https://github.com/leanprover-community/mathlib4>.
- Revision: `56a005855ea17e0b0958f73ec801ae140b0a1679` (`v4.35.0`).
- License: Apache-2.0; upstream notices remain in the pinned Lake dependency.
- Direct imports, with no source copying or modifications:
  `Mathlib/Analysis/InnerProductSpace/TensorProduct.lean` supplies the binary
  Hilbert tensor inner product and `TensorProduct.inner_tmul`;
  `Mathlib/Analysis/InnerProductSpace/GramSchmidtOrtho.lean` supplies
  `gramSchmidtBasis`, `gramSchmidt_def''`, `span_gramSchmidt_Iio`, and
  `gramSchmidt_inv_triangular`.
  `Mathlib/LinearAlgebra/TensorProduct/Associator.lean` supplies
  `TensorProduct.tensorTensorTensorComm` and its pure-tensor formula;
  `Mathlib/LinearAlgebra/PiTensorProduct/Generators.lean` supplies
  `PiTensorProduct.submodule_span_eq_top` for nested pure-tensor spanning.
- Consumers: `BostConjecture/Tensor/Hilbert.lean` constructs the positive
  finite tensor form and proves its pure-tensor formula, uniqueness and
  compatibility with factor isometries and reindexing.
  `Tensor/Regroup.lean`, `Tensor/HilbertRegroup.lean` and
  `Tensor/DualRegroup.lean` use the associator and spanning results to prove
  finite tensor interchange, preservation of its Hilbert form and integral
  projective-dual regrouping. Duality-metric compatibility and determinant
  isometry remain separate obligations.
  `Specht/Orthogonal.lean` and `Specht/Spectral.lean` use the actual
  standard-polytabloid basis for monic orthogonalization and content
  eigenvalues. These imports do not supply the adjacent-transposition
  normalization or the covolume asymptotic.
- Toolchain compatibility and transitive axioms are checked in the project
  build and the exact geometry/Specht probes recorded in `verification/`.

## Harder–Narasimhan games — Yijun Yuan

- Repository: <https://github.com/YijunYuan/HarderNarasimhan>
- Revision: `14b3090e1e169b77fe381102a1289f24c2b08a11`.
- License: Apache-2.0; copyright and author notices remain in the unmodified
  Lake dependency. This is the user's project.
- Integration: pinned Lake dependency, Lean/mathlib `v4.35.0`.
- Imports: `HarderNarasimhan.Filtration.Unique`,
  `HarderNarasimhan.PayoffFunction.Slope`, and
  `HarderNarasimhan.PayoffFunction.NashEquilibrium` (13-module source closure).
- Results: HN existence/uniqueness, additive-interval slopes are slope-like,
  and the game/ordinary slope semistability comparison.
- Source: Chen–Jeannin, *Harder–Narasimhan games*,
  <https://arxiv.org/abs/2306.08283>, especially §§2.2, 3.3, 4.3–4.4.
- Intended consumer: arithmetic HN theory in the manuscript's §§2 and 7.
  Still required: saturated subobjects versus generic-fibre subspaces,
  actual Hermitian quotient degrees, degree supermodularity, and Hermitian
  duality. The library's order-dual operation alone is not Hermitian duality.
  Interval degree additivity is distinct from modularity of object degree;
  only supermodularity of the latter is appropriate here.

## Complex Specht modules and Euclidean Mahler compactness — openai/math

- Repository: <https://github.com/openai/math>
- Revision: `4eaee87548250b2682affda7d05d947c05554bae` (upstream Lean 4.34.1).
- License: Apache-2.0, exact upstream `lean/LICENSE` retained at
  `vendor/openai/LICENSE`.
- Source map and original SHA-256 hashes: `vendor/openai/PROVENANCE.json`.
  Local paths preserve the upstream `lean/OAI/` hierarchy under `vendor/openai/OAI/`.
- Copied Specht cone: `RepresentationTheory/Saxl/{Model,Basic,Polytabloid,SpechtSubmodule}.lean`.
  Results include `OAI.Saxl.specht_irreducible` and
  `OAI.Saxl.specht_cyclic_of_ne_zero` for the actual complex orbit span of a
  column-antisymmetrized row tabloid.
- Copied Mahler cone: `NumberTheory/ArithmeticGroups/Lattices/` files
  `ShortestVector`, `ProjectedLattice`, `BasisLift`, `BoundedBasis`,
  `OrthogonalStretch`, `Minkowski/Ellipsoid`, `UniformShortSpan`, `FrameMatrices`.
  The key result is `FrameMatrices.Construction.exists_compact_lattice_frames`
  in that namespace: a compact set of nondegenerate frames containing an
  integral basis of every full discrete real lattice with covolume in a fixed
  positive interval and a common positive lower bound on nonzero vector norms.
- Local changes: Lean 4.35 module headers, public imports and exposed public
  declarations; source/modification notices; removed unused Kronecker
  multiplicity, staircase and Saxl-conjecture code from `Model` and `Basic`.
  Retained theorem statements and proof bodies otherwise unchanged.
- Intended consumers: rectangular Specht irreducibility (§6) and the underlying
  real-lattice compactness step (§7). The project-local
  `BostConjecture/Specht/{Integral,Tableau,Metric}.lean` now consumes this
  Specht cone to construct the integral orbit lattice, prove its equality
  with the all-polytabloid span, identify its complex scalar extension
  equivariantly, and realize its orthonormal word metric. These are original
  bridge proofs using the unmodified vendor declarations. The original local
  `Norm`, `Rectangle`, `Standard`, and `OneRow` modules add the rectangular
  word realization, initial norm, standard-family independence, and one-row
  covolume calculation. `Standard` uses an original lexicographic proof;
  the separately attributed TauCeti adaptation below supplies rational
  straightening. Still required: determinant-isotypic bridges; for
  compactness, restriction of scalars, arithmetic covolume/systole formulas,
  persistence of the integer-ring action, and degree continuity.

## Hook-length formula — Etingof representation-theory formalization

- Repository: <https://github.com/mathlib-initiative/Etingof-RepresentationTheory-draft1>
- Revision: `c6d86a8bd52065aafb8251fa1cdcd55b609743ef` (upstream Lean 4.32.2).
- Source tree: `clean-code/release/RepresentationTheory/`, copied selectively to
  `vendor/etingof/RepresentationTheory/`. The exact release `LICENSE` and
  `NOTICE` are retained at `vendor/etingof/`.
- Root: `RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics`;
  the five-file import closure proves
  `Partition.auxiliaryCard_mul_hookLengthProduct_eq_factorial` in that namespace.
  Despite the upstream generic naming, the objects counted are bijective
  increasing fillings of partition cells and the factors are actual hook lengths.
- Local changes and exact file hashes are recorded in the vendor provenance
  record. Changes update Lean 4.35 visibility and proof elaboration.
- Actual consumer: `Specht/HookCount.lean` identifies the existing enumerating
  standard tableaux with `AuxiliaryPartitionSource` by inversion and derives
  `card_standard_mul_hookProduct`. Its `partitionCell_mem` and
  `partitionCellEquiv` adapt the private `sytCell_iff_mem_toYoungDiagram` and
  `sytCellEquiv` in `Combinatorics/YoungDiagram/CornerStatistics.lean` at the
  same revision, preserving coordinates and attribution. The inverse-tableau
  proofs are new; Lean 4.35 visibility and dependent rewriting are adapted.
  The copied formula's dependency cone is kernel-checked and audited through
  this consumer. Downstream `Specht/ShiftedCount.lean` proves the shifted
  factorial product; `PrefixCount.lean` and `PrefixWeights.lean` prove the
  prefix bijection and exact binomial weight. `PrefixNormalizer.lean`,
  `Separation.lean` and `Asymptotic.lean` now consume these counts through
  labelled normalization and concentration to prove the covolume limit.

## Gram determinants and covolumes — The Tau Ceti contributors

- Repository: <https://github.com/TauCetiProject/TauCeti>.
- Revision: `b3b0334ab9203d9faee4b2f34cd75161463ecdd0`.
- License: Apache-2.0, original `LICENSE` retained at `vendor/tauceti/LICENSE`.
- Extracted from `TauCeti/Analysis/InnerProductSpace/Gram/Hadamard.lean`
  and `TauCeti/Algebra/Module/ZLattice/Covolume.lean` into the 95-line
  `BostConjecture/Lattice/Covolume.lean`. Copyright and attribution are preserved.
  Exact file/declaration hashes and changes are in `vendor/tauceti/PROVENANCE.json`.
- Local changes: backport from Lean 4.36.0-rc2 to 4.35; narrow Mathlib imports;
  derive lattice-inclusion covolume monotonicity using Mathlib's relative-index
  formula, avoiding an additional fundamental-domain comparison helper.
- Results: coordinate Gram determinant, volume of orthonormal fundamental
  domains, Gram formulas for covolumes, and reversal of covolume under lattice
  inclusion, in arbitrary finite-dimensional real inner product spaces.
- Intended consumer: the full-rank standard-polytabloid sublattice's Gram
  determinant bounds the actual integral orbit lattice's covolume. The
  orbit lattice is now constructed as `BostConjecture.Specht.spanLattice`,
  with discreteness and fullness proved. The consumer
  `BostConjecture.Specht.covolume_sq_eq_integer_gram` applies the copied
  Gram theorem, and `one_le_covolume` derives its lower bound.
  `covolume_sq_le_det_gram` now consumes the copied lattice-inclusion theorem
  and span Gram formula for an integral real basis, with that hypothesis
  explicit. `oneRow_covolume_eq_one` supplies an actual integral basis and
  computes its covolume. `standardRealBasis` now supplies the standard
  integral real basis to `covolume_sq_le_det_standard_gram`; the seminormal
  Gram formula remains open. No TauCeti Lake
  dependency was added.

## Rational Garnir straightening — The Tau Ceti contributors

- Repository: <https://github.com/TauCetiProject/TauCeti>, revision
  `b3b0334ab9203d9faee4b2f34cd75161463ecdd0`; Apache-2.0, with the original
  license at `vendor/tauceti/LICENSE` and notices in each adapted file.
- `TauCeti/RepresentationTheory/Symmetric/Specht/Garnir.lean`: adapted
  `exists_ne_rowIndex_relabel_eq`, the signed Garnir relation, Garnir set
  definitions, cardinality and internal-column-permutation lemmas to
  `BostConjecture/Specht/{Garnir,GarnirSets}.lean`.
- `TauCeti/RepresentationTheory/Symmetric/Specht/Straightening.lean`: adapted
  the collected internal multiplicity and rational span lemmas, bounded
  straightening weight, strict-progress lemmas and
  `polytabloid_mem_span_polytabloid_standard` to `Garnir.lean` and
  `Straightening.lean`.
- Selected helpers only: `Combinatorics/Young/Diagram.lean`'s
  `card_filter_fst_lt_filter_snd_eq`; `Algebra/BigOperators/Finset/Swap.lean`'s
  `sum_swap_apply_add`; `Algebra/Order/BigOperators/Sum/LtSum.lean`'s
  `sum_lt_sum_of_forall_lt` and `sum_lt_sum_image_sdiff` (all paths under
  `TauCeti/`). Helpers are private within their consuming modules.
- Modifications: port to Lean 4.35; use existing `OAI.Saxl.Tableau n μ`
  and integral word polytabloids; remove the categorical permutation module
  and all its imports; prove cancellation directly over the integers by a
  finite-sum involution; extend coefficientwise to rationals; use the existing
  standardness predicate and prove the label/cardinality bridge. No alternate
  tableau, representation or lattice was introduced.
- Consumer: `BostConjecture.Specht.polytabloidRat_mem_span_standard` supplies
  rational spanning to `Basis.lean`, whose original scalar-extension and
  basis proofs construct `standardRealBasis`, establish the integral rank
  formula, and apply `covolume_sq_le_det_standard_gram`. Division by a positive internal multiplicity
  occurs over the rationals: no integral basis claim is made.
- Only these needed proof pieces are adapted, with their local dependency cone
  checked. Source hashes and target modules are recorded in
  `vendor/tauceti/PROVENANCE.json`; transitive axiom probes are recorded in
  `verification/SpechtAxioms.lean` and results in `verification/RESULTS.md`.

## Alternating-tensor determinant covariance — AxiomMath/Stacks

- Repository: <https://github.com/AxiomMath/Stacks>, revision
  `012108f61d7f92a6ffc35ec3f263b6da5d438125`.
- Original path: `StacksFrontier/LinearAlgebra/Matrix/AlternatingTensorPower.lean`.
  Exactly eight declarations, from `Matrix.altVec` through
  `Matrix.sum_tensorPow_mul_altVec`, are extracted into
  `BostConjecture/LinearAlgebra/AlternatingTensorPower.lean`.
- License: Apache-2.0; the exact license is retained in `vendor/stacks/LICENSE`.
  [Per-declaration provenance](vendor/stacks/PROVENANCE.json) records hashes,
  modifications, toolchain versions, and the checked dependency cone.
- Changes: scoped module documentation and deprecated conditional-lemma names
  updated for Lean/mathlib 4.35. Only three Mathlib imports; no Stacks dependency.
  Extraction was durably recorded at workspace-ledger commit `c1ce881`.
- Consumer: the original bridge `Specht/ColumnTensor.lean` identifies the
  existing rectangular polytabloid coefficients with a product of `altVec`
  coordinates. `Specht/Covariance.lean` consumes the extracted
  `Matrix.sum_tensorPow_mul_altVec` to prove the actual word matrix action
  on every rectangular polytabloid, integral lattice vector, its scalar span,
  and the checked complex Specht module is multiplication by `det u ^ k`.
  Its pure-tensor formula applies the matrix separately to each factor.
  Projective-module gluing and invariant-space equality
  remain separate mathematical obligations.
- The extraction's eight transitive axiom probes are in
  `verification/StacksAxioms.lean`; the module and all probes were checked by
  the parent extraction session, separately from the preceding Specht build.

## Selective Mathlib PR ports

These user-approved ports retain the Lean/mathlib 4.35 pins and the exact
Apache-2.0 licenses and author notices. They are checked local producers
from proposals that were unmerged when retrieved. Detailed original paths,
export lists, file hashes, adaptations and axiom checks are in the linked
provenance records; no arithmetic or analytic Bost bridge follows merely
from importing them.

- **Exterior base change, #40948 — Nailin Guan.**
  Repository `Thmoas-Guan/mathlib4_fork`, revision
  `b642b6723caf97b7b462dd5ddeabb0226c3b5433`.
  `Mathlib/LinearAlgebra/ExteriorPower/BaseChange.lean` and two projections
  from `ExteriorAlgebra/Grading.lean` are ported to
  `BostConjecture/LinearAlgebra/ExteriorPower/` with adjusted imports;
  proof bodies are unchanged. The five public exports include
  `exteriorPower.baseChangeEquiv` and both pure-tensor formulas.
  Intended consumers: determinant and Plucker scalar extension.
  [Provenance and license](vendor/mathlib-prs/40948/PROVENANCE.json).
- **Finite projective tensor duality, #44845 — Daniel Horton.**
  Repository `DanielJHorton/mathlib4`, revision
  `47365e3b9fd4329f058c31ac7aa9565a6036b17d`.
  `Mathlib/LinearAlgebra/PiTensorProduct/Projective.lean` and three
  `Dual/Defs.lean` declarations are ported to
  `BostConjecture/LinearAlgebra/PiTensorProduct/`; two missing reindex
  simplifications are proved inline. Ten exports include
  `PiTensorProduct.piTensorHomEquiv` and
  `PiTensorProduct.dualDistribEquivOfProjective`.
  Intended consumer: contractions over nonfree finite projective
  integer-ring modules. [Provenance and license](vendor/mathlib-prs/44845/PROVENANCE.json).
- **Polar decomposition, #45002 — Tjeerd Jan Heeringa.**
  Repository `TJHeeringa/mathlib4`, revision
  `41260205df493c627e1ac0e54812cfdeb6517fbc`.
  `Mathlib/Analysis/InnerProductSpace/{Abs,Polar}.lean` is ported to
  `BostConjecture/Analysis/InnerProductSpace/` with one relocated import
  and documentation corrections; the 30 declarations and proofs are
  unchanged. Actual consumers: `Balanced.SpecialLinearPolar` and
  `Balanced.OrbitNorm`, proving unitary/logarithm/determinant adapters and
  the full special-linear orbit norm bound on complex Hilbert spaces.
  The algebraic orbit criterion remains open.
  [Provenance and license](vendor/mathlib-prs/45002/PROVENANCE.json).

The parent checked all three narrow module builds and all 45 export axiom
probes before this session integrated their root imports. See
[reuse survey](verification/STACKS_AND_MATHLIB_PRS.md) for the parent review
and the exact separation between these producers and their future consumers.

## Central Specht action consumer — session 0013

`Specht/Central.lean` substantively consumes `OAI.Saxl.columnAlt_tabloid`
from the already pinned OpenAI copy (original path
`lean/OAI/RepresentationTheory/Saxl/SpechtSubmodule.lean`, revision
`4eaee87548250b2682affda7d05d947c05554bae`, Apache-2.0).
No additional source is copied or modified. The consumer proves that the
central transposition sum acts by total diagram content, first on complex
standard polytabloids, then on the actual real Specht span and integral orbit
lattice. Its scalar is computed by the new local `Content.lean` proofs.
The transitive axiom probe includes this imported rank-one producer.

## Geometry integration consumers — session 0013

The checked local modules `Geometry/TensorRealization.lean` (0d893d5),
`Tensor/Evaluation.lean` (1c0ac0c), and `Geometry/FreeEmbedding.lean`
(922a2f4) are now root imports. Tensor realization consumes the attributed
Stacks tensor-coordinate equivalence and the existing integral Specht
covariance; evaluation consumes the attributed finite-projective tensor
and duality port. Free embedding consumes the canonical orbit-lattice
inclusion and flat scalar extension. No additional external code is copied.
The free embedding is injective under flatness over the integers; its
covariance and frame transition hold over every commutative ring.
Projective gluing, restricted isotypic nonvanishing, invariant-space equality,
and the archimedean norm estimate remain separate obligations.

## Intrinsic arithmetic line integration — session 0013

`Arithmetic/HermitianLine.lean` is now a root import. It consumes Mathlib's
checked product formula, fractional-ideal norm, lattice-index and
projective/flat APIs at the existing pinned Mathlib revision; no external
code is copied or modified. Its local consumers include choice-independent
intrinsic line degree and the actual finite quotient-cardinality formula
for nonfree finite projective lines over every number field. Source blobs,
22 foundational-only axiom probes and original checks are recorded in
`verification/ARITHMETIC.md`. Determinant/higher-rank degree calculus and
intrinsic Harder–Narasimhan specialization remain open.

## Prefix restriction and branching support — session 0015

`Specht/Prefix.lean`, `Specht/Branching.lean` and `Specht/Filtration.lean`
are original local proofs in the existing word/tableau model; no external
source is copied. They reuse Mathlib's `YoungDiagram`, finite equivalences,
`Equiv.Perm.extendDomain` and `sign_extendDomain` at the pinned revision,
and substantively consume the checked local standard basis and central
content action. The latter retains the attributed OpenAI rank-one dependency
above. Consumers are the smaller polytabloid slice, the sliced central action,
and the invariant largest-label support filtration. The branching quotient,
colexicographic triangularity and general covolume limit remain open.

## Determinant scalar-extension integration — session 0015

`Geometry/DeterminantBaseChange.lean` (checked handoff `3ac7a36`) is now a
root import, including the top exterior-power frame twist and tensor
scalar-extension map. Its original exact checks and 38 foundational-only
axiom probes are recorded in `verification/GEOMETRY.md`. It consumes the
attributed exterior-power and tensor-coordinate APIs above; no new external
code is copied. The equality is the scalar-extension square on elementary
inputs for arbitrary source and target frames. Projective descent and global
injectivity remain separate unproved obligations. The checked
`Geometry/DeterminantNaturality.lean` (7c76270) is also imported; it proves
naturality for arbitrary maps between free modules of the same rank. The
lightweight determinant-coordinate extraction d470bdb is shared with arithmetic.
Its 42-export audit and post-extraction build are recorded in the same evidence.

## Determinant degree construction integration — session 0015

`Arithmetic/Degree.lean` (checked source 6429efa and 5d59bb0; evidence
af132a7) is now imported. The actual finite-projective determinant line and
its complex Gram metric consume the attributed exterior base-change API
and Mathlib at the existing pins, with the shared lightweight local
`Geometry/DeterminantCoordinates.lean`; no additional external source is
copied. The construction, normalized degree/slope and actual determinant
quotient formula apply to arbitrary number fields and nonfree modules.
The 40-probe audit and 3,241-job module check are recorded in
`verification/ARITHMETIC.md`. Metric uniqueness/frame independence,
zero/rank-one normalization, degree calculus and intrinsic HN remain open.

## Branching quotient and last content action — session 0017

`Specht/Quotient.lean` and `Specht/LastMurphy.lean` are original local
proofs, with no new external source copying. They retain the canonical
orbit lattice and its Hilbert word realization. They consume the existing
standard basis, prefix restriction and support filtration, Mathlib's
`LinearMap.quotKerEquivOfSurjective` and `Submodule.quotEquivOfEq`, and
`Function.Injective.map_swap` at the pinned Mathlib revision above.
The exact kernel theorem is consumed to prove central prefix action modulo
the preceding filtration step, then the last Murphy content scalar. The
OpenAI antisymmetrizer theorem remains a transitive dependency of the central
content producer, with its attribution unchanged. Recursive colex triangularity,
seminormal norms and the general covolume limit are still open.

## Principal-cover descent integration — session 0017

Checked handoffs `e4812e5` and `f58c467` extend the determinant-twist
base-change identity to its full scalar-linear square and provide
`Geometry/LocalizationDescent.lean`, now a root import. Original proofs
clear denominators and combine a unit-ideal relation to descend compatible
linear maps and detect injectivity. No additional code was copied from
Stacks or any other external project. The pinned tensor/exterior APIs above
are retained; `verification/GEOMETRY.md` records the 9,068-job build and
59 foundational-only axiom probes. Finite-projective local frames and
overlap transport must still be supplied before constructing the global
integral injection.

## Normalized seminormal norms and Gram evaluation — session 0021

`Specht/Adjacent.lean`, `ColumnReading.lean`, `AdjacentPath.lean`,
`PrefixNorm.lean`, `PrefixNormInitial.lean` and `Seminormal.lean` are original
local proofs in the existing tableau/word representation. No new external
source was copied. They substantively consume the attributed OpenAI Specht
cone through the checked content eigenvalues and local standard basis.
The canonical integral orbit lattice and its orthonormal Hilbert metric are
unchanged. The normalization and explicit prefix product are now proved,
not assumed from the Ryom-Hansen/Murphy reference.

Direct Mathlib reuse retains the repository, exact revision and Apache 2.0
license recorded above. Used declarations include
`InnerProductSpace.ext_inner_left_basis`
(`Mathlib/Analysis/InnerProductSpace/Dual.lean`),
`Fin.strictMono_iff_lt_succ` (`Mathlib/Order/Fin/Basic.lean`),
`Finset.prod_range_reflect` (`Mathlib/Algebra/BigOperators/Intervals.lean`)
and `Nat.factorial_eq_prod_range_add_one`
(`Mathlib/Data/Nat/Factorial/BigOperators.lean`). They are imported unchanged;
consumers are spectral-line separation, legal paths and the initial product.
Exact new-producer audits and source blobs are in `verification/RESULTS.md`.
The general sublinear covolume limit is still open.

## Checked arithmetic and geometric integration — session 0021

The root additionally consumes the owners' checked
`Arithmetic.NestedQuotient`, `SaturationDegree`, `LineTensorDegree` and
`DualFiber` leaves, and `Geometry.ProjectiveMetric`, `Contraction` and
`Tensor.DualMetric` (transitively including the delivered determinant metric,
position action and projective permutation modules). These are original local
proofs with the existing pinned dependencies. No new external code was copied.
Their separate 135-probe arithmetic and 131-probe geometry audits are recorded
in `verification/ARITHMETIC.md` and `verification/GEOMETRY.md`. They do not
close arbitrary-rank degree identities/HN, the restricted pairing norm bound,
or the main theorem. Later leaves are outside this fixed import batch.

## Labelled occupancy counting — session 0026

`Specht/Hypergeometric.lean` is an original finite-subset proof of the
multivariate hypergeometric law. It imports unchanged Mathlib declarations
`Fintype.card_finset_len` (`Mathlib/Data/Fintype/Powerset.lean`),
`Fintype.card_sigma` and `Fintype.card_pi`
(`Mathlib/Data/Fintype/BigOperators.lean`) at the pinned revision and
Apache 2.0 license recorded above. The concrete block bijection consumes
these counts; its sum identity proves probability normalization.
No external code was copied and no new dependency was added.

`Specht/OccupancySort.lean` additionally imports unchanged
`Tuple.sort`, `Tuple.monotone_sort`, `Tuple.unique_antitone`
(`Mathlib/Data/Fin/Tuple/Sort.lean`) and `Matrix.det_vandermonde_ne_zero_iff`
(`Mathlib/LinearAlgebra/Vandermonde.lean`) at that same revision and license.
The concrete tuple equivalence consumes sorting; determinant permutation
and nonvanishing prove the actual squared-Vandermonde weight's symmetry
and collision vanishing, feeding its factorial sum identity.

`Specht/ShiftedShapes.lean` uses the unchanged `YoungDiagram.ofRowLens`
and `YoungDiagram.rowLen_ofRowLens` from
`Mathlib/Combinatorics/Young/YoungDiagram.lean` to construct actual
subdiagrams after staircase subtraction. Both inverse identities and the
cardinality statement are local proofs; no alternate partition model is added.

`Specht/PrefixDistribution.lean` uses the unchanged `Equiv.sigmaFiberEquiv`
from `Mathlib/Logic/Equiv/Sum.lean` to count the actual prefix fibers, then
combines the preceding original producers with the squared Vandermonde
determinant identity. It adds no dependency or external copied code.

`Specht/PrefixNormalizer.lean` evaluates the rectangle count and normalizer
by original finite-product proofs, using unchanged Mathlib factorial and
interval-product identities at the same pinned revision. Its explicit
probability theorem consumes the actual prefix-fiber count. No additional
concentration or asymptotic result is imported or assumed.

The checked root batch includes the owners' original
`Arithmetic.DeterminantProduct`, `IntegralDeterminantProduct`,
`IntegralExactDeterminant` (including projective determinant shear),
`Geometry.ContractionBaseChange`, and `Balanced.PluckerNorm`
(including exponential flow) leaves. Their provenance and separate scoped
audits remain in the arithmetic, geometry and balanced verification records.
The shared root build is integration evidence, not completion of those tasks.

The complex exterior Gram metric and Plücker consumer delivered at `76a3ad5`
reuse Mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679`
(Apache-2.0): `Module.Basis.exteriorPower` and its coordinate API in
`Mathlib/LinearAlgebra/ExteriorPower/Basis.lean`, `pairingDual` and
`pairingDual_ιMulti_ιMulti` in `Mathlib/LinearAlgebra/ExteriorPower/Pairing.lean`,
and Euclidean coordinate transport in `Mathlib/Analysis/InnerProductSpace/PiL2.lean`.
These imports are unchanged; no source was copied. Original local proofs
construct the full complex exterior metric, identify its Gram norms, and prove
the actual exterior isometry and balanced Plücker norm stationarity.
They also consume the existing `Tensor.inner_ext_of_span` uniqueness lemma.
The real-only Mathlib exterior metric is not used as a substitute for this
complex producer. The separate analytic convexity and semistability results
remain open. The intrinsic exact-determinant handoff at `9ed74af` is original
local code using the already attributed exterior and projective infrastructure.

## Orbit-criterion mathematical references — session 0026

The BALANCED lane registered Maithani, *Splittings and the Reynolds Operator*,
arXiv:2412.18841v2 (11 September 2025), and Milne, *Algebraic Geometry*,
v6.10 (11 November 2024), at `55fdc42`. Exact original files, SHA256 hashes,
license notices and source anchors are recorded in `references/manifest.yaml`
and `verification/BALANCED.md`. Maithani Theorem 5.6 and Proposition A.6
support the finite-degree averaging and density blueprint; Milne Theorem 9.7
and Aside 9.8 support constructibility and closure comparison. The Milne
page-201 file is a normalized statement excerpt, not a full transcription.
No Lean code was copied from either reference. The orbit criterion and its
used external results remain unproved Lean obligations.

## Finite sampling and concentration — session 0028

Session 0028 adds original finite-product and subset-counting proofs in
`Specht/BulkNormalizer.lean` and `Specht/Sampling.lean`. They import unchanged
Mathlib at `56a005855ea17e0b0958f73ec801ae140b0a1679` (Apache-2.0):
`Nat.factorial_mul_ascFactorial`, `Nat.ascFactorial_le_pow_add` and
`Nat.descFactorial_pos` in `Mathlib/Data/Nat/Factorial/Basic.lean`, product
formulas in `Mathlib/Data/Nat/Factorial/BigOperators.lean`, `Nat.choose_mul`
in `Mathlib/Data/Nat/Choose/Basic.lean`, and `Finset.card_powersetCard`
in `Mathlib/Data/Finset/Powerset.lean`. The concrete normalizer lower bound
consumes the rising-factorial identities; the sampling moment bound consumes
the subset count and falling-factorial inequality. No external source was copied.

The new integration imports are original owner-delivered
`Arithmetic.ExactDegree`, `Geometry.ContractionNorm`, and
`Balanced.SpectralExpansion`, together with `InvariantTheory.Semistability`.
The final geometry batch also includes the original local
`Geometry.InvariantBaseChange`, `PiInvariants`, and `PolynomialTensor`;
their pinned-library reuse and 184-probe audit are recorded in
`verification/GEOMETRY.md`. No external source was copied by this integration.
The spectral expansion uses unchanged Mathlib
`Mathlib/Analysis/InnerProductSpace/Spectrum.lean`,
`Mathlib/Analysis/SpecialFunctions/Exponential.lean`, and
`Mathlib/Analysis/Convex/Deriv.lean` at the same revision and license for the
actual exterior-norm spectral expansion and convexity. The owner audit files
record their exact consumers and remaining theorem boundaries.

`Specht/OccupancyMGF.lean` uses the unchanged
`Real.norm_exp_sub_one_sub_id_le` and `Real.add_one_le_exp` in
`Mathlib/Analysis/Complex/Exponential.lean` to bound the centered exponential
moment, then proves finite exponential Markov and union bounds locally.
The actual occupancy law is retained through `occupancyEquiv`. The sufficient
tail constant is weaker than the manuscript's Hoeffding constant; the
blueprint explicitly records that adaptation and its asymptotic sufficiency.
The invariant-polynomial handoff imports unchanged
`Mathlib/LinearAlgebra/SymmetricAlgebra/Basic.lean`,
`Mathlib/RingTheory/Finiteness/Subalgebra.lean`, and
`Mathlib/RepresentationTheory/Invariants.lean` at the same pinned revision
and license. Their consumers are the owners' intrinsic polynomial evaluation,
homogeneous subspace, action and invariant-to-semistability proofs.

## Sublinear Specht covolume — session 0030

The proofs in `Specht/WeightedGap.lean`, `BulkGap.lean`,
`GapAsymptotics.lean`, `PrefixEvent.lean`, `Separation.lean`,
`LogInsertion.lean`, `LogExpectation.lean`, and `Asymptotic.lean` are
original local code. They use unchanged Mathlib at
`56a005855ea17e0b0958f73ec801ae140b0a1679` (Apache-2.0):
`Matrix.det_vandermonde` in `Mathlib/LinearAlgebra/Vandermonde.lean`;
real-power/exponential limits in
`Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean` and
`Pow/Real.lean`; finite expectations in
`Mathlib/Algebra/{,Order/}BigOperators/Expect.lean`; ceiling bounds in
`Mathlib/Algebra/Order/Floor/Semiring.lean`; and reciprocal limits in
`Mathlib/Analysis/SpecificLimits/Basic.lean`.
The actual consumers are the weighted bad-gap estimate, its uniform
bulk decay, the actual-tableau logarithmic average and the canonical
orbit lattice limit. No probability, invariant-space or semistability
conclusion is assumed. The sufficient concentration constant and the
full-rank standard-sublattice comparison are documented adaptations of
the manuscript; the original integral orbit lattice is unchanged.

## Symmetric polarization — The Tau Ceti contributors

- Repository: <https://github.com/TauCetiProject/TauCeti>.
- Exact revision: `3c3a32baea963db05c302adeb307b22baae4de78`.
- Original paths: `TauCeti/LinearAlgebra/SymmetricPower/{Basic,Lift,Algebra}.lean`.
  Copyright 2026 The Tau Ceti contributors; Apache-2.0. Exact hashes,
  immutable upstream files and the license are retained in
  [vendor provenance](vendor/tauceti-polarization/PROVENANCE.md).
- Local paths: `BostConjecture/LinearAlgebra/SymmetricPower/`.
  The selected quotient/lift, tensor section, factorial-composite,
  naturality and homogeneous-algebra comparison declarations are retained.
  The algebra namespace is changed to `BostConjecture.SymmetricPower`;
  Lean 4.35 imports and elaboration are adapted as listed in provenance.
  Basis, monomial and WordFiltration cones are omitted.
- Actual consumers: `Geometry.PolynomialPolarization` constructs the
  equivariant symmetric lift with nonzero evaluation;
  `PluckerPolarization` and `DegreeDivisibility` apply it to the actual
  Plucker polynomial. Port commits `47c79f2`, `d56b70d`; initial consumer
  `c55300f`. The 226-probe owner audit uses only foundational axioms.
  Upstream Lean 4.36.0-rc2 is adapted to this project's unchanged Lean 4.35.
  Rectangular invariant spanning and coaction are separate obligations.

## Additional integrated consumers — session 0030

The arithmetic tensor degree, subspace supermodularity, bounded-sections
and HN interval proofs are original local code. `Arithmetic.SubspaceHN`
and `Slope.FiniteLength` consume `GameValue`, `NashEquilibrium`, and
`Filtration.Exists` from the already attributed pinned HarderNarasimhan
revision `14b3090e`; they prove actual intermediate quotient slope bounds.
The checked `Arithmetic.HermitianHN` consumer at `fb56e97` now proves
semistability of actual HN grades against all integral submodules, attained
maximal slope and containment of every maximizer in the first saturated term.
It uses unchanged Mathlib quotient, submodule correspondence and finite-projective
APIs, with no additional copied code. The 287-probe owner audit is foundational-only.
HN uniqueness and bounded-degree finiteness were separate at that checkpoint;
the completed owner delivery is now integrated at cf39176.
`Arithmetic.ArchimedeanFiniteness` uses unchanged Mathlib
`NumberField.Embeddings.finite_of_norm_le` and finite-projective coordinate
embeddings to prove finiteness of bounded actual integral sections.
This does not assert bounded-degree finiteness. Exact owner checks are in
`verification/ARITHMETIC.md`.

`Balanced.SpecialLinearPolar` uses unchanged Mathlib continuous functional
calculus logarithms (`Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog/Basic.lean`,
Frédéric Dupuis, Apache-2.0) and trace/eigenvalue/determinant formulas.
`Balanced.OrbitNorm` consumes this polar factorization and the checked
tensor exponential identity to exclude zero from the Euclidean orbit
closure. Exact declarations and audits are in `verification/BALANCED.md`.
All Mathlib imports here use the pinned revision above without copying.

`InvariantTheory.PluckerCoordinates`, `SpecialLinearCoordinates` and
`Coaction` also use that unchanged Mathlib dependency: tensor-product
basis coordinates (`LinearAlgebra/TensorProduct/Basis.lean`), exterior
basis/minor formulas (`LinearAlgebra/ExteriorPower/Basis.lean`), determinant
maps (`LinearAlgebra/Determinant.lean`), `Matrix.SpecialLinearGroup`,
`Ideal.Quotient.liftₐ`, `Algebra.FiniteType.quotient`, and
`Submodule.toBaseChange.toLinearEquiv` (`RingTheory/Flat/Basic.lean`).
Their consumer is the actual degree-restricted polynomial coordinate
pullback for the Plucker action, with the forward convention documented
in `verification/BALANCED.md`. The 120-probe owner audit is foundational-only.
This is not a proof of rational-point detection or invariant base change.

## Schur-Weyl permutation commutant — The Tau Ceti contributors

- Repository: <https://github.com/TauCetiProject/TauCeti>.
- Exact revision: `b3b0334ab9203d9faee4b2f34cd75161463ecdd0`.
- License: Apache-2.0; copyright 2026 The Tau Ceti contributors. Original
  notices and all 14 immutable source/license/toolchain files are preserved
  under [vendor/tauceti-schur-weyl](vendor/tauceti-schur-weyl/PROVENANCE.md),
  with SHA256 and git blob hashes in `MANIFEST.json`.
- Exact original paths/declarations and local mapping are listed individually
  in the provenance table. The selected slices are multilinear polarization,
  the generic permutation action and its invariants, finite-projective
  comparison-map commutant, semisimple image double centralizer, and
  invertible diagonal density. Local modules are
  `BostConjecture/RepresentationTheory/SchurWeyl/`.
- Adaptations: direct averaging replaces the upstream norm-map dependency;
  the existing checked Mathlib PR44845 `piTensorHomEquiv` replaces TauCeti's
  tensor-Hom infrastructure; the endpoint is generalized from coordinate
  spaces to arbitrary finite-dimensional modules. Pinned 4.35 API changes
  are recorded in the mapping. No full TauCeti dependency, categorical
  representation layer, highest-weight classification or toolchain change.
- Actual consumers: `Geometry.RectangularCovector`, `RectangularSpan` and
  `RectangularInvariants` construct the bilinear coefficient covector,
  rank-one commutant operator, integral orbit-action transport and determinant
  root normalization. The final result identifies actual SL-fixed tensors
  with the scalar-extended rectangular lattice over algebraically closed
  characteristic-zero fields. Source snapshot `26489ca`, checked evidence
  pin `2a0d5c6`; all254 transitive owner probes are foundational-only.
  Independent source review checked raw upstream hashes and all consumer
  bridges. Field descent and contraction nonvanishing remain open.

`Tensor.HomDual` and `Geometry.HomTensor` are original local composition and
consumer proofs. They use unchanged pinned Mathlib `Module.evalEquiv`,
`dualTensorHomEquiv`, `TensorProduct.dualDistribEquiv` and the previously
attributed finite-projective PiTensor duality, then connect to the actual
polynomial quotient and canonical tensor pairing. No copied code, freeness
hypothesis or new arithmetic representation is introduced.

## Verification

Run `horizon --root ../.. check --json` from this project, then
`horizon --root ../.. check --lean verification/ReuseAxioms.lean --json`.
The latter audits the transitive axioms of the named reused producers.
Source inspections and successful prerequisite builds do not certify the
unwritten arithmetic bridges or main theorem. Current evidence is recorded in
`verification/RESULTS.md` once the corresponding checks finish.

## Shared integration of invariant detection, HN symmetry and closure prerequisites

All imports in this batch use the unchanged Apache-2.0 Mathlib dependency
`https://github.com/leanprover-community/mathlib4` at
`56a005855ea17e0b0958f73ec801ae140b0a1679`; no upstream file was copied or
modified. The following are original project proofs consuming those APIs.

- `InvariantTheory/LocalizationDetection.lean`, `SpecialLinearDetection.lean`
  and `InvariantDetection.lean` use localization-away lifting/surjectivity
  (`RingTheory/Localization/Away/Basic.lean`), infinite-field polynomial
  extensionality, `TensorProduct.equivFinsuppOfBasisRight`
  (`LinearAlgebra/TensorProduct/Basis.lean`), and
  `Matrix.SpecialLinearGroup.toLin_equiv`
  (`LinearAlgebra/SpecialLinearGroup.lean`). Their actual consumer is the
  equality of the existing homogeneous invariant space with the kernel of
  the explicit polynomial coaction minus the trivial coaction.
- `InvariantTheory/SpecialLinearBaseChange.lean` uses
  `Algebra.TensorProduct.tensorQuotientEquiv`
  (`RingTheory/TensorProduct/Quotient.lean`),
  `MvPolynomial.algebraTensorAlgEquiv`
  (`RingTheory/TensorProduct/MvPolynomial.lean`) and
  `Ideal.quotientEquivAlg` (`RingTheory/Ideal/Quotient/Operations.lean`)
  for the actual determinant-one coordinate-algebra comparison. The
  homogeneous coaction square remains its next consumer.
- `InvariantTheory/OrbitImage.lean` uses canonical
  `MvPolynomial.zeroLocus` from `RingTheory/Nullstellensatz.lean` to identify
  the actual Plücker orbit with the polynomial image of determinant-one
  equations. It does not invoke a Nullstellensatz conclusion.
- `Arithmetic/HNUniqueness.lean`, `HNIsometry.lean` and
  `IrreducibleSemistable.lean` use canonical quotient/submodule maps, the
  pinned HarderNarasimhan uniqueness API recorded above,
  `Module.End.baseChangeHom` and `Representation.IsIrreducible` from
  `RepresentationTheory/Irreducible.lean`. The consumer is intrinsic
  semistability of an integral isometric action with irreducible generic
  representation; tensor/dual irreducibility is a separate producer.
- `InvariantTheory/ComplexClosure/Coordinates.lean` uses
  `SymmetricAlgebra.equivMvPolynomial`, `equivMvPolynomial_symm_X`
  (`LinearAlgebra/SymmetricAlgebra/Basis.lean`), canonical `zeroLocus` and
  `vanishingIdeal` (`RingTheory/Nullstellensatz.lean`), `continuous_eval`
  (`Topology/Algebra/MvPolynomial.lean`) and `continuous_equivFun_basis`
  (`Topology/Algebra/Module/FiniteDimension.lean`). The consumer is the
  coordinate description of intrinsic polynomial Zariski closure and its
  one-sided Euclidean closure inclusion.
- `InvariantTheory/ComplexClosure/Roots.lean` uses `Complex.isAlgClosed`
  (`Analysis/Complex/Polynomial/Basic.lean`),
  `Splits.eval_eq_prod_roots_of_monic`, `Splits.natDegree_eq_card_roots`
  (`Algebra/Polynomial/Splits.lean`), `IsRoot.norm_lt_cauchyBound`
  (`Analysis/Polynomial/CauchyBound.lean`), `Multiset.exists_min_image`
  (`Data/Finset/Max.lean`) and `Tendsto.bddAbove_range`
  (`Topology/Order/LiminfLimsup.lean`). Its intended consumer is the pending
  finite-normalization openness argument. Neither the closure equality nor
  Lemma 7.2 follows from these imports.

Exact delivered revisions, kernel checks, axiom probes and independent
reviews are recorded in `verification/BALANCED.md`, `ARITHMETIC.md` and
`COMPLEX_CLOSURE.md`; shared root evidence is in `verification/RESULTS.md`.

The same shared batch adds `InvariantTheory/PolynomialBaseChange.lean`
(`35d1080`): the actual matched-basis polynomial algebra equivalence and
homogeneous image characterization use the above `equivMvPolynomial` and
`algebraTensorAlgEquiv` unchanged. The coaction square remains deferred.
`ComplexClosure/IntegralLifting.lean` and `FiniteFiber.lean` (`e2a0e4d`)
add closed-point/minimal-polynomial lifting, actual fiber finiteness and
uniform coordinate bounds, using unmodified `minpoly.ker_eval`
(`FieldTheory/Minpoly/IsIntegrallyClosed.lean`),
`exists_ideal_over_maximal_of_isIntegral` (`RingTheory/Ideal/GoingUp.lean`),
`finite_of_finite_type_of_isJacobsonRing` (`RingTheory/Jacobson/Ring.lean`),
`IsAlgClosed.lift` (`FieldTheory/IsAlgClosed/Basic.lean`) and
`AlgHom.liftOfSurjective` (`RingTheory/Ideal/Quotient/Operations.lean`).
Their finite-normalization openness consumer remains unproved.

`Geometry/HomInvariants.lean` is an original composition of the checked
project polynomial lift, Hom-dual regrouping, independent invariants and
rectangular invariant equality. It defines the canonical action by
`PiTensorProduct.map`, and uses existing `Representation.dual`,
`TensorProduct.ext` and `Module.addCommMonoidToAddCommGroup`. The latter
keeps the inherited tensor monoid visible while elaborating the actual
invariant-subspace restriction; no new module representation is introduced.
The result supplies nonzero pairing on independent invariant factors and
its source rectangular lattice restriction. Dual-target rectangular
restriction and the full canonical determinant contraction remain separate.

## Independent dual factors and further checked shared producers

`Tensor/DualRegroup.lean` and `Geometry/DualInvariants.lean` add original
finite-projective naturality and fixed-vector transport through the existing
canonical duality/regrouping equivalence. Their actual consumer extracts a
nonzero pairing with independently invariant dual factors from the actual
Hom polynomial. No external code is copied; the Mathlib module, tensor and
representation APIs above are unchanged.

`InvariantTheory/HomogeneousComponents.lean` (`6524042`/`926a4d5`) imports
Mathlib `RingTheory/MvPolynomial/Homogeneous.lean` at the pinned revision,
using `homogeneousSubmodule_one_pow`, `homogeneousComponent_of_mem`, finite
homogeneous decomposition and its uniqueness to build intrinsic homogeneous
components and extract a positive-degree invariant. Its consumer is the
pending complex orbit criterion; compact averaging and density are separate.

`InvariantTheory/ComplexClosure/Normalization.lean` (`06c1747`) uses
unmodified Mathlib multivariate polynomial UFD and integral-closure instances
from `RingTheory/Polynomial/UniqueFactorization.lean` and
`RingTheory/Polynomial/RationalRoot.lean`, `IsCompact.tendsto_subseq` and
`IsSeqClosed.isClosed` (`Topology/Sequences.lean`), and `isCompact_univ_pi`
(`Topology/Compactness/Compact.lean`). Its proved openness conclusion assumes
an actual integral injective polynomial coordinate map; construction of that
map and density are subsequent obligations. These imports retain the same
repository/revision/Apache-2.0 license stated above; no source is copied.

## Canonical nonvanishing and closure/averaging integration

`Geometry/DualSpecialLinear.lean` and `Nonvanishing.lean` are original
compositions using Mathlib's `SpecialLinearGroup.dualMap`,
`SpecialLinearGroup.congr_linearEquiv` and `Module.evalEquiv` unchanged.
They feed actual transpose surjectivity into the checked rectangular
invariant theorem and then into the existing projective determinant pairing.
The nonzero invariant polynomial is the mathematical input, not a new
certificate or a replacement for geometric semistability.

BALANCED deliveries `CompactAverage` (`3e7976e`) and `UnitaryDensity`
(`96d2f1b`) reuse pinned Apache-2.0 Mathlib probability Haar measure,
Bochner integral translation and continuous-linear-map commutation,
`Matrix.toEuclideanCLM`, `Matrix.IsHermitian.spectral_theorem`,
`MvPolynomial.funext_set`, `Circle.exp_injOn_Icc`, and
`Matrix.det_mvPolynomialX_ne_zero`. No source copied. Their sources are
the registered Maithani Theorem 5.6, U–GL density proposition and
product-of-infinite-sets lemma; actual consumers and remaining special-unitary
averaging obligations are recorded in `verification/BALANCED.md`.

CLOSURE final delivery `53f1119` imports `ComplexClosure.Comparison`,
consuming the actual normalization, constructibility and principal-open
density producers to prove `closure_polynomial_image_zeroLocus`.
Additional unchanged Mathlib imports at the same pinned revision/license:
`RingTheory/NoetherNormalization.lean` (`exists_integral_inj_algHom_of_fg`),
`Algebra/MvPolynomial/Funext.lean` (`funext_set`),
`RingTheory/Ideal/GoingUp.lean` (`Ideal.under_ne_bot`),
`Topology/Separation/Basic.lean` (`infinite_of_mem_nhds`),
`RingTheory/Spectrum/Prime/Chevalley.lean`
(`PrimeSpectrum.isConstructible_range_comap`, including its
`ChevalleyComplexity` dependency),
`RingTheory/Spectrum/Prime/ConstructibleSet.lean`
(`exists_constructibleSetData_iff`),
`RingTheory/Ideal/MinimalPrime/Noetherian.lean`
(`finite_minimalPrimes_of_isNoetherianRing`),
`RingTheory/Ideal/MinimalPrime/Basic.lean` (`exists_minimalPrimes_le`),
`RingTheory/FinitePresentation.lean` (`of_finiteType`), and
`Topology/Homeomorph/Defs.lean` (`Homeomorph.preimage_closure`).
No source copied or dependencies changed. The intended actual consumer is
BALANCED's checked special-linear polynomial Plücker orbit image (`84a679f`).
Exact authorship, source review and 40-probe evidence are preserved in
`verification/COMPLEX_CLOSURE.md`.


Shared integration also consumes ARITH's `IndependentPiSemistable` and
`RestrictionOfScalars` (`a1aa8cb`, `387d06a`; earlier restriction checkpoint
`11fd898`). The finite-family isometric irreducible-action consumer reuses
canonical Mathlib density and the attributed projective tensor duality;
restriction to integers uses `LinearAlgebra/Dimension/Localization.lean`,
`LinearAlgebra/FreeModule/PID.lean` and `Algebra/Module/Rat.lean` at the pinned
Mathlib revision/license. No code copied. Exact provenance and the 338-probe
owner audit are in ARITHMETIC.md. Degree finiteness is now integrated
through the separate DegreeFiniteness consumer below.
BALANCED's `PluckerSemistability` (`7f56300`) consumes the proved polynomial
orbit closure comparison and balanced norm bound, while
`SpecialUnitaryDensity` (`6da0e3e`) consumes unitary polynomial density and
the actual determinant-normalization coordinate retraction. These are
original compositions, with no further copied external code. The delivered
181-probe audit and positive-dimensional scope are recorded in BALANCED.md;
actual invariant-polynomial existence was subsequently proved and integrated
at cf39176, as recorded below.


`Geometry/NonvanishingBaseChange.lean` and `PluckerNonvanishing.lean` are
original compositions of the previously attributed projective tensor/exterior
scalar-extension equivalences, the checked Plucker polynomial pullback and
the actual canonical pairing. The positive sequence reuses the unchanged
accepted `Specht.rectangleTableau` and standard natural-number divisibility;
no external code, core representation or mathematical axiom is added.
`InvariantTheory/PolynomialAverage.lean` (`6db192a`) imports unchanged
Mathlib `RingTheory/Finiteness/Lattice.lean` and
`Algebra/MvPolynomial/Funext.lean` at the pinned revision/license, and
substantively consumes the already attributed compact Haar integration
producer. Its intrinsic bounded-degree continuity and integral polynomial
consumer are detailed in BALANCED.md. No source is copied.


## Exact balanced criterion and arithmetic finiteness integration

BALANCED's `SpecialUnitaryAction`, `PluckerAverage`, `OrbitCriterion` and
intrinsic `IsBalanced.plucker_semistable` (`a63eae3`, `2c9b7b8`, `d91a68c`)
consume the checked compact averaging, SU density and polynomial-orbit closure
comparison. Unmodified additional Mathlib imports are
`Topology/Algebra/Star/Unitary.lean`, `Topology/Algebra/Group/Matrix.lean` and
`Topology/Algebra/MvPolynomial.lean`, at the same pinned
`56a005855ea17e0b0958f73ec801ae140b0a1679` revision and Apache-2.0 license.
No source is copied. The actual consumer constructs a positive-degree
homogeneous invariant nonzero on every nonzero vector of the intrinsic
Plucker line of a nonzero balanced subspace. Exact source and independent
review evidence, including the 195-probe audit, are in BALANCED.md.

ARITH's `DegreeFiniteness` (`05360d4`, precursors `92e69d7`, `b3c1ac2`,
`ba9bf02`, `87fd7bc`) consumes actual short determinant sections, the fixed
ambient exterior lattice and Plucker recovery. It imports unchanged Mathlib
`NumberTheory/NumberField/CanonicalEmbedding/ConvexBody.lean` and the
fractional-ideal Minkowski and fundamental-domain-volume APIs, plus
`LinearAlgebra/ExteriorPower/Basis.lean` and
`LinearAlgebra/LinearIndependent/Lemmas.lean`, at that same revision/license.
It reuses the established project `Balanced.ExteriorMetric` without copying
or changing it. Its finite-degree-superlevel-set conclusion covers saturated
nonfree projective modules over arbitrary number fields; its 366-probe audit
and independent honesty/ground acceptance are in ARITHMETIC.md.


`Arithmetic/RestrictionCovolume/{TraceSpace,Conjugation,Covolume}.lean`
is authored by BOST-COVOLUME/run0008 (explicit evidence commits `cafb32d`,
`9b40453`; earlier source was captured by lifecycle snapshots `21ba17f`,
`b75a4e2`). It reuses the existing pinned Mathlib lattice/basis APIs and
`NumberTheory/NumberField/Discriminant/Basic.lean`, and the already attributed
`Lattice.Covolume` TauCeti extraction, with no new copied source. The actual
trace space and integer lattice, weighted-place norm, Euclidean Haar Gram
formula and rank-zero degree/discriminant endpoint are kernel-checked and
independently accepted. The 24-probe audit at 01:55:18 UTC is foundational-only;
positive-rank discriminant identification is not part of this handoff.


`Tensor/TwoFactors.lean` and the accepted transport prefix of
`Geometry/BinaryPlucker.lean` are original compositions of the unchanged
Mathlib `PiTensorProduct.tmulEquivDep`, `subsingletonEquiv` and
`TensorProduct.congr/map` APIs (`LinearAlgebra/PiTensorProduct/Basic.lean`,
`LinearAlgebra/TensorProduct/Map.lean`, same pinned revision/license).
Their actual consumer transports the project Plucker invariant through the
canonical two-factor equivalence. No external source is copied, no core
representation is duplicated, and no additional axiom is used. The terminal
original-ring binary sequence application remains an unverified preserved
attempt, separate from these checked declarations.
