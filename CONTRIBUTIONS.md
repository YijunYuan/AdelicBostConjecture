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
  prefix bijection and exact binomial weight. Labelled normalization and
  concentration remain obligations for the rectangular prefix law (§5).

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
  unchanged. Intended consumer: polar factorization in the balanced
  Plucker argument. This API is for complex Hilbert spaces; the unitary,
  logarithm and determinant adapters remain open.
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

## Verification

Run `horizon --root ../.. check --json` from this project, then
`horizon --root ../.. check --lean verification/ReuseAxioms.lean --json`.
The latter audits the transitive axioms of the named reused producers.
Source inspections and successful prerequisite builds do not certify the
unwritten arithmetic bridges or main theorem. Current evidence is recorded in
`verification/RESULTS.md` once the corresponding checks finish.
