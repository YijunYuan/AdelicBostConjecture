# Reused formalizations

This project targets Theorem 1.1 of `bost.pdf` over proper adelic curves with
countable characteristic-zero fields. The source tree retains the main theorem
module and its dependencies, including shared algebraic proofs from the earlier
development. This file records external source reuse;
it does not attribute the upstream proofs to the project author.

Mathlib, HarderNarasimhan and ArakelovGeometry are pinned remote Lake dependencies.
Existing copied or adapted source is under `BostConjecture/ExternalCode/`, grouped by
origin and compiled as part of the single `BostConjecture` library. Module
paths describe file organization; public declaration namespaces retain their
upstream names. The substantially adapted Garnir proofs keep the existing
`BostConjecture.Specht` namespace because they use this project's integral
word model. The symmetric-algebra port uses its original
`TauCeti.SymmetricPower` namespace.

Every external Lean module has a source section identifying its repository,
exact revision and original files. Copyright, author and license notices are
preserved. Historical extraction manifests retain the original source hashes,
modification records and checks; their relocation sections identify current
paths. Original sources are retrievable from the pinned repositories and revisions;
redundant upstream source snapshots are omitted. No complete upstream build is
claimed by checking the selected dependency cone. The retained source supports
the public adelic theorems; historical manifests
may therefore describe declarations or modules that have since been removed.

## ArakelovGeometry: adelic foundations and instability filtrations

- Repository: <https://github.com/YijunYuan/ArakelovGeometry> (private).
- Pinned revision: `c9dfe39888d87cdde965b647116127744cf3623e`.
- License: Apache-2.0; source notices are preserved.
- Integration: unmodified remote git dependency at that revision. Lean/mathlib 4.35.0 and
  HarderNarasimhan `14b3090e1e169b77fe381102a1289f24c2b08a11` match this project.
  The migration from `0a608c4` follows upstream commits `c093b26` (integral ring
  maps, prime spectra and the `ExternalCode` reorganization) and `c9dfe39`
  (property instances). Base measurability,
  Archimedean normalization and common countable density now use instances;
  tensor, degree and HN consumers use the revised signatures. Completed inner
  products are selected by `NormFamily.fiberInnerProductSpace`. The local
  Specht norms and determinant powers expose their canonical property instances.
  Local `Adelic/Induction/HNContraction` adapts the proofs in
  `HarderNarasimhan/Hermitian/{Functoriality,LargestSubspace}` to independent
  carrier universes and supplies the reverse minimal-slope threshold consequence.
  Source copyright and license notices are retained. No dependency sources are edited.
- Consumers: `Adelic/Geometry/{Polynomial,Plucker,ScalarExtension,Nonvanishing,Quotient}`
  reuse `InvariantTheory/{Semistability,Plucker,Linearization}` and
  `InvariantTheory/Binary/TensorTransport`, retaining the original-field
  pairing and quotient dual inclusion. `tensorBaseChangeEquiv`,
  `dualBaseChangeEquiv`, and `dualBaseChangeEquiv_dualMap` provide the actual
  tensor/dual transport. `Adelic/Semistability/Group` consumes
  `map_destabilizingSubspace_eq_of_completed_isometry` from
  `HarderNarasimhan/Galois/HNScalarExtension`.
- `Adelic/Induction/{GradeEquality,TensorHN,RankInduction,MaxSlope}` reuse
  actual completed norms, degree identities, HN uniqueness, HN functoriality,
  and the component maps in `Tensor/Graded/{Basic,Degree}`. The Bost-specific
  modules `Examples/Trivial/Filtration/HN/OptimalVariation`, `Tensor/Graded/Degree`
  and `Tensor/Graded/HNVariation` at the pinned revision are adapted in local
  `Adelic/Induction/{OptimalVariation,GradedVariation,HNVariation}`. Copyright,
  author and license notices are retained. The local versions use namespace
  `BostConjecture.Adelic`, so they coexist with the unchanged upstream versions.
  The upper bound now uses target HN
  functoriality directly; its generic bundle and spanning constructions remain
  in AG. The local unstable-case theorem is
  `BostConjecture.Adelic.slope_sum_le_tensor_quotient_of_not_geometricallySemistable`.
- `Adelic/Induction/{FiniteNorms,FiniteSlopes,FiniteMaxSlope}` reuse the
  completed tensor grouping and coherence exports in
  `Tensor/Hermitian/{Dual/Basic,Grouping,Coherence}`, tensor construction on
  countable bases, and `Slope/{Basic,Tensor}`. The unconditional finite
  mean-slope formula feeds the determinant-Specht product degree calculation;
  `Induction/Bost` instantiates the finite maximal-slope assembly with the proved
  binary theorem. No upstream source is copied in these modules.
- `Adelic/Contraction/PairingBaseChange` generalizes the completed-map arguments
  of `AdelicVectorBundle/Tensor/PairMap.lean` to independent carrier universes,
  using its imported seminorm-map producers. In `PairingNorm`, the private
  `multilinear_bound_of_generator_bounds` adapts the proof of
  `AdelicVectorBundle/ScalarExtension/Degree.lean`'s private
  `seminorm_multilinearMap_le_of_linear_bound` to dependent generator sets and
  weights. This bound feeds finite-place regrouping, `dualRegroupEquiv_norm_le`,
  and finally the actual `canonicalPairing_norm_le`. These are local adaptations
  of proof arguments; their original upstream producers are unchanged.
- `Adelic/Slope/{GeometricSubspace,GeometricQuotient}` consume the actual
  pairing contraction, the Specht covolume limit, and unchanged exports from
  `Construction/Tensor/Countable`, `Slope/{Quotient,DualUpper}`, norm-family
  pushforward composition, and duality. The resulting geometric quotient bound
  is unconditional and uses the actual induced and quotient norms.
- Boundary: the local instability-variation result retains a smaller-rank
  tensor-HN hypothesis. This project discharges it by simultaneous rank induction
  and separately proves the geometric semistable branch. `Induction/Bost`
  combines these producers into Theorem 1.1; no main theorem is assumed upstream.
- Verification: the geometry, group and induction consumers above passed
  serialized Horizon kernel checks on 11 November 2026. Their recorded
  transitive axiom audits use only `propext`, `Classical.choice`, and `Quot.sound`;
  the public main declarations discharge the conditional induction helpers'
  geometric quotient bound with `Slope/GeometricQuotient`.
  These checks certify the imported dependency cone, not the whole upstream
  library. Prefer this dependency's exports over duplicate local ports after
  comparing exact statements. The current alignment and migration checks are
  recorded in [the alignment notes](docs/paper-code-alignment.md). The additional TauCeti
  symmetric-power adaptation is recorded below.

## Mathlib

- Repository: <https://github.com/leanprover-community/mathlib4>.
- Revision: `56a005855ea17e0b0958f73ec801ae140b0a1679` (`v4.35.0`).
- License: Apache-2.0; the dependency retains its notices unchanged.
- Integration: direct imports from the pinned Lake dependency, without source
  modifications. The separate unmerged PR ports are listed below.
- Important original APIs include
  `Analysis/InnerProductSpace/TensorProduct.lean` (`TensorProduct.inner_tmul`),
  `Analysis/InnerProductSpace/GramSchmidtOrtho.lean` (`gramSchmidtBasis`,
  `gramSchmidt_def''`, `span_gramSchmidt_Iio`, `gramSchmidt_inv_triangular`),
  `LinearAlgebra/TensorProduct/Associator.lean`
  (`TensorProduct.tensorTensorTensorComm`), and
  `LinearAlgebra/PiTensorProduct/Generators.lean`
  (`PiTensorProduct.submodule_span_eq_top`).
- Consumers: the intrinsic tensor Hilbert metric, tensor regrouping, Specht
  orthogonalization and content eigenvalues. The invariant-theory and asymptotic
  modules also directly import Mathlib's existing projective-module, polynomial,
  measure and analysis APIs;
  their import lists identify the precise modules used.
- The Specht lattice and invariant-tensor proofs reuse the Dedekind-domain instance in
  `Mathlib/RingTheory/Flat/TorsionFree.lean`: torsion-free modules are flat.
  Specht lattice embeddings and permutation actions use `LinearMap.restrict`
  from `Mathlib/Algebra/Module/Submodule/LinearMap.lean` for their restricted maps.
## Harder–Narasimhan games

- Repository: <https://github.com/YijunYuan/HarderNarasimhan>.
- Revision: `14b3090e1e169b77fe381102a1289f24c2b08a11`.
- Author: Yijun Yuan; license: Apache-2.0.
- Integration: unmodified pinned Lake dependency, Lean/mathlib `v4.35.0`.
- Consumers: ArakelovGeometry's HN existence, uniqueness and slope interfaces.
  The adelic main proof uses those interfaces for actual Hermitian bundles.
  The former local number-field HN and finite-length slope adapters have been
  removed with the independent number-field proof branch.
- Mathematical source: Chen–Jeannin, *Harder–Narasimhan games*,
  <https://arxiv.org/abs/2306.08283>, §§2.2, 3.3, 4.3–4.4.

## OpenAI: complex Specht modules

- Repository: <https://github.com/openai/math>.
- Revision: `4eaee87548250b2682affda7d05d947c05554bae`; upstream Lean 4.34.1.
- License: Apache-2.0; [license](BostConjecture/ExternalCode/OAI/LICENSE) and
  [source manifest](BostConjecture/ExternalCode/OAI/PROVENANCE.json).
- Original source root: `lean/OAI/`; local source root:
  `BostConjecture/ExternalCode/OAI/`.
- Specht source: `RepresentationTheory/Saxl/{Model,Basic,Polytabloid,SpechtSubmodule}.lean`.
  The exports include `OAI.Saxl.specht_irreducible`,
  `OAI.Saxl.specht_cyclic_of_ne_zero` and `OAI.Saxl.columnAlt_tabloid`.
- Adaptations: Lean 4.35 module visibility, removal of unused staircase,
  Kronecker multiplicity and Saxl-conjecture declarations, relocated imports,
  source documentation and mathlib-style formatting. Umbrella Mathlib imports
  are replaced by the specific modules used. Classical inference is
  localized to proofs; unnecessary decidability/finiteness arguments are
  removed from `finset_eq_of_signed_sum`.
- Consumers: the actual integral Specht orbit lattice, standard polytabloids,
  and central content action. Project-specific scalar-extension and adelic
  degree bridges are proved separately in the local modules. The former Mahler
  compactness port has no remaining consumer and has been removed; its
  extraction history remains identified in the source manifest.

## Etingof representation theory: hook-length formula

- Repository: <https://github.com/mathlib-initiative/Etingof-RepresentationTheory-draft1>.
- Revision: `c6d86a8bd52065aafb8251fa1cdcd55b609743ef`; upstream Lean 4.32.2.
- License: Apache-2.0; [license](BostConjecture/ExternalCode/Etingof/LICENSE),
  [notice](BostConjecture/ExternalCode/Etingof/NOTICE), and
  [source manifest](BostConjecture/ExternalCode/Etingof/PROVENANCE.json).
- Original source root: `clean-code/release/RepresentationTheory/`; local root:
  `BostConjecture/ExternalCode/Etingof/RepresentationTheory/`.
- Selected four-module closure:
  `YoungDiagram/PartitionConstructions`, `Partition/YoungDiagram`,
  `SymmetricGroup/PartitionAuxiliaryConstructions`, and
  `Combinatorics/YoungDiagram/CornerStatistics`.
- Principal declaration:
  `RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics.Partition.auxiliaryCard_mul_hookLengthProduct_eq_factorial`.
  The counted objects are increasing bijective fillings of partition cells.
- Adaptations: Lean 4.35 visibility and proof elaboration, local import paths,
  source documentation, formatting and explicit simplification dependencies.
  The original `RepresentationTheory` namespaces are retained. The two
  auxiliary-construction files retain only `auxiliaryPartitionNatList`,
  `AuxiliaryPartitionSource`, and `auxiliaryYoungDiagramOfPartition`; unused
  canonical-filling, group-algebra and semistandard-tableau APIs are omitted.
  Umbrella Mathlib imports are replaced by the precise prerequisites.
  Unused source-reference metadata tooling and compatibility aliases are
  omitted; bibliographic references remain in source comments.
- Consumers: `Specht` hook and shifted counts, followed by prefix weights and
  the covolume asymptotic. The hook-count bridge also adapts the upstream
  private `sytCell_iff_mem_toYoungDiagram` and `sytCellEquiv` as
  `partitionCell_mem` and `partitionCellEquiv`; the inverse-tableau proofs
  are project-specific.

## TauCeti: covolumes, straightening and Schur–Weyl duality

- Repository: <https://github.com/TauCetiProject/TauCeti>.
- Revision: `b3b0334ab9203d9faee4b2f34cd75161463ecdd0`; upstream Lean 4.36.0-rc2.
- Authors: The Tau Ceti contributors; license: Apache-2.0.
  [License](BostConjecture/ExternalCode/TauCeti/LICENSE),
  [covolume and straightening provenance](BostConjecture/ExternalCode/TauCeti/PROVENANCE.json),
  [Schur–Weyl provenance](BostConjecture/ExternalCode/TauCeti/Provenance/SchurWeyl/PROVENANCE.md).
- Covolumes: selected declarations from
  `TauCeti/Analysis/InnerProductSpace/Gram/Hadamard.lean` and
  `TauCeti/Algebra/Module/ZLattice/Covolume.lean` live in
  `BostConjecture/ExternalCode/TauCeti/Lattice/Covolume.lean`.
  They include `OrthonormalBasis.det_gram_eq_norm_det_sq`,
  `OrthonormalBasis.volume_fundamentalDomain`,
  `OrthonormalBasis.volume_real_fundamentalDomain`,
  `ZLattice.covolume_sq_eq_det_gram`, `ZLattice.covolume_span_sq_eq_det_gram`,
  and `ZLattice.covolume_le_covolume_of_le`.
  The port specializes to real inner-product spaces and uses Mathlib's
  relative-index formula for lattice inclusion. Specht metric and Gram bounds
  consume these results.
- Straightening: `TauCeti/RepresentationTheory/Symmetric/Specht/{Garnir,Straightening}.lean`
  and selected helpers from `Combinatorics/Young/Diagram.lean`,
  `Algebra/BigOperators/Finset/Swap.lean`, and
  `Algebra/Order/BigOperators/Sum/LtSum.lean` are adapted under
  `BostConjecture/ExternalCode/TauCeti/RepresentationTheory/Specht/`.
  The proofs replace categorical tabloids with the existing OAI tableaux and
  integral word coordinates, prove integer cancellation by an involution,
  and collect multiplicities over the rationals. The standard-tableau result
  is bundled into the local `RowStandard`, `ColumnStandard` and `IsStandard`
  property classes. The consumer
  `BostConjecture.Specht.polytabloidRat_mem_span_standard` supplies rational
  spanning to the standard real basis; it does not assert an integral basis.
- Schur–Weyl: selected sources under `TauCeti/RepresentationTheory/Symmetric/TensorAction/`,
  `RepresentationTheory/AsAlgebraHom.lean`, `Data/Finset/Basic.lean`,
  `LinearAlgebra/Multilinear/Polarization.lean`, `LinearAlgebra/End/Centralizer.lean`,
  `RingTheory/Semisimple/DoubleCentralizer.lean`,
  `LinearAlgebra/Matrix/GeneralLinearGroup/Multilinear.lean`, and
  `LinearAlgebra/PiTensorProduct/GeneralLinear.lean` are adapted under
  `BostConjecture/ExternalCode/TauCeti/RepresentationTheory/SchurWeyl/`.
  The provenance table records every selected declaration and its source.
  The port keeps permutation actions, inclusion-exclusion polarization,
  pure-power spanning, the double centralizer and invertible diagonal span;
  it reuses the projective tensor-Hom API from PR #44845 and generalizes the
  coordinate endpoint to arbitrary finite-dimensional modules.
  `PiTensorProduct.mem_permutation_span_of_commute_units` is consumed by
  rectangular invariant-space identification. Private helpers retain the
  upstream `TauCeti` namespace.

## TauCeti: symmetric-power polarization

- Repository: <https://github.com/TauCetiProject/TauCeti>.
- Revision: `3c3a32baea963db05c302adeb307b22baae4de78`; upstream Lean 4.36.0-rc2.
- Authors: The Tau Ceti contributors; license: Apache-2.0.
  [Detailed provenance and license](BostConjecture/ExternalCode/TauCeti/Provenance/SymmetricPower/PROVENANCE.md).
- Original files: `TauCeti/LinearAlgebra/SymmetricPower/{Basic,Lift,Algebra}.lean`.
  The generic quotient, tensor and lift APIs remain in
  `BostConjecture/ExternalCode/TauCeti/LinearAlgebra/SymmetricPower/{Basic,Lift}.lean`.
  The universe-polymorphic finite-index adaptation is in
  `BostConjecture/ExternalCode/TauCeti/LinearAlgebra/SymmetricPower/Finite.lean`.
- The new file adapts the existing selective port at the same pinned revision,
  retaining the Tau Ceti contributors' copyright and Apache-2.0 license and
  crediting Yijun Yuan for the adaptation. Its public namespace remains
  `TauCeti.SymmetricPower`.
- `FinitePower R M n` abbreviates Mathlib's existing symmetric quotient indexed
  by `ULift (Fin n)`. Canonical reindexing connects it to ordinary finite tensor
  powers. The homogeneous target remains `range(SymmetricAlgebra.ι)^n`.
  The adapted commuting creation operators give the homogeneous equivalence;
  existing quotient lift, symmetrization, factorial composite and naturality
  provide the natural section. No second quotient or homogeneous-polynomial
  representation is introduced.
- Consumer: `Geometry/Polynomial/Polarization.lean` uses
  `finiteEquivHomogeneous`, `finiteMk_comp_toTensorPower`, and
  `finiteToTensorPower_comp_map` to lift invariant polynomials to invariant
  tensors. Normalization by the factorial occurs in characteristic-zero field
  consumers. The existing invariant and canonical-pairing route supplies the
  original-field nonzero-pairing sequences in
  `Adelic/Geometry/{Nonvanishing,Quotient}.lean`.
- The previous local `Algebra.lean` had no remaining consumer after this
  generalization and was removed. Its upstream hash and adaptation history
  remain in the provenance document. The pinned ArakelovGeometry coordinate
  multiplication API does not provide the natural symmetric section required
  by this route.

## Stacks: alternating-tensor determinant covariance

- Repository: <https://github.com/AxiomMath/Stacks>.
- Revision: `012108f61d7f92a6ffc35ec3f263b6da5d438125`; upstream Lean 4.34.0-rc2.
- License: Apache-2.0; [license](BostConjecture/ExternalCode/Stacks/LICENSE) and
  [per-declaration provenance](BostConjecture/ExternalCode/Stacks/PROVENANCE.json).
- Original path: `StacksFrontier/LinearAlgebra/Matrix/AlternatingTensorPower.lean`.
  Local path: `BostConjecture/ExternalCode/Stacks/LinearAlgebra/Matrix/AlternatingTensorPower.lean`.
- Eight selected declarations: `Matrix.altVec`, `sum_mul_altVec`,
  `altVec_coe_perm`, `altVec_eq_zero_of_not_bijective`, `det_submatrix_left`,
  `tensorPow`, `tensorPow_apply`, and `sum_tensorPow_mul_altVec`.
- Adaptations: scoped source documentation and replacement of deprecated
  conditional-lemma names for Lean/mathlib 4.35; the `Matrix` namespace remains.
- Consumers: Specht column tensors and determinant covariance in the actual
  rectangular word representation.

## Selective Mathlib PR ports

Each port retains its exact Apache-2.0 license, author notices, source hashes
and original declaration names. These are local checked producers, not a
replacement Mathlib dependency. All target Lean/mathlib `v4.35.0`.

| PR | Repository and exact revision | Original sources and principal declarations | Local source root and consumers |
| --- | --- | --- | --- |
| [#40948](https://github.com/leanprover-community/mathlib4/pull/40948) | `Thmoas-Guan/mathlib4_fork` at `b642b6723caf97b7b462dd5ddeabb0226c3b5433` | Nailin Guan's `Mathlib/LinearAlgebra/ExteriorPower/BaseChange.lean` and two projections from `ExteriorAlgebra/Grading.lean`; `exteriorPower.baseChangeEquiv` and `ExteriorAlgebra.toExteriorPower` | `ExternalCode/MathlibPRs/PR40948/`; arithmetic determinants and geometric Plucker base change |
| [#44845](https://github.com/leanprover-community/mathlib4/pull/44845) | `DanielJHorton/mathlib4` at `47365e3b9fd4329f058c31ac7aa9565a6036b17d` | Daniel Horton's `Mathlib/LinearAlgebra/PiTensorProduct/Projective.lean` and two declarations from `Dual/Defs.lean`; `PiTensorProduct.Projective`, `piTensorHomEquiv`, `dualDistribEquivOfProjective`, `Module.Dual.dualBaseRingEquiv` | `ExternalCode/MathlibPRs/PR44845/`; integral projective tensor duality, contraction and Schur–Weyl duality |

Local roots in the table are relative to `BostConjecture/`. Each contains
`LICENSE` and `PROVENANCE.json`. PR #40948 extracts a small projection
prerequisite. PR #44845 expands two unavailable reindex simplifications.
Both retained ports have relocated module imports and mathlib-style source
documentation. The unused PR #45002 polar-decomposition port was removed
with the balanced-metric proof branch.
