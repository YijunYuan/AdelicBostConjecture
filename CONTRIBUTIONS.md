# Reused formalizations

This project targets Theorem 1.1 of `bost.pdf` over proper adelic curves with
countable characteristic-zero fields. Existing number-field proofs from
`old.pdf` are reused where applicable. This file records external source reuse;
it does not attribute the upstream proofs to the project author.

Mathlib, HarderNarasimhan and ArakelovGeometry are pinned Lake dependencies.
New selectively copied source belongs under `BostConjecture/ExternalResults/`;
existing copied or adapted source is under `BostConjecture/ExternalCode/`, grouped by
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
claimed by checking the selected dependency cone. The retained source is further
restricted to dependencies of the four principal theorems; historical manifests
may therefore describe declarations or modules that have since been removed.

## ArakelovGeometry: adelic foundations and instability filtrations

- Repository: <https://github.com/YijunYuan/ArakelovGeometry> (private).
- Revision: `0a608c4f219c4de669be8b6b1a1bc47f996d8d72`.
- License: Apache-2.0; retained in the pinned Lake dependency.
- Integration: unchanged dependency, fetched by SSH; Lean/mathlib 4.35.0 and
  HarderNarasimhan `14b3090e1e169b77fe381102a1289f24c2b08a11` match this project.
- Intended consumers: the adelic implementation of this paper's Sections 6–7,
  using actual completed norms, degrees, HN filtrations, Plucker invariants and
  `slope_sum_le_tensor_quotient_of_not_geometricallySemistable`.
- Boundary: the last result retains the smaller-rank tensor-HN induction
  hypothesis; this project must discharge it by simultaneous rank induction.
  Its existence does not prove the geometric semistable branch or Theorem 1.1.
- Verification: source interfaces and pins inspected during setup. Local
  consumer builds and transitive axiom checks are pending and will be recorded
  with the implemented consumers. Prefer this dependency's external exports
  over duplicate local ports once their exact statements have been compared.

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
  orthogonalization and content eigenvalues. The arithmetic, invariant-theory,
  compactness and asymptotic modules also directly import Mathlib's existing
  number-field, projective-module, polynomial, Haar-measure and analysis APIs;
  their import lists identify the precise modules used.
- Typeclass refactoring also reuses the Dedekind-domain instance in
  `Mathlib/RingTheory/Flat/TorsionFree.lean`: torsion-free modules are flat.
  The arithmetic fiber and tensor proofs infer flatness through this instance
  instead of installing repeated `IsLocalization.flat` proofs locally.
  Specht lattice embeddings and permutation actions use `LinearMap.restrict`
  from `Mathlib/Algebra/Module/Submodule/LinearMap.lean` for their restricted maps.
- `Slope/DedekindCut.lean` uses `DedekindCut.principal`,
  `principal_le_iff`, `left_subset_left_iff`, `ext'`, `right_principal` and
  `upperBounds_left` from `Mathlib/Order/Completion.lean`, together with
  `csSup_le_iff` from `Mathlib/Order/ConditionallyCompleteLattice/Basic.lean`.
  Its local real-value conversion and bounds lemma feed
  `Arithmetic/HN/MaxSlope.lean`; the pinned upstream sources are unmodified.

## Harder–Narasimhan games

- Repository: <https://github.com/YijunYuan/HarderNarasimhan>.
- Revision: `14b3090e1e169b77fe381102a1289f24c2b08a11`.
- Author: Yijun Yuan; license: Apache-2.0.
- Integration: unmodified pinned Lake dependency, Lean/mathlib `v4.35.0`.
- Original modules: `HarderNarasimhan.Filtration.Unique`,
  `HarderNarasimhan.Filtration.Exists`,
  `HarderNarasimhan.PayoffFunction.Defs`,
  `HarderNarasimhan.PayoffFunction.Slope`, and
  `HarderNarasimhan.PayoffFunction.NashEquilibrium`.
- Results: HN existence and uniqueness, additive-interval slopes, and the
  comparison of game semistability with ordinary slope semistability.
- Maximal-slope consumers: `Slope/FiniteLength.lean` combines
  `PayoffFunction.B_top_eq_max_top` and `IsSlopeLike.min_eq_A` from
  `HarderNarasimhan.PayoffFunction.GameValue` with breakpoint semistability to
  prove that a breakpoint attains `PayoffFunction.max ⊤`.
  `Arithmetic/HN/Filtration.lean` applies
  `PayoffFunction.hnFiltration_succ_isGreatest_breakpoints` from
  `HarderNarasimhan.Filtration.Exists` to identify the slope supremum with the
  first HN slope. The definition and finiteness of `maxSlope` are independent
  of this identification: `Arithmetic/HN/MaxSlope.lean` uses `PayoffFunction.max`
  and its upper/lower bounds from `PayoffFunction.Defs`, together with the
  project's arithmetic degree-finiteness results. These are local bridge
  proofs; upstream code is unchanged.
- Consumers: arithmetic HN filtrations and the finite-length slope adapters.
  The project separately proves the Hermitian degree, quotient and duality
  bridges; order duality alone is not Hermitian duality.
- Mathematical source: Chen–Jeannin, *Harder–Narasimhan games*,
  <https://arxiv.org/abs/2306.08283>, §§2.2, 3.3, 4.3–4.4.

## OpenAI: complex Specht modules and Euclidean Mahler compactness

- Repository: <https://github.com/openai/math>.
- Revision: `4eaee87548250b2682affda7d05d947c05554bae`; upstream Lean 4.34.1.
- License: Apache-2.0; [license](BostConjecture/ExternalCode/OAI/LICENSE) and
  [source manifest](BostConjecture/ExternalCode/OAI/PROVENANCE.json).
- Original source root: `lean/OAI/`; local source root:
  `BostConjecture/ExternalCode/OAI/`.
- Specht source: `RepresentationTheory/Saxl/{Model,Basic,Polytabloid,SpechtSubmodule}.lean`.
  The exports include `OAI.Saxl.specht_irreducible`,
  `OAI.Saxl.specht_cyclic_of_ne_zero` and `OAI.Saxl.columnAlt_tabloid`.
- Mahler source: `NumberTheory/ArithmeticGroups/Lattices/` modules
  `ShortestVector`, `ProjectedLattice`, `BasisLift`, `BoundedBasis`,
  `OrthogonalStretch`, `Minkowski/Ellipsoid`, `UniformShortSpan`, `FrameMatrices`.
  The principal result is
  `OAI.NumberTheory.ArithmeticGroups.Lattices.FrameMatrices.Construction.exists_compact_lattice_frames`.
- Adaptations: Lean 4.35 module visibility, removal of unused staircase,
  Kronecker multiplicity and Saxl-conjecture declarations, relocated imports,
  source documentation and mathlib-style formatting. Umbrella Mathlib imports
  are replaced by the specific modules used. Classical inference is
  localized to proofs; unnecessary decidability/finiteness arguments are
  removed from `finset_eq_of_signed_sum` and `continuous_basis_matrix`.
- Consumers: the actual integral Specht orbit lattice, standard polytabloids,
  central content action, and arithmetic compactness via real trace frames.
  Project-specific scalar-extension, degree and restriction-of-scalars bridges
  are proved separately in the local modules.

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
  and collect multiplicities over the rationals. The consumer
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
- Original files: `TauCeti/LinearAlgebra/SymmetricPower/{Basic,Lift,Algebra}.lean`;
  local root: `BostConjecture/ExternalCode/TauCeti/LinearAlgebra/SymmetricPower/`.
- Selected declarations: quotient extensionality and maps, `SymmetricPower.lift`,
  `consMul`, the natural tensor section and factorial composite, homogeneous
  multiplication and the symmetric-algebra comparison.
- Adaptations: Lean 4.35 imports and elaboration; unused basis, monomial and
  WordFiltration APIs omitted. The homogeneous component remains the existing
  power of the generator range. The algebra port restores the original
  `TauCeti.SymmetricPower` namespace.
- Consumers: geometric polynomial polarization, Plucker polarization and
  degree divisibility for invariant polynomials.

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
| [#45002](https://github.com/leanprover-community/mathlib4/pull/45002) | `TJHeeringa/mathlib4` at `41260205df493c627e1ac0e54812cfdeb6517fbc` | Tjeerd Jan Heeringa's `Mathlib/Analysis/InnerProductSpace/{Abs,Polar}.lean`; `ContinuousLinearMap.abs`, `polarₚₗᵢ`, `polar` and the polar decomposition identities | `ExternalCode/MathlibPRs/PR45002/`; balanced special-linear polar decomposition and orbit-norm bounds |

Local roots in the table are relative to `BostConjecture/`. Each contains
`LICENSE` and `PROVENANCE.json`. PR #40948 extracts a small projection
prerequisite. PR #44845 expands two unavailable reindex simplifications.
PR #45002 adjusts local imports and documentation references. All ports also
have relocated module imports and mathlib-style source documentation.
