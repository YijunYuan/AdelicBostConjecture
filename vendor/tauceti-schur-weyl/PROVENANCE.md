# Selective Schur–Weyl proof extraction

Repository: https://github.com/TauCetiProject/TauCeti

Revision: `b3b0334ab9203d9faee4b2f34cd75161463ecdd0`.
License: Apache-2.0. Copyright and authors: The Tau Ceti contributors (2026).
`original/` retains immutable upstream files; `MANIFEST.json` records SHA256
and git blob hashes. The copied source is not an installed dependency.

Authorized by I-0070 after mathematical route review. Target Lean/mathlib pins
are unchanged. The upstream uses Lean 4.36.0-rc2; its build is unestablished.

Selected code lives under `BostConjecture/RepresentationTheory/SchurWeyl/`.
Only the permutation action, inclusion-exclusion polarization, pure-power
spanning, comparison-map commutant, semisimple image double centralizer and
invertible diagonal span are selected. Coordinate-specific wrappers, bundled
GL actions, FDRep, highest weights, classification, and TauCeti tensor-Hom
infrastructure are excluded. The existing project `piTensorHomEquiv` from
Mathlib PR #44845 is reused. Generic source namespaces are preserved where
canonical APIs are absent locally; private helper names use the project namespace.

Consumers: the actual determinant-covariant rectangular tensor and its bilinear
coefficient covector in Geometry, then rectangular invariant identification.
Canonical contraction nonvanishing remains a later consumer. See the local
kernel evidence below and in GEOMETRY.md; upstream-wide validity is not claimed.

## Selected declarations and adaptations

All original paths below are relative to `TauCeti/` at the exact revision above.
All local paths are relative to `BostConjecture/RepresentationTheory/SchurWeyl/`.
Names retain their original namespaces except the endpoint generalization noted
below. Private helper namespaces `TauCeti` became `BostConjecture.SchurWeyl`.

| Original path / declarations | Local file | Adaptation |
| --- | --- | --- |
| `RepresentationTheory/Symmetric/TensorAction/Basic.lean`: `PiTensorProduct.reindexRepresentation`, `_apply`, `commute_reindexRepresentation_map`; `RepresentationTheory/AsAlgebraHom.lean`: `MonoidAlgebra.toSubmodule_range_lift`, `Representation.toSubmodule_range_asAlgebraHom`, `commute_asAlgebraHom_of_forall_commute`, `mem_centralizer_range_asAlgebraHom_iff` | `Action.lean` | Omit coordinate wrappers and unused algebra-adjoin API. Use pinned `Module.End.mul_apply`. |
| `Data/Finset/Basic.lean`: `Finset.sum_powerset_neg_one_pow_card_of_ring`; `LinearAlgebra/Multilinear/Polarization.lean`: `MultilinearMap.sum_neg_one_pow_card_smul_apply_sum_compl`, `PiTensorProduct.sum_neg_one_pow_card_smul_tprod_sum_compl` and their private finite-set helpers | `Polarization.lean` | Add the precise pinned Mathlib choose-sum import; rename private namespace. |
| `RepresentationTheory/Symmetric/TensorAction/Invariants.lean`: `PiTensorProduct.tprod_const_mem_invariants`, `sum_reindexRepresentation_mem_span`, `range_sum_reindexRepresentation`, `invariants_reindexRepresentation` | `Invariants.lean` | Omit SymmetricPower and coordinate results. Replace the last proof's norm-map dependency with direct averaging and inversion of the factorial. The preserved `RepresentationTheory/Invariants.lean` was reviewed but no code from it is imported or extracted. |
| `RepresentationTheory/Symmetric/TensorAction/Centralizer.lean`: `PiTensorProduct.piTensorHomEquiv_reindexRepresentation_tprod_mul`, `piTensorHomEquiv_reindexRepresentation_mul`, `mem_span_range_map_const_iff_forall_commute` and private inverse-cancellation helper | `Centralizer.lean` | Reuse the project's previously checked finite-projective `piTensorHomEquiv` (Mathlib PR44845); replace upstream pure-tensor simplifications by `piTensorHomEquiv_apply` and `piTensorHomMap_tprod_eq_map`. No second tensor-Hom representation. |
| `LinearAlgebra/End/Centralizer.lean`: `Subalgebra.restrictScalars_mem_centralizer`; `RingTheory/Semisimple/DoubleCentralizer.lean`: `Subalgebra.centralizer_centralizer_of_isSemisimpleModule`, `AlgHom.centralizer_centralizer_range` | `DoubleCentralizer.lean` | Keep only the endomorphism-subalgebra/image argument. Use pinned Mathlib's `Module.Finite.toModuleEnd_moduleEnd_surjective` and `Module.End.mul_apply`. |
| `LinearAlgebra/Matrix/GeneralLinearGroup/Multilinear.lean`: `MultilinearMap.exists_mvPolynomial_eval_eq_apply_const`, `apply_const_eq_zero_of_eq_zero_on_gl`; `LinearAlgebra/PiTensorProduct/GeneralLinear.lean`: `PiTensorProduct.map_const_mem_span_range_map_const_units`, `span_range_map_const_units_eq_span_range_map_const` | `GeneralLinear.lean` | Combine the two short source modules; keep canonical matrix polynomial density and dual-annihilator argument. |
| `RepresentationTheory/Symmetric/TensorAction/SchurWeyl.lean`: `TauCeti.coe_centralizer_range_permTensorActionAlgHom_eq_span_range_map_const`, `TauCeti.centralizer_span_range_map_const_eq_range_permTensorActionAlgHom`, `TauCeti.mem_range_permTensorActionAlgHom_iff_forall_commute` | `SchurWeyl.lean` | Generalize the coordinate-space endpoint to arbitrary finite-dimensional modules and arbitrary finite index types. New names: `PiTensorProduct.coe_centralizer_reindex_eq_diagonal_span`, `centralizer_diagonal_span_eq_reindex_range`, `mem_permutation_span_iff_commute_diagonal`, `mem_permutation_span_of_commute_units`. Derive the last criterion using the selected invertible-density theorem. |

The actual downstream consumer is
`Geometry.mem_range_freeLatticeMap_of_determinant_covariant` in
`Geometry/RectangularSpan.lean`. It constructs the rank-one operator from
`Geometry.rectangularCovector`, proves commutation from determinant covariance,
uses `PiTensorProduct.mem_permutation_span_of_commute_units`, and evaluates at
`Geometry.rectangularTensor`. `Geometry.permutation_span_apply_rectangularTensor`
uses the existing integral orbit action and `freeLatticeMap_reindex`; the
normalization is the SPECHT-owned `sum_polytabloidInt_sq` theorem.

No external assumption or full TauCeti dependency is installed. The cone uses
unchanged Mathlib Maschke, semisimple-module density and matrix-polynomial
identity theorems. Exact kernel/axiom results and source reviews are recorded
in `verification/GEOMETRY.md`; the SPECHT lane owns the corresponding
`CONTRIBUTIONS.md` entry.

The additional concrete consumer `Geometry.mem_range_freeLatticeMap_iff_specialLinear_fixed`
in `Geometry/RectangularInvariants.lean` derives determinant covariance from
actual SL invariance by extracting a determinant root over an algebraically
closed field. It does not assume any invariant-space identification.
