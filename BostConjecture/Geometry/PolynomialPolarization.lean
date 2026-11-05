module

public import BostConjecture.Geometry.PolynomialTensor
public import BostConjecture.LinearAlgebra.SymmetricPower.Algebra

/-! # Natural symmetric tensor lifts of homogeneous invariant polynomials

The section is the checked symmetric-power homogeneous equivalence followed by
TauCeti's symmetrization and division by the factorial. Its actual quotient,
naturality and evaluation identities connect it to the canonical contraction.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Geometry

open Module PiTensorProduct InvariantTheory
open scoped TensorProduct

variable {F : Type} [Field F] {X Y : Type*}
  [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y]

/-- The symmetric quotient multiplication is the existing polynomial tensor map. -/
theorem toSymmetricAlgebra_mk {d : ℕ} (u : ⨂[F] (_ : Fin d), Dual F X) :
    BostConjecture.SymmetricPower.toSymmetricAlgebra F (Dual F X) d
      (_root_.SymmetricPower.mk F (Fin d) (Dual F X) u) = polynomialTensorMap F X d u := by
  induction u using PiTensorProduct.induction_on with
  | smul_tprod r ℓ =>
    simp only [map_smul, polynomialTensorMap_tprod]
    congr 1
    exact BostConjecture.SymmetricPower.toSymmetricAlgebra_tprod F (Dual F X) d ℓ
  | add u v hu hv => simp only [map_add, hu, hv]

/-- The generic homogeneous comparison specialized to the established intrinsic
polynomial degree space, with its canonical module structure. -/
def symmetricPowerPolynomialEquiv (F : Type) [Field F]
    (X : Type*) [AddCommGroup X] [Module F X] (d : ℕ) :
    Sym[F]^d (Dual F X) ≃ₗ[F] homogeneousPolynomials F X d :=
  BostConjecture.SymmetricPower.equivHomogeneous d

@[simp]
theorem symmetricPowerPolynomialEquiv_coe {d : ℕ} (u : Sym[F]^d (Dual F X)) :
    (symmetricPowerPolynomialEquiv F X d u : SymmetricAlgebra F (Dual F X)) =
      BostConjecture.SymmetricPower.toSymmetricAlgebra F (Dual F X) d u :=
  BostConjecture.SymmetricPower.coe_equivHomogeneous_apply d u

private theorem toSymmetricAlgebra_symm {d : ℕ} (p : homogeneousPolynomials F X d) :
    BostConjecture.SymmetricPower.toSymmetricAlgebra F (Dual F X) d
      ((symmetricPowerPolynomialEquiv F X d).symm p) = p := by
  rw [← symmetricPowerPolynomialEquiv_coe,
    LinearEquiv.apply_symm_apply]

private theorem toSymmetricAlgebra_map_dual {d : ℕ} (f : X →ₗ[F] Y)
    (u : Sym[F]^d (Dual F Y)) :
    BostConjecture.SymmetricPower.toSymmetricAlgebra F (Dual F X) d
      (_root_.SymmetricPower.map f.dualMap u) = polynomialPullback f
        (BostConjecture.SymmetricPower.toSymmetricAlgebra F (Dual F Y) d u) := by
  have h : (BostConjecture.SymmetricPower.toSymmetricAlgebra F (Dual F X) d).comp
        (_root_.SymmetricPower.map f.dualMap) =
      (polynomialPullback f).toLinearMap.comp
        (BostConjecture.SymmetricPower.toSymmetricAlgebra F (Dual F Y) d) := by
    apply _root_.SymmetricPower.ext
    intro ℓ
    simp
    rfl
  exact LinearMap.congr_fun h u

/-- The quotient of symmetrization is multiplication by the degree factorial. -/
theorem polynomialTensorMap_toTensorPower {d : ℕ} (u : Sym[F]^d (Dual F X)) :
    polynomialTensorMap F X d (_root_.SymmetricPower.toTensorPower F (Fin d) (Dual F X) u) =
      (d.factorial : F) • BostConjecture.SymmetricPower.toSymmetricAlgebra F (Dual F X) d u := by
  rw [← toSymmetricAlgebra_mk]
  have h := LinearMap.congr_fun
    (_root_.SymmetricPower.mk_comp_toTensorPower (R := F) (ι := Fin d) (M := Dual F X)) u
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
    Fintype.card_fin] at h
  rw [h, map_nsmul, Nat.cast_smul_eq_nsmul]

variable [CharZero F]

/-- The canonical normalized symmetric lift of an intrinsic homogeneous polynomial. -/
def polynomialSymmetricLift (F : Type) [Field F] [CharZero F]
    (X : Type*) [AddCommGroup X] [Module F X] (d : ℕ) :
    homogeneousPolynomials F X d →ₗ[F] (⨂[F] (_ : Fin d), Dual F X) :=
  ((d.factorial : F)⁻¹ • _root_.SymmetricPower.toTensorPower F (Fin d) (Dual F X)).comp
    (symmetricPowerPolynomialEquiv F X d).symm.toLinearMap

/-- The symmetric lift is a section of the actual homogeneous polynomial quotient. -/
@[simp]
theorem polynomialTensorMap_symmetricLift {d : ℕ} (p : homogeneousPolynomials F X d) :
    polynomialTensorMap F X d (polynomialSymmetricLift F X d p) = p := by
  change polynomialTensorMap F X d ((d.factorial : F)⁻¹ • _) = _
  rw [map_smul, polynomialTensorMap_toTensorPower, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero d)), one_smul]
  exact toSymmetricAlgebra_symm p

/-- The normalized section commutes with every linear pullback. -/
theorem polynomialSymmetricLift_pullback {d : ℕ} (f : X →ₗ[F] Y)
    (p : homogeneousPolynomials F Y d) :
    PiTensorProduct.map (fun _ : Fin d => f.dualMap) (polynomialSymmetricLift F Y d p) =
      polynomialSymmetricLift F X d
        ⟨polynomialPullback f p, polynomialPullback_mem_homogeneous f p.property⟩ := by
  have h : (symmetricPowerPolynomialEquiv F X d).symm
        ⟨polynomialPullback f p, polynomialPullback_mem_homogeneous f p.property⟩ =
      _root_.SymmetricPower.map f.dualMap
        ((symmetricPowerPolynomialEquiv F Y d).symm p) := by
    apply BostConjecture.SymmetricPower.toSymmetricAlgebra_injective d
    rw [toSymmetricAlgebra_symm, toSymmetricAlgebra_map_dual, toSymmetricAlgebra_symm]
  change PiTensorProduct.map (fun _ : Fin d => f.dualMap) ((d.factorial : F)⁻¹ • _) =
    (d.factorial : F)⁻¹ • _
  simp only [map_smul, LinearEquiv.coe_coe]
  rw [h]
  congr 1
  exact (LinearMap.congr_fun (_root_.SymmetricPower.toTensorPower_comp_map f.dualMap) _).symm

omit [CharZero F] in
private theorem reindex_toTensorPower {d : ℕ} (σ : Equiv.Perm (Fin d))
    (u : Sym[F]^d (Dual F X)) :
    reindex F (fun _ : Fin d => Dual F X) σ
      (_root_.SymmetricPower.toTensorPower F (Fin d) (Dual F X) u) =
      _root_.SymmetricPower.toTensorPower F (Fin d) (Dual F X) u := by
  have h : (reindex F (fun _ : Fin d => Dual F X) σ).toLinearMap.comp
      (_root_.SymmetricPower.toTensorPower F (Fin d) (Dual F X)) =
        _root_.SymmetricPower.toTensorPower F (Fin d) (Dual F X) := by
    apply _root_.SymmetricPower.ext
    intro ℓ
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      _root_.SymmetricPower.toTensorPower_tprod, map_sum, reindex_tprod]
    exact Fintype.sum_bijective (· * σ⁻¹) (Group.mulRight_bijective _) _ _ (fun τ => rfl)
  exact LinearMap.congr_fun h u

/-- The section takes values in the actual position-permutation fixed tensors. -/
theorem polynomialSymmetricLift_reindex {d : ℕ} (σ : Equiv.Perm (Fin d))
    (p : homogeneousPolynomials F X d) :
    reindex F (fun _ : Fin d => Dual F X) σ (polynomialSymmetricLift F X d p) =
      polynomialSymmetricLift F X d p := by
  change reindex F (fun _ : Fin d => Dual F X) σ ((d.factorial : F)⁻¹ • _) =
    (d.factorial : F)⁻¹ • _
  rw [map_smul, reindex_toTensorPower]

/-- A symmetric tensor is recovered by lifting its polynomial quotient. -/
theorem polynomialSymmetricLift_eq_of_symmetric {d : ℕ}
    (p : homogeneousPolynomials F X d) (u : ⨂[F] (_ : Fin d), Dual F X)
    (hu : polynomialTensorMap F X d u = p)
    (hfix : ∀ σ : Equiv.Perm (Fin d), reindex F (fun _ : Fin d => Dual F X) σ u = u) :
    polynomialSymmetricLift F X d p = u := by
  have h : (symmetricPowerPolynomialEquiv F X d).symm p =
      _root_.SymmetricPower.mk F (Fin d) (Dual F X) u := by
    apply BostConjecture.SymmetricPower.toSymmetricAlgebra_injective d
    rw [toSymmetricAlgebra_symm, toSymmetricAlgebra_mk, hu]
  change (d.factorial : F)⁻¹ • _ = u
  simp only [LinearEquiv.coe_coe]
  rw [h, _root_.SymmetricPower.toTensorPower_mk]
  simp only [hfix, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul F, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero d)), one_smul]

/-- Invariant homogeneous polynomials have invariant tensor lifts with the same
nonzero canonical evaluation. -/
theorem exists_invariant_tensor_evaluation_ne_zero [FiniteDimensional F X]
    {G : Type*} [Group G] (ρ : Representation F G X) {d : ℕ}
    {p : SymmetricAlgebra F (Dual F X)} (hp : p ∈ homogeneousInvariants ρ d)
    {x : X} (hx : polynomialEval x p ≠ 0) :
    ∃ u : ⨂[F] (_ : Fin d), Dual F X,
      polynomialTensorMap F X d u = p ∧
      (∀ g, PiTensorProduct.map (fun _ : Fin d => (ρ g⁻¹).dualMap) u = u) ∧
      dualDistribEquivOfProjective F (fun _ : Fin d => X) u
        (tprod F fun _ : Fin d => x) ≠ 0 := by
  refine ⟨polynomialSymmetricLift F X d ⟨p, hp.1⟩,
    polynomialTensorMap_symmetricLift _, ?_, ?_⟩
  · intro g
    rw [polynomialSymmetricLift_pullback]
    congr 1
    apply Subtype.ext
    exact hp.2 g
  · rwa [← polynomialEval_tensorMap, polynomialTensorMap_symmetricLift]

end BostConjecture.Geometry
