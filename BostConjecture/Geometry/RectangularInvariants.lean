module

public import BostConjecture.Geometry.RectangularSpan
public import Mathlib.LinearAlgebra.SpecialLinearGroup
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Rectangular special-linear invariant tensors over algebraically closed fields

A determinant root turns any invertible map into a special-linear map. The
resulting weight identity feeds the checked rectangular rank-one argument.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Geometry

open Module PiTensorProduct
open scoped TensorProduct

variable {F M : Type*} [Field F] [CharZero F] [AddCommGroup M] [Module F M]
  [FiniteDimensional F M] {n a k : ℕ}

omit [CharZero F] [FiniteDimensional F M] in
/-- Scaling all factors scales a tensor-power operator by the degree power. -/
theorem tensorPower_map_smul (c : F) (f : M →ₗ[F] M) (v : ⨂[F] (_ : Fin n), M) :
    PiTensorProduct.map (fun _ => c • f) v =
      c ^ n • PiTensorProduct.map (fun _ => f) v := by
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r x => simp [PiTensorProduct.tprod_smul, smul_comm]
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]

/-- Over an algebraic closure, actual SL invariance implies the rectangular
GL determinant weight. -/
theorem determinant_covariant_of_specialLinear_fixed [IsAlgClosed F]
    (ha : 0 < a) (hn : n = a * k) (b : Basis (Fin a) F M)
    (v : ⨂[F] (_ : Fin n), M)
    (hv : ∀ g : SpecialLinearGroup F M,
      PiTensorProduct.map (fun _ => (g : M →ₗ[F] M)) v = v)
    (g : (Module.End F M)ˣ) :
    PiTensorProduct.map (fun _ => (g : Module.End F M)) v =
      (LinearMap.toMatrix b b (g : Module.End F M)).det ^ k • v := by
  let e := LinearMap.GeneralLinearGroup.toLinearEquiv g
  have he : (e : M →ₗ[F] M) = (g : Module.End F M) := rfl
  have hd : LinearMap.det (g : Module.End F M) ≠ 0 := by
    rw [← he, ← LinearEquiv.coe_det]
    exact Units.ne_zero e.det
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (LinearMap.det (g : Module.End F M)) ha
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, zero_pow (Nat.ne_of_gt ha)] at hc
    exact hd hc.symm
  let e' := e.trans (LinearEquiv.smulOfUnit (Units.mk0 c hc0)⁻¹)
  have he' : (e' : M →ₗ[F] M) = c⁻¹ • (g : Module.End F M) := by
    apply LinearMap.ext
    intro x
    rfl
  have hedet : e'.det = 1 := by
    apply Units.ext
    rw [LinearEquiv.coe_det, he', LinearMap.det_smul,
      Module.finrank_eq_card_basis b, Fintype.card_fin, inv_pow, hc, inv_mul_cancel₀ hd]
    rfl
  have hfix := hv ⟨e', hedet⟩
  change PiTensorProduct.map (fun _ => (e' : M →ₗ[F] M)) v = v at hfix
  rw [he', tensorPower_map_smul] at hfix
  have hmul := congrArg (fun x => c ^ n • x) hfix
  rw [smul_smul, ← mul_pow, mul_inv_cancel₀ hc0, one_pow, one_smul] at hmul
  rw [hmul, hn, pow_mul, hc, LinearMap.det_toMatrix]

/-- Actual SL-fixed tensors are exactly the scalar-extended rectangular
integral lattice, over an algebraically closed characteristic-zero field. -/
theorem mem_range_freeLatticeMap_iff_specialLinear_fixed [IsAlgClosed F]
    (ha : 0 < a) (hk : 0 < k)
    (t : OAI.Saxl.Tableau n (Specht.rectangle a k)) (b : Basis (Fin a) F M)
    (v : ⨂[F] (_ : Fin n), M) :
    v ∈ LinearMap.range (freeLatticeMap hk t b) ↔
      ∀ g : SpecialLinearGroup F M,
        PiTensorProduct.map (fun _ => (g : M →ₗ[F] M)) v = v := by
  constructor
  · rintro ⟨x, rfl⟩ g
    rw [map_freeLatticeMap hk t b b, LinearMap.det_toMatrix, g.det_eq_one, one_pow, one_smul]
  · intro hv
    apply mem_range_freeLatticeMap_of_determinant_covariant hk t b v
    have hn : n = a * k := by
      simpa using Fintype.card_congr (Specht.rectangleCoordinates t)
    exact determinant_covariant_of_specialLinear_fixed ha hn b v hv

end BostConjecture.Geometry
