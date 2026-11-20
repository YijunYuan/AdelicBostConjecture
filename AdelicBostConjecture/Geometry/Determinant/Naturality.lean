/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import AdelicBostConjecture.Geometry.Determinant.Frame

/-!
# Naturality of the determinant-twisted free inclusion

The determinant twist absorbs the covariance factor for arbitrary linear
maps, including noninvertible ones. This allows local realizations to be
transported between free models of a localized projective module.
-/

@[expose] public section

noncomputable section

namespace AdelicBostConjecture.Geometry

open Module exteriorPower
open scoped TensorProduct

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {n a k : ℕ}

/-- The top exterior-power map has the matrix determinant as its coordinate. -/
theorem determinantCoordinates_map (b : Basis (Fin a) R M) (c : Basis (Fin a) R N)
    (f : M →ₗ[R] N) (η : ⋀[R]^a M) :
    determinantCoordinates c (exteriorPower.map a f η) =
      (LinearMap.toMatrix b c f).det * determinantCoordinates b η := by
  have h : c.det (f ∘ b) = (LinearMap.toMatrix b c f).det := by
    rw [Basis.det_apply]
    congr 1
    ext i j
    simp [Basis.toMatrix_apply, LinearMap.toMatrix_apply]
  obtain ⟨r, rfl⟩ := (determinantCoordinates b).symm.surjective η
  simp only [determinantCoordinates_symm_apply, map_smul, map_apply_ιMulti,
    determinantCoordinates_ιMulti, Basis.det_self, smul_eq_mul, mul_one, h]
  exact mul_comm _ _

/-- Tensoring the top exterior-power map gives the determinant power. -/
theorem determinantPowerCoordinates_map (b : Basis (Fin a) R M)
    (c : Basis (Fin a) R N) (f : M →ₗ[R] N)
    (η : ⨂[R] (_ : Fin k), ⋀[R]^a M) :
    determinantPowerCoordinates k c
      (PiTensorProduct.map (fun _ : Fin k => exteriorPower.map a f) η) =
      (LinearMap.toMatrix b c f).det ^ k * determinantPowerCoordinates k b η := by
  induction η using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    simp only [map_smul, PiTensorProduct.map_tprod, determinantPowerCoordinates_tprod,
      determinantCoordinates_map b c, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  | add x y hx hy => simp only [map_add, hx, hy, mul_add]

/-- Naturality on elementary determinant-twisted tensors. -/
theorem map_freeDeterminantMap_tmul (hk : 0 < k)
    (t : OAI.Saxl.Tableau n (Specht.rectangle a k))
    (b : Basis (Fin a) R M) (c : Basis (Fin a) R N) (f : M →ₗ[R] N)
    (η : ⨂[R] (_ : Fin k), ⋀[R]^a M) (z : R ⊗[ℤ] Specht.orbitLattice t) :
    PiTensorProduct.map (fun _ : Fin n => f)
      (freeDeterminantMap hk t b (η ⊗ₜ[R] z)) =
    freeDeterminantMap hk t c
      (PiTensorProduct.map (fun _ : Fin k => exteriorPower.map a f) η ⊗ₜ[R] z) := by
  simp only [freeDeterminantMap_tmul, map_smul, map_freeLatticeMap hk t b c f,
    determinantPowerCoordinates_map b c f, smul_smul]
  rw [mul_comm]

/-- The actual determinant-twisted inclusion is natural for all linear maps
between free modules of the same rank. -/
theorem map_freeDeterminantMap (hk : 0 < k)
    (t : OAI.Saxl.Tableau n (Specht.rectangle a k))
    (b : Basis (Fin a) R M) (c : Basis (Fin a) R N) (f : M →ₗ[R] N) :
    PiTensorProduct.map (fun _ : Fin n => f) ∘ₗ freeDeterminantMap hk t b =
    freeDeterminantMap hk t c ∘ₗ
      TensorProduct.map (PiTensorProduct.map (fun _ : Fin k => exteriorPower.map a f))
        (LinearMap.id : (R ⊗[ℤ] Specht.orbitLattice t) →ₗ[R] _) := by
  apply TensorProduct.ext'
  intro η z
  simpa only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply] using
    map_freeDeterminantMap_tmul hk t b c f η z

end AdelicBostConjecture.Geometry
