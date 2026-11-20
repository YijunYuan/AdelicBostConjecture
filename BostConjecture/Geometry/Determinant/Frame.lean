/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Geometry.Determinant.Coordinates
public import BostConjecture.Geometry.Tensor.FreeEmbedding

/-!
# Frame-independent determinant-twisted tensor realization

The top exterior power supplies the determinant line. Its frame coordinates
absorb exactly the determinant weight in the rectangular lattice realization.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Geometry

open Module exteriorPower
open scoped TensorProduct

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable {n a k : ℕ}

/-- Tensor-power coordinates on the determinant line. -/
def determinantPowerCoordinates (k : ℕ) (b : Basis (Fin a) R M) :
    (⨂[R] (_ : Fin k), ⋀[R]^a M) ≃ₗ[R] R :=
  PiTensorProduct.congr (fun _ : Fin k => determinantCoordinates b) ≪≫ₗ
    (PiTensorProduct.constantBaseRingEquiv (Fin k) R).toLinearEquiv

@[simp]
theorem determinantPowerCoordinates_tprod (b : Basis (Fin a) R M)
    (η : Fin k → ⋀[R]^a M) :
    determinantPowerCoordinates k b (PiTensorProduct.tprod R η) =
      ∏ q, determinantCoordinates b (η q) := by
  simp [determinantPowerCoordinates]

theorem determinantPowerCoordinates_change_basis (b c : Basis (Fin a) R M)
    (η : ⨂[R] (_ : Fin k), ⋀[R]^a M) :
    determinantPowerCoordinates k c η =
      (LinearMap.toMatrix b c (LinearMap.id : M →ₗ[R] M)).det ^ k *
        determinantPowerCoordinates k b η := by
  induction η using PiTensorProduct.induction_on with
  | smul_tprod r η =>
    simp only [map_smul, determinantPowerCoordinates_tprod, smul_eq_mul,
      determinantCoordinates_change_basis b c, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    ring
  | add x y hx hy => simp only [map_add, hx, hy, mul_add]

/-- The local determinant-twisted inclusion, with an intrinsic source formed
from the actual top exterior power and integral lattice. -/
def freeDeterminantMap (hk : 0 < k)
    (t : OAI.Saxl.Tableau n (Specht.rectangle a k)) (b : Basis (Fin a) R M) :
    (⨂[R] (_ : Fin k), ⋀[R]^a M) ⊗[R] (R ⊗[ℤ] Specht.orbitLattice t) →ₗ[R]
      (⨂[R] (_ : Fin n), M) :=
  freeLatticeMap hk t b ∘ₗ (TensorProduct.lid R _).toLinearMap ∘ₗ
    (LinearEquiv.rTensor _ (determinantPowerCoordinates k b)).toLinearMap

@[simp]
theorem freeDeterminantMap_tmul (hk : 0 < k)
    (t : OAI.Saxl.Tableau n (Specht.rectangle a k)) (b : Basis (Fin a) R M)
    (η : ⨂[R] (_ : Fin k), ⋀[R]^a M) (z : R ⊗[ℤ] Specht.orbitLattice t) :
    freeDeterminantMap hk t b (η ⊗ₜ[R] z) =
      determinantPowerCoordinates k b η • freeLatticeMap hk t b z := by
  simp [freeDeterminantMap]

theorem freeDeterminantMap_injective [Module.Flat ℤ R] (hk : 0 < k)
    (t : OAI.Saxl.Tableau n (Specht.rectangle a k)) (b : Basis (Fin a) R M) :
    Function.Injective (freeDeterminantMap hk t b) :=
  (freeLatticeMap_injective hk t b).comp <|
    (TensorProduct.lid R _).injective.comp <|
    (LinearEquiv.rTensor _ (determinantPowerCoordinates k b)).injective

/-- This paper, proof of Lemma 6.1, independence of the chosen frame.

The determinant line absorbs the frame dependence of the lattice map. -/
theorem freeDeterminantMap_eq (hk : 0 < k)
    (t : OAI.Saxl.Tableau n (Specht.rectangle a k)) (b c : Basis (Fin a) R M) :
    freeDeterminantMap hk t b = freeDeterminantMap hk t c := by
  apply TensorProduct.ext'
  intro η z
  simp only [freeDeterminantMap_tmul]
  rw [freeLatticeMap_change_basis hk t b c z,
    determinantPowerCoordinates_change_basis b c η, smul_smul, mul_comm]

/-- The intrinsic determinant-twisted map has the required local normalization. -/
theorem freeDeterminantMap_basis (hk : 0 < k)
    (t : OAI.Saxl.Tableau n (Specht.rectangle a k)) (b : Basis (Fin a) R M)
    (z : R ⊗[ℤ] Specht.orbitLattice t) :
    freeDeterminantMap hk t b
      (PiTensorProduct.tprod R (fun _ : Fin k => ιMulti R a b) ⊗ₜ[R] z) =
        freeLatticeMap hk t b z := by
  simp [Basis.det_self]

end BostConjecture.Geometry
