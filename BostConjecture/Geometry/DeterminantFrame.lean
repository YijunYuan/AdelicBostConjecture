module

public import BostConjecture.Geometry.FreeEmbedding
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.Determinant

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

/-- Coordinates on the actual top exterior power, normalized by the basis wedge. -/
def determinantCoordinates (b : Basis (Fin a) R M) : (⋀[R]^a M) ≃ₗ[R] R :=
  LinearEquiv.ofLinearMap (alternatingMapLinearEquiv b.det)
    (LinearMap.toSpanSingleton R _ (ιMulti R a b))
    (by ext; simp [Basis.det_self])
    (by
      apply exteriorPower.linearMap_ext
      apply b.ext_alternating
      intro p hp
      let σ : Equiv.Perm (Fin a) := Equiv.ofBijective p
        (Finite.injective_iff_bijective.mp hp)
      simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
        LinearMap.id_apply, LinearMap.toSpanSingleton_apply,
        alternatingMapLinearEquiv_apply_ιMulti]
      change b.det (b ∘ σ) • ιMulti R a b = ιMulti R a (b ∘ σ)
      simp [AlternatingMap.map_perm, Basis.det_self])

@[simp]
theorem determinantCoordinates_ιMulti (b : Basis (Fin a) R M) (v : Fin a → M) :
    determinantCoordinates b (ιMulti R a v) = b.det v :=
  alternatingMapLinearEquiv_apply_ιMulti b.det v

@[simp]
theorem determinantCoordinates_symm_apply (b : Basis (Fin a) R M) (r : R) :
    (determinantCoordinates b).symm r = r • ιMulti R a b := rfl

/-- The determinant coordinate of a top wedge transforms by the frame determinant. -/
theorem determinantCoordinates_change_basis (b c : Basis (Fin a) R M)
    (η : ⋀[R]^a M) :
    determinantCoordinates c η =
      (LinearMap.toMatrix b c (LinearMap.id : M →ₗ[R] M)).det *
        determinantCoordinates b η := by
  have h : c.det b = (LinearMap.toMatrix b c (LinearMap.id : M →ₗ[R] M)).det := by
    rw [Basis.det_apply]
    congr 1
    ext i j
    simp [Basis.toMatrix_apply, LinearMap.toMatrix_apply]
  obtain ⟨r, rfl⟩ := (determinantCoordinates b).symm.surjective η
  simp only [determinantCoordinates_symm_apply, map_smul, determinantCoordinates_ιMulti,
    Basis.det_self, smul_eq_mul, mul_one]
  rw [h, mul_comm]

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

/-- The determinant line absorbs the frame dependence of the lattice map. -/
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
