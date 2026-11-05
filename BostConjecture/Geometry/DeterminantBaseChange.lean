module

public import BostConjecture.Geometry.DeterminantFrame
public import BostConjecture.Tensor.BaseChange
public import BostConjecture.LinearAlgebra.ExteriorPower.BaseChange

/-!
# Scalar extension of the determinant-twisted free inclusion

The tensor and exterior-power scalar-extension maps commute with the actual
integral rectangular inclusion. These identities apply in particular to
localization and supply the compatibility required on overlaps.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Geometry

open Module PiTensorProduct exteriorPower
open scoped TensorProduct

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] {n a k : ℕ}

/-- Tensor coordinates commute with scalar extension. -/
theorem tensorCoordinates_scalarExtension (b : Basis (Fin a) R M)
    (z : ⨂[R] (_ : Fin n), M) :
    tensorCoordinates n (b.baseChange S)
      (Tensor.scalarExtension R S (fun _ : Fin n => M) z) =
        fun w => algebraMap R S (tensorCoordinates n b z w) := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    ext w
    simp [LinearMapClass.map_smul_of_tower, Algebra.smul_def, tensorCoordinates_tprod]
  | add x y hx hy =>
    ext w
    simp only [map_add, hx, hy, Pi.add_apply]

/-- The integral rectangular realization commutes with extension of coefficients. -/
theorem scalarExtension_freeLatticeMap (hk : 0 < k)
    (t : OAI.Saxl.Tableau n (Specht.rectangle a k)) (b : Basis (Fin a) R M)
    (z : R ⊗[ℤ] Specht.orbitLattice t) :
    Tensor.scalarExtension R S (fun _ : Fin n => M) (freeLatticeMap hk t b z) =
      freeLatticeMap hk t (b.baseChange S)
        (TensorProduct.AlgebraTensorModule.map (Algebra.linearMap R S)
          (LinearMap.id : Specht.orbitLattice t →ₗ[ℤ] Specht.orbitLattice t) z) := by
  induction z using TensorProduct.inductionOn with
  | tmul r x =>
    apply (tensorCoordinates n (b.baseChange S)).injective
    ext w
    simp [LinearMapClass.map_smul_of_tower, tensorCoordinates_scalarExtension,
      freeLatticeMap_tmul, Algebra.smul_def]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Scalar extension of the tensor power of the actual determinant line. -/
def determinantPowerScalarExtension (k a : ℕ) :
    (⨂[R] (_ : Fin k), ⋀[R]^a M) →ₗ[R]
      (⨂[S] (_ : Fin k), ⋀[S]^a (S ⊗[R] M)) :=
  (PiTensorProduct.map (fun _ : Fin k =>
    (exteriorPower.baseChangeEquiv R M S a).toLinearMap)).restrictScalars R ∘ₗ
      Tensor.scalarExtension R S (fun _ : Fin k => ⋀[R]^a M)

/-- Determinant coordinates commute with the canonical exterior-power base change. -/
theorem determinantCoordinates_baseChange (b : Basis (Fin a) R M) (η : ⋀[R]^a M) :
    determinantCoordinates (b.baseChange S)
      (exteriorPower.baseChangeEquiv R M S a (1 ⊗ₜ[R] η)) =
        algebraMap R S (determinantCoordinates b η) := by
  obtain ⟨r, rfl⟩ := (determinantCoordinates b).symm.surjective η
  simp only [determinantCoordinates_symm_apply, TensorProduct.tmul_smul,
    LinearMapClass.map_smul_of_tower, determinantCoordinates_ιMulti, Basis.det_self, smul_eq_mul, mul_one]
  rw [exteriorPower.baseChangeEquiv_apply_tmul]
  have hb : (TensorProduct.mk R S M 1) ∘ b = b.baseChange S := by
    ext i
    simp
  rw [hb]
  simp [Basis.det_self, Algebra.smul_def]

/-- The determinant power has the same scalar-extension compatibility. -/
theorem determinantPowerCoordinates_scalarExtension (b : Basis (Fin a) R M)
    (η : ⨂[R] (_ : Fin k), ⋀[R]^a M) :
    determinantPowerCoordinates k (b.baseChange S)
      (determinantPowerScalarExtension k a η) =
        algebraMap R S (determinantPowerCoordinates k b η) := by
  induction η using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    simp [determinantPowerScalarExtension, LinearMapClass.map_smul_of_tower,
      determinantCoordinates_baseChange,
      Algebra.smul_def]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The actual determinant-twisted inclusion commutes with scalar extension. -/
theorem scalarExtension_freeDeterminantMap (hk : 0 < k)
    (t : OAI.Saxl.Tableau n (Specht.rectangle a k)) (b : Basis (Fin a) R M)
    (η : ⨂[R] (_ : Fin k), ⋀[R]^a M) (z : R ⊗[ℤ] Specht.orbitLattice t) :
    Tensor.scalarExtension R S (fun _ : Fin n => M)
      (freeDeterminantMap hk t b (η ⊗ₜ[R] z)) =
    freeDeterminantMap hk t (b.baseChange S)
      (determinantPowerScalarExtension k a η ⊗ₜ[S]
        TensorProduct.AlgebraTensorModule.map (Algebra.linearMap R S)
          (LinearMap.id : Specht.orbitLattice t →ₗ[ℤ] Specht.orbitLattice t) z) := by
  simp only [freeDeterminantMap_tmul, map_smul,
    scalarExtension_freeLatticeMap, determinantPowerCoordinates_scalarExtension]
  rw [algebraMap_smul]

end BostConjecture.Geometry
