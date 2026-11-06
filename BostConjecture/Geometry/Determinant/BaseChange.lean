/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Geometry.Determinant.Frame
public import BostConjecture.Tensor.Algebra.BaseChange
public import BostConjecture.ExternalCode.MathlibPRs.PR40948.LinearAlgebra.ExteriorPower.BaseChange

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
    simp only [map_smul, Tensor.scalarExtension_tprod]
    rw [← algebraMap_smul S r, map_smul]
    simp [tensorCoordinates_tprod, Algebra.smul_def]
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
    simp only [TensorProduct.AlgebraTensorModule.map_tmul, Algebra.linearMap_apply,
      LinearMap.id_apply, freeLatticeMap_tmul, map_smul]
    rw [← algebraMap_smul S r, map_smul]
    simp [tensorCoordinates_scalarExtension]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Scalar extension of the tensor power of the actual determinant line. -/
def determinantPowerScalarExtension (k a : ℕ) :
    (⨂[R] (_ : Fin k), ⋀[R]^a M) →ₗ[R]
      (⨂[S] (_ : Fin k), ⋀[S]^a (S ⊗[R] M)) :=
  (PiTensorProduct.map (fun _ : Fin k =>
    (exteriorPower.baseChangeEquiv R M S a).toLinearMap)).restrictScalars R ∘ₗ
      Tensor.scalarExtension R S (fun _ : Fin k => ⋀[R]^a M)

/-- Scalar extension commutes with the tensor power of the determinant line. -/
def determinantPowerBaseChangeEquiv (k a : ℕ) :
    S ⊗[R] (⨂[R] (_ : Fin k), ⋀[R]^a M) ≃ₗ[S]
      (⨂[S] (_ : Fin k), ⋀[S]^a (S ⊗[R] M)) :=
  (Tensor.baseChangeEquiv R S (fun _ : Fin k => ⋀[R]^a M)).trans
    (PiTensorProduct.congr (fun _ : Fin k => exteriorPower.baseChangeEquiv R M S a))

@[simp]
theorem determinantPowerBaseChangeEquiv_tmul (s : S)
    (η : ⨂[R] (_ : Fin k), ⋀[R]^a M) :
    determinantPowerBaseChangeEquiv k a (s ⊗ₜ[R] η) =
      s • determinantPowerScalarExtension k a η := by
  change PiTensorProduct.map (fun _ : Fin k =>
    (exteriorPower.baseChangeEquiv R M S a).toLinearMap)
      (s • Tensor.scalarExtension R S (fun _ : Fin k => ⋀[R]^a M) η) = _
  rw [map_smul]
  rfl

/-- The intrinsic determinant-twisted lattice source commutes with scalar extension. -/
def determinantTwistBaseChangeEquiv (L : Type*) [AddCommGroup L] (k a : ℕ) :
    S ⊗[R] ((⨂[R] (_ : Fin k), ⋀[R]^a M) ⊗[R] (R ⊗[ℤ] L)) ≃ₗ[S]
      (⨂[S] (_ : Fin k), ⋀[S]^a (S ⊗[R] M)) ⊗[S] (S ⊗[ℤ] L) :=
  (TensorProduct.AlgebraTensorModule.distribBaseChange R S _ _).trans
    (TensorProduct.congr (determinantPowerBaseChangeEquiv k a)
      (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ R S S L))

@[simp]
theorem determinantTwistBaseChangeEquiv_tmul (L : Type*) [AddCommGroup L]
    (s : S) (η : ⨂[R] (_ : Fin k), ⋀[R]^a M) (x : L) :
    determinantTwistBaseChangeEquiv L k a (s ⊗ₜ[R] (η ⊗ₜ[R] (1 ⊗ₜ[ℤ] x))) =
      s • (determinantPowerScalarExtension k a η ⊗ₜ[S] (1 ⊗ₜ[ℤ] x)) := by
  simp [determinantTwistBaseChangeEquiv, TensorProduct.smul_tmul']

/-- Determinant coordinates commute with the canonical exterior-power base change. -/
theorem determinantCoordinates_baseChange (b : Basis (Fin a) R M) (η : ⋀[R]^a M) :
    determinantCoordinates (b.baseChange S)
      (exteriorPower.baseChangeEquiv R M S a (1 ⊗ₜ[R] η)) =
        algebraMap R S (determinantCoordinates b η) := by
  obtain ⟨r, rfl⟩ := (determinantCoordinates b).symm.surjective η
  simp only [determinantCoordinates_symm_apply, TensorProduct.tmul_smul]
  rw [← algebraMap_smul S r, map_smul, map_smul, exteriorPower.baseChangeEquiv_apply_tmul]
  have hb : (TensorProduct.mk R S M 1) ∘ b = b.baseChange S := by
    ext i
    simp
  rw [hb]
  simp [Basis.det_self]

/-- The determinant power has the same scalar-extension compatibility. -/
theorem determinantPowerCoordinates_scalarExtension (b : Basis (Fin a) R M)
    (η : ⨂[R] (_ : Fin k), ⋀[R]^a M) :
    determinantPowerCoordinates k (b.baseChange S)
      (determinantPowerScalarExtension k a η) =
        algebraMap R S (determinantPowerCoordinates k b η) := by
  induction η using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    simp only [map_smul]
    rw [← algebraMap_smul S r, map_smul]
    simp [determinantPowerScalarExtension, determinantCoordinates_baseChange]
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

/-- The scalar-extension square is valid for any target frame, as needed on
localization overlaps. -/
theorem scalarExtension_freeDeterminantMap_of_basis (hk : 0 < k)
    (t : OAI.Saxl.Tableau n (Specht.rectangle a k)) (b : Basis (Fin a) R M)
    (c : Basis (Fin a) S (S ⊗[R] M))
    (η : ⨂[R] (_ : Fin k), ⋀[R]^a M) (z : R ⊗[ℤ] Specht.orbitLattice t) :
    Tensor.scalarExtension R S (fun _ : Fin n => M)
      (freeDeterminantMap hk t b (η ⊗ₜ[R] z)) =
    freeDeterminantMap hk t c
      (determinantPowerScalarExtension k a η ⊗ₜ[S]
        TensorProduct.AlgebraTensorModule.map (Algebra.linearMap R S)
          (LinearMap.id : Specht.orbitLattice t →ₗ[ℤ] Specht.orbitLattice t) z) := by
  rw [freeDeterminantMap_eq hk t c (b.baseChange S)]
  exact scalarExtension_freeDeterminantMap hk t b η z

/-- The full scalar-linear compatibility square, with intrinsic base-change
isomorphisms on both the source and target. -/
theorem freeDeterminantMap_baseChange (hk : 0 < k)
    (t : OAI.Saxl.Tableau n (Specht.rectangle a k)) (b : Basis (Fin a) R M)
    (c : Basis (Fin a) S (S ⊗[R] M)) :
    (Tensor.baseChangeEquiv R S (fun _ : Fin n => M)).toLinearMap ∘ₗ
        (freeDeterminantMap hk t b).baseChange S =
      freeDeterminantMap hk t c ∘ₗ
        (determinantTwistBaseChangeEquiv (Specht.orbitLattice t) k a).toLinearMap := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro s z
  induction z using TensorProduct.inductionOn with
  | tmul η z =>
    induction z using TensorProduct.inductionOn with
    | tmul r x =>
      rw [show r ⊗ₜ[ℤ] x = r • (1 ⊗ₜ[ℤ] x) by simp [TensorProduct.smul_tmul'],
        TensorProduct.tmul_smul, TensorProduct.tmul_smul]
      change Tensor.baseChangeMap R S _
        ((freeDeterminantMap hk t b).baseChange S
          ((r • s) ⊗ₜ[R] (η ⊗ₜ[R] (1 ⊗ₜ[ℤ] x)))) = _
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.baseChange_tmul,
        Tensor.baseChangeMap_tmul, scalarExtension_freeDeterminantMap_of_basis hk t b c]
      erw [determinantTwistBaseChangeEquiv_tmul (R := R) (S := S) (M := M)
        (Specht.orbitLattice t) (r • s) η x]
      simp only [map_smul, TensorProduct.AlgebraTensorModule.map_tmul,
        Algebra.linearMap_apply, map_one, LinearMap.id_apply]
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]

end BostConjecture.Geometry
