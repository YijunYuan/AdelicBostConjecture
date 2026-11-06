/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Geometry.Tensor.LatticeMetric
public import BostConjecture.Geometry.Determinant.Frame
public import BostConjecture.Arithmetic.Determinant.Metric

/-!
# Isometry of the local determinant-twisted inclusion

The source form is the tensor product of the existing Gram determinant form
and the canonical complex lattice form. The target is the actual Hilbert
tensor core. No metric-preservation hypothesis is assumed.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Geometry

open Module PiTensorProduct
open scoped TensorProduct

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {a k n : ℕ}

/-- Determinant tensor coordinates of an orthonormal frame preserve the scalar form. -/
theorem determinantPowerCore_inner (b : OrthonormalBasis (Fin a) ℂ M)
    (η ξ : ⨂[ℂ] (_ : Fin k), ⋀[ℂ]^a M) :
    (Tensor.tensorCore (fun _ : Fin k => Arithmetic.ComplexDeterminant.core b)).inner η ξ =
      star (determinantPowerCoordinates k b.toBasis η) *
        determinantPowerCoordinates k b.toBasis ξ := by
  have h := Tensor.inner_ext_of_span (PiTensorProduct.tprod ℂ)
    (span_tprod_eq_top (R := ℂ) (s := fun _ : Fin k => ⋀[ℂ]^a M))
    (Tensor.tensorCore (fun _ : Fin k => Arithmetic.ComplexDeterminant.core b))
    (InnerProductSpace.toCore (𝕜 := ℂ) (E := ℂ)) LinearMap.id
    (determinantPowerCoordinates k b.toBasis).toLinearMap
  have hp : ∀ (v w : Fin k → ⋀[ℂ]^a M),
      (Tensor.tensorCore (fun _ : Fin k => Arithmetic.ComplexDeterminant.core b)).inner
        (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ w) =
      inner ℂ (determinantPowerCoordinates k b.toBasis (PiTensorProduct.tprod ℂ v))
        (determinantPowerCoordinates k b.toBasis (PiTensorProduct.tprod ℂ w)) := by
    intro v w
    simp [Tensor.tensorCore_inner_tprod, Arithmetic.ComplexDeterminant.core_inner,
      determinantPowerCoordinates_tprod, finprod_eq_prod_of_fintype,
      Finset.prod_mul_distrib, map_prod, RCLike.inner_apply, mul_comm]
  exact (h hp η ξ).trans (mul_comm _ _)

/-- The local determinant inclusion is an isometry for the prescribed metrics. -/
theorem freeDeterminantMap_inner (hk : 0 < k)
    (t : OAI.Saxl.Tableau n (Specht.rectangle a k)) (b : OrthonormalBasis (Fin a) ℂ M)
    (x y : (⨂[ℂ] (_ : Fin k), ⋀[ℂ]^a M) ⊗[ℂ] (ℂ ⊗[ℤ] Specht.orbitLattice t)) :
    (Tensor.hilbertCore (fun _ : Fin n => M)).inner
      (freeDeterminantMap hk t b.toBasis x) (freeDeterminantMap hk t b.toBasis y) =
    (Tensor.binaryCore
      (Tensor.tensorCore (fun _ : Fin k => Arithmetic.ComplexDeterminant.core b))
      (latticeComplexCore t)).inner x y := by
  let : AddCommGroup ((⨂[ℂ] (_ : Fin k), ⋀[ℂ]^a M) ⊗[ℂ]
      (ℂ ⊗[ℤ] Specht.orbitLattice t)) := TensorProduct.addCommGroup
        (R := ℂ) (M := ⨂[ℂ] (_ : Fin k), ⋀[ℂ]^a M) (N := ℂ ⊗[ℤ] Specht.orbitLattice t)
  let c := Tensor.hilbertCore (fun _ : Fin n => M)
  let c' : PreInnerProductSpace.Core ℂ (⨂[ℂ] (_ : Fin n), M) := { __ := c }
  apply Tensor.inner_ext_of_span
    (A := (⨂[ℂ] (_ : Fin k), ⋀[ℂ]^a M) ⊗[ℂ] (ℂ ⊗[ℤ] Specht.orbitLattice t))
    (V := ⨂[ℂ] (_ : Fin n), M)
    (W := (⨂[ℂ] (_ : Fin k), ⋀[ℂ]^a M) ⊗[ℂ] (ℂ ⊗[ℤ] Specht.orbitLattice t))
    (fun p : (⨂[ℂ] (_ : Fin k), ⋀[ℂ]^a M) × (ℂ ⊗[ℤ] Specht.orbitLattice t) =>
      p.1 ⊗ₜ[ℂ] p.2) _ c
    (Tensor.binaryCore
      (Tensor.tensorCore (fun _ : Fin k => Arithmetic.ComplexDeterminant.core b))
      (latticeComplexCore t))
    (freeDeterminantMap hk t b.toBasis) LinearMap.id _ x y
  · convert TensorProduct.span_tmul_eq_top (R := ℂ)
      (⨂[ℂ] (_ : Fin k), ⋀[ℂ]^a M) (ℂ ⊗[ℤ] Specht.orbitLattice t) using 1
    congr 1
    ext z
    simp only [Set.mem_range, Set.mem_ofPred_eq, Prod.exists]
  · rintro ⟨η, z⟩ ⟨ξ, w⟩
    simp only [freeDeterminantMap_tmul, LinearMap.id_apply]
    change c.inner (determinantPowerCoordinates k b.toBasis η • freeLatticeMap hk t b.toBasis z)
      (determinantPowerCoordinates k b.toBasis ξ • freeLatticeMap hk t b.toBasis w) =
      (Tensor.tensorCore (fun _ : Fin k => Arithmetic.ComplexDeterminant.core b)).inner η ξ *
        (latticeComplexCore t).inner z w
    rw [c.smul_left, InnerProductSpace.Core.inner_smul_right (c := c'),
      freeLatticeMap_inner, determinantPowerCore_inner]
    simp only [RCLike.star_def]
    ring

end BostConjecture.Geometry
