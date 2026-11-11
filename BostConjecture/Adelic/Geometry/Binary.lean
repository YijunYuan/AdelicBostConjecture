/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.InvariantTheory.Binary.TensorTransport
public import BostConjecture.Geometry.Plucker.Nonvanishing

/-!
# Binary tensor duality in the Bool convention

The finite-family dual inclusion agrees with the ordinary binary dual inclusion
under ArakelovGeometry's prescribed Bool tensor equivalence. This identifies the
map in the nonvanishing producer with the map used by the binary norm estimates.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Adelic.Geometry

open Module PiTensorProduct ArakelovGeometry
open scoped TensorProduct

variable {K : Type*} [Field K] (E : Bool → Type*)
  [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]
  [∀ i, FiniteDimensional K (E i)]

/-- The prescribed Bool equivalence preserves tensor-dual evaluation. -/
theorem dualDistrib_boolTensorEquiv (z : ⨂[K] i, Dual K (E i)) (x : ⨂[K] i, E i) :
    TensorProduct.dualDistribEquiv K (E false) (E true)
      (boolTensorEquiv K (fun i ↦ Dual K (E i)) z) (boolTensorEquiv K E x) =
      dualDistribEquivOfProjective K E z x := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod a f =>
    induction x using PiTensorProduct.induction_on with
    | smul_tprod b y =>
      simp [finprod_eq_prod_of_fintype, mul_comm]
    | add x y hx hy => simp only [map_add, hx, hy]
  | add z w hz hw => simp only [map_add, LinearMap.add_apply, hz, hw]

/-- The original quotient's dual inclusion is the same map in the Bool tensor
model and in the ordinary binary tensor model. -/
theorem dualTensorInclusion_bool
    {V : Type*} [AddCommGroup V] [Module K V]
    (q : E false ⊗[K] E true →ₗ[K] V) :
    (boolTensorEquiv K (fun i ↦ Dual K (E i))).toLinearMap ∘ₗ
      (dualDistribEquivOfProjective K E).symm.toLinearMap ∘ₗ
      (q ∘ₗ (boolTensorEquiv K E).toLinearMap).dualMap =
    (TensorProduct.dualDistribEquiv K (E false) (E true)).symm.toLinearMap ∘ₗ q.dualMap := by
  apply LinearMap.ext
  intro ℓ
  apply (TensorProduct.dualDistribEquiv K (E false) (E true)).injective
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := (boolTensorEquiv K E).surjective x
  change TensorProduct.dualDistribEquiv K (E false) (E true)
      (boolTensorEquiv K (fun i ↦ Dual K (E i))
        ((dualDistribEquivOfProjective K E).symm _)) (boolTensorEquiv K E y) = _
  rw [dualDistrib_boolTensorEquiv, LinearEquiv.apply_symm_apply]
  simp

end BostConjecture.Adelic.Geometry
