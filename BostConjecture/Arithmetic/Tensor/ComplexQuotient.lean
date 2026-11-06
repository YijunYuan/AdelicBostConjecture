/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Exterior.OrthogonalLift
public import BostConjecture.Tensor.Metric.Basic
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Orthogonal quotient lifts commute with Hilbert tensor products

The tensor of the orthogonal right inverse has image perpendicular to the
actual tensor kernel. Uniqueness then identifies it with the quotient lift.
-/

@[expose] public section

noncomputable section

open TensorProduct
open scoped InnerProductSpace

namespace BostConjecture.Arithmetic.ComplexQuotient

variable {E F W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [AddCommGroup F] [Module ℂ F]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

/-- Right tensoring the orthogonal lift gives the orthogonal lift of the
right-tensored surjection. -/
lemma lift_rTensor (f : E →ₗ[ℂ] F) (hf : Function.Surjective f) (z : F ⊗[ℂ] W) :
    lift (f.rTensor W) (LinearMap.rTensor_surjective W hf) z =
      (lift f hf).rTensor W z := by
  symm
  apply eq_lift
  · rw [Submodule.mem_orthogonal]
    intro u hu
    have hk : LinearMap.ker (f.rTensor W) =
        LinearMap.range ((LinearMap.ker f).subtype.rTensor W) :=
      (rTensor_exact W f.exact_subtype_ker_map hf).linearMap_ker_eq
    obtain ⟨v, rfl⟩ := (SetLike.ext_iff.mp hk u).mp hu
    clear hu
    induction v using TensorProduct.inductionOn with
    | tmul x w =>
      induction z using TensorProduct.inductionOn with
      | tmul y w' =>
        rw [LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, TensorProduct.inner_tmul]
        have ho := (Submodule.mem_orthogonal _ _).mp (lift_mem f hf y) x x.property
        exact mul_eq_zero_of_left ho _
      | add y z hy hz => simp only [map_add, inner_add_right, hy, hz, add_zero]
    | add x y hx hy => simp only [map_add, inner_add_left, hx, hy, add_zero]
  · induction z using TensorProduct.inductionOn with
    | tmul y w => simp only [LinearMap.rTensor_tmul, map_lift]
    | add x y hx hy => simp only [map_add, hx, hy]

/-- The orthogonal quotient form on a tensor is the binary tensor of the
orthogonal quotient form and the unchanged factor. -/
lemma core_rTensor_inner (f : E →ₗ[ℂ] F) (hf : Function.Surjective f)
    (x y : F ⊗[ℂ] W) :
    (core (f.rTensor W) (LinearMap.rTensor_surjective W hf)).inner x y =
      (Tensor.binaryCore (core f hf) (InnerProductSpace.toCore (𝕜 := ℂ) (E := W))).inner x y := by
  let c := Tensor.binaryCore (core f hf) (InnerProductSpace.toCore (𝕜 := ℂ) (E := W))
  let c' : PreInnerProductSpace.Core ℂ (F ⊗[ℂ] W) := { __ := c }
  change inner ℂ (lift (f.rTensor W) _ x) (lift (f.rTensor W) _ y) = c.inner x y
  rw [lift_rTensor f hf, lift_rTensor f hf]
  induction x using TensorProduct.inductionOn with
  | tmul a w =>
    induction y using TensorProduct.inductionOn with
    | tmul b w' =>
      rw [LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, TensorProduct.inner_tmul]
      exact (Tensor.binaryCore_inner_tmul (core f hf)
        (InnerProductSpace.toCore (𝕜 := ℂ) (E := W)) a b w w').symm
    | add y z hy hz =>
      simp only [map_add, inner_add_right, InnerProductSpace.Core.inner_add_right (c := c'), hy, hz]
  | add x z hx hz => simp only [map_add, inner_add_left, c.add_left, hx, hz]

end BostConjecture.Arithmetic.ComplexQuotient
