/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.SpecialLinearGroup
public import Mathlib.RepresentationTheory.Basic

/-!
# The intrinsic special-linear action on the Plücker exterior power

The independent special-linear actions on two factors induce an action
on exterior powers of their tensor product. This is the Plücker action
used in the geometric semistability criterion.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.InvariantTheory

open scoped TensorProduct
open exteriorPower

/-- The actual exterior power of the tensor product action of the two special linear groups. -/
def pluckerRepresentation (K U W : Type*) [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup W] [Module K W] (s : ℕ) :
    Representation K (SpecialLinearGroup K U × SpecialLinearGroup K W) (⋀[K]^s (U ⊗[K] W)) where
  toFun g := exteriorPower.map s (TensorProduct.map (g.1 : U →ₗ[K] U) (g.2 : W →ₗ[K] W))
  map_one' := by
    simp
    rfl
  map_mul' g h := by
    simp only [Prod.fst_mul, Prod.snd_mul, SpecialLinearGroup.coe_mul,
      LinearEquiv.coe_toLinearMap_mul, Module.End.mul_eq_comp]
    rw [TensorProduct.map_comp, map_comp]

variable {K U W : Type*} [Field K]
  [AddCommGroup U] [Module K U] [AddCommGroup W] [Module K W]

@[simp]
theorem pluckerRepresentation_apply (s : ℕ)
    (g : SpecialLinearGroup K U × SpecialLinearGroup K W) (z : ⋀[K]^s (U ⊗[K] W)) :
    pluckerRepresentation K U W s g z =
      exteriorPower.map s (TensorProduct.map (g.1 : U →ₗ[K] U) (g.2 : W →ₗ[K] W)) z := rfl

end BostConjecture.InvariantTheory
