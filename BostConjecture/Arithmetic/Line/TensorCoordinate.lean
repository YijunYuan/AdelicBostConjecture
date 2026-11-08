/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Line.Coordinates
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.LinearAlgebra.TensorProduct.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-!
# Coefficient ideals of tensor products of integral lines

Multiplying two actual integral coordinates gives an injective coordinate
on their tensor product, with coefficient ideal the product of their ideals.
The proof uses flat scalar extension and localization, with no integral basis.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct
open scoped nonZeroDivisors

namespace BostConjecture.Arithmetic

variable {K : Type*} [Field K] [NumberField K]
variable {M N : Type*} [AddCommGroup M] [Module (𝓞 K) M]
    [AddCommGroup N] [Module (𝓞 K) N]

/-- Multiply the actual coordinates of two integral tensor factors. -/
def tensorCoordinate (f : M →ₗ[𝓞 K] K) (g : N →ₗ[𝓞 K] K) : M ⊗[𝓞 K] N →ₗ[𝓞 K] K :=
  (LinearMap.mul' (𝓞 K) K).comp (TensorProduct.map f g)

omit [NumberField K] in
@[simp]
lemma tensorCoordinate_tmul (f : M →ₗ[𝓞 K] K) (g : N →ₗ[𝓞 K] K) (x : M) (y : N) :
    tensorCoordinate f g (x ⊗ₜ[𝓞 K] y) = f x * g y := rfl

/-- The tensor coordinate is injective when the second factor is flat. -/
lemma tensorCoordinate_injective [Module.Flat (𝓞 K) N]
    (f : M →ₗ[𝓞 K] K) (g : N →ₗ[𝓞 K] K)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (tensorCoordinate f g) :=
  (IsLocalization.bijective_linearMap_mul' (nonZeroDivisors (𝓞 K)) K).injective.comp
    (TensorProduct.map_injective_of_flat_flat f g hf hg)

variable [Module.Finite (𝓞 K) M] [Module.Finite (𝓞 K) N]

/-- The actual tensor-coordinate ideal is the product of the factor ideals. -/
theorem coordinateIdeal_tensor (f : M →ₗ[𝓞 K] K) (g : N →ₗ[𝓞 K] K) :
    coordinateIdeal (tensorCoordinate f g) = coordinateIdeal f * coordinateIdeal g := by
  have he : tensorCoordinate f g = (Submodule.mulMap f.range g.range).comp
      (TensorProduct.map f.rangeRestrict g.rangeRestrict) := by
    apply TensorProduct.ext'
    intro x y
    rfl
  apply FractionalIdeal.coeToSubmodule_injective
  dsimp only
  rw [FractionalIdeal.coe_mul]
  change (tensorCoordinate f g).range = f.range * g.range
  rw [he, LinearMap.range_comp,
    LinearMap.range_eq_top.mpr (TensorProduct.map_surjective f.surjective_rangeRestrict
      g.surjective_rangeRestrict), Submodule.map_top, Submodule.mulMap_range]

/-- The finite logarithmic contribution is additive for tensor coordinates. -/
theorem logIdealNorm_tensorCoordinate [Nontrivial M] [Nontrivial N]
    (f : M →ₗ[𝓞 K] K) (g : N →ₗ[𝓞 K] K)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    logIdealNorm (coordinateIdeal (tensorCoordinate f g)) =
      logIdealNorm (coordinateIdeal f) + logIdealNorm (coordinateIdeal g) := by
  rw [coordinateIdeal_tensor]
  exact logIdealNorm_mul (coordinateIdeal_ne_zero f hf) (coordinateIdeal_ne_zero g hg)

end BostConjecture.Arithmetic
