/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Submodule.IntegralSubspace
public import BostConjecture.Arithmetic.Exterior.Metric
public import BostConjecture.Arithmetic.Exterior.PluckerRecovery

/-!
# Generic images of integral determinant sections

The canonical exterior scalar extension identifies the image of an integral
determinant section with a Plücker vector of its actual generic subspace.
-/

@[expose] public section

noncomputable section

open NumberField exteriorPower Module
open scoped TensorProduct

namespace BostConjecture.Arithmetic

variable {K : Type*} [Field K] [NumberField K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]

@[simp]
lemma integralPartGenericEquiv_tmul (X : Submodule K (K ⊗[𝓞 K] M))
    (a : K) (x : integralPart X) :
    (integralPartGenericEquiv X (a ⊗ₜ[𝓞 K] x) : K ⊗[𝓞 K] M) = a ⊗ₜ[𝓞 K] (x : M) := rfl

/-- Generic scalar extension of an integral exterior inclusion lies in the
exterior image of the original generic subspace. -/
lemma integralPart_exterior_section (X : Submodule K (K ⊗[𝓞 K] M)) (r : ℕ)
    (x : ⋀[𝓞 K]^r (integralPart X)) :
    map r X.subtype
        (map (N := X) r (integralPartGenericEquiv X).toLinearMap
          (exteriorPower.baseChangeEquiv (𝓞 K) (integralPart X) K r (1 ⊗ₜ[𝓞 K] x))) =
      exteriorPower.baseChangeEquiv (𝓞 K) M K r
        (1 ⊗ₜ[𝓞 K] map r (integralPart X).subtype x) := by
  let F : (⋀[𝓞 K]^r (integralPart X)) →ₗ[𝓞 K] (⋀[K]^r (K ⊗[𝓞 K] M)) :=
    ((map r X.subtype).comp
      (map (N := X) r (integralPartGenericEquiv X).toLinearMap)).restrictScalars (𝓞 K) ∘ₗ
      (exteriorPower.baseChangeEquiv (𝓞 K) (integralPart X) K r).toLinearMap.restrictScalars
        (𝓞 K) ∘ₗ
      TensorProduct.mk (𝓞 K) K _ 1
  let G : (⋀[𝓞 K]^r (integralPart X)) →ₗ[𝓞 K] (⋀[K]^r (K ⊗[𝓞 K] M)) :=
    ((exteriorPower.baseChangeEquiv (𝓞 K) M K r).toLinearMap.restrictScalars (𝓞 K)).comp
      ((TensorProduct.mk (𝓞 K) K _ 1).comp (map r (integralPart X).subtype))
  have he : F = G := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change map r X.subtype (map (N := X) r (integralPartGenericEquiv X).toLinearMap
      (exteriorPower.baseChangeEquiv (𝓞 K) (integralPart X) K r
        (1 ⊗ₜ[𝓞 K] ιMulti (𝓞 K) r v))) =
      exteriorPower.baseChangeEquiv (𝓞 K) M K r
        (1 ⊗ₜ[𝓞 K] map r (integralPart X).subtype (ιMulti (𝓞 K) r v))
    rw [map_apply_ιMulti, exteriorPower.baseChangeEquiv_apply_tmul,
      exteriorPower.baseChangeEquiv_apply_tmul, map_apply_ιMulti, map_apply_ιMulti]
    congr 1
  exact LinearMap.congr_fun he x

omit [NumberField K] in
/-- A common nonzero exterior vector recovers two generic subspaces of the
same finite dimension. -/
theorem eq_of_mem_exterior_ranges {V : Type*} [AddCommGroup V] [Module K V]
    (U W : Submodule K V) [Module.Finite K U] [Module.Finite K W]
    {r : ℕ} (hU : finrank K U = r) (hW : finrank K W = r)
    {ξ : ⋀[K]^r V} (hξ : ξ ≠ 0)
    (hξU : ξ ∈ (map r U.subtype).range) (hξW : ξ ∈ (map r W.subtype).range) : U = W := by
  obtain ⟨η, hη⟩ := hξU
  obtain ⟨ζ, hζ⟩ := hξW
  have hη0 : η ≠ 0 := fun he => hξ (by simpa [he] using hη.symm)
  have hζ0 : ζ ≠ 0 := fun he => hξ (by simpa [he] using hζ.symm)
  exact eq_of_plucker_eq U W (finBasisOfFinrankEq K U hU) (finBasisOfFinrankEq K W hW)
    η ζ hη0 hζ0 (hη.trans hζ.symm)

end BostConjecture.Arithmetic
