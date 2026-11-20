/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Tensor.PairMap
public import ArakelovGeometry.AdelicVectorBundle.Subquotient.EquivalencePullback

/-!
# Tensor isometries across carrier universes

The tensor of two completed isometries is an isometry for the actual
Hilbert/epsilon norms. Source and target carriers may lie in different
universes. This permits finite-dimensional coordinate transport without
changing the original scalar field.

The analytic input is AG's completed binary tensor contraction across carrier
universes; the reverse inequality uses the inverse equivalences.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace ArakelovGeometry.NormFamily

universe u v w w'

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E F G H : Type*}
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]
  [AddCommGroup G] [Module K G] [FiniteDimensional K G]
  [AddCommGroup H] [Module K H] [FiniteDimensional K H]

/-- Tensoring completed isometric linear equivalences preserves the full actual
orthogonal tensor norms, with independent source and target carrier universes. -/
theorem orthogonalTensorPair_norm_congr
    (ξ : NormFamily S E) (η : NormFamily S F) (ζ : NormFamily S G) (θ : NormFamily S H)
    [hN : S.IsArchimedeanNormalized]
    [hξ : ξ.IsHermitian] [hη : η.IsHermitian]
    [hζ : ζ.IsHermitian] [hθ : θ.IsHermitian]
    (e : E ≃ₗ[K] G) (f : F ≃ₗ[K] H) (ω : S.Ω)
    (he : ∀ x, ζ.norm ω (e.toLinearMap.baseChange (S.ϕ ω).Completion x) = ξ.norm ω x)
    (hf : ∀ y, θ.norm ω (f.toLinearMap.baseChange (S.ϕ ω).Completion y) = η.norm ω y)
    (z : (S.ϕ ω).Completion ⊗[K] (E ⊗[K] F)) :
    (ζ ⊗ʰ θ).norm ω
        ((TensorProduct.congr e f).toLinearMap.baseChange (S.ϕ ω).Completion z) =
      (ξ ⊗ʰ η).norm ω z := by
  let eω := e.baseChange K (S.ϕ ω).Completion E G
  let fω := f.baseChange K (S.ϕ ω).Completion F H
  have he' (x) : ξ.norm ω (e.symm.toLinearMap.baseChange (S.ϕ ω).Completion x) =
      ζ.norm ω x := by
    change ξ.norm ω (eω.symm x) = ζ.norm ω x
    have h := (he (eω.symm x)).symm
    change ξ.norm ω (eω.symm x) = ζ.norm ω (eω (eω.symm x)) at h
    simpa only [LinearEquiv.apply_symm_apply] using h
  have hf' (y) : η.norm ω (f.symm.toLinearMap.baseChange (S.ϕ ω).Completion y) =
      θ.norm ω y := by
    change η.norm ω (fω.symm y) = θ.norm ω y
    have h := (hf (fω.symm y)).symm
    change η.norm ω (fω.symm y) = θ.norm ω (fω (fω.symm y)) at h
    simpa only [LinearEquiv.apply_symm_apply] using h
  apply le_antisymm (orthogonalTensorPair_map_norm_le_of_norm_eq ξ η ζ θ
    e.toLinearMap f.toLinearMap ω he hf z)
  let t := (TensorProduct.congr e f).baseChange K (S.ϕ ω).Completion _ _
  have h := orthogonalTensorPair_map_norm_le_of_norm_eq ζ θ ξ η
    e.symm.toLinearMap f.symm.toLinearMap ω he' hf' (t z)
  change (ξ ⊗ʰ η).norm ω (t.symm (t z)) ≤ _ at h
  rw [LinearEquiv.symm_apply_apply] at h
  exact h

end ArakelovGeometry.NormFamily
