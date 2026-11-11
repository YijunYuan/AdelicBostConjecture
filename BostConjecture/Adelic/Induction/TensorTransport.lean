/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Adelic.Contraction.PairingBaseChange
public import ArakelovGeometry.AdelicVectorBundle.Subquotient.EquivalencePullback

/-!
# Tensor isometries across carrier universes

The tensor of two completed isometries is an isometry for the actual
Hilbert/epsilon norms. Source and target carriers may lie in different
universes. This permits finite-dimensional coordinate transport without
changing the original scalar field.

The analytic input is the existing completed finite-tensor contraction in
`Contraction.PairingBaseChange`; the binary identification is checked on
pure tensors, and the reverse inequality uses the inverse equivalences.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace ArakelovGeometry.NormFamily

universe u v w w'

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E F : Type w} {G H : Type w'}
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]
  [AddCommGroup G] [Module K G] [FiniteDimensional K G]
  [AddCommGroup H] [Module K H] [FiniteDimensional K H]

private theorem tensorPair_map_bound
    (ξ : NormFamily S E) (η : NormFamily S F) (ζ : NormFamily S G) (θ : NormFamily S H)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hξ : ξ.IsHermitian hN) (hη : η.IsHermitian hN)
    (hζ : ζ.IsHermitian hN) (hθ : θ.IsHermitian hN)
    (f : E →ₗ[K] G) (g : F →ₗ[K] H) (ω : S.Ω)
    (hf : ∀ x, ζ.norm ω (f.baseChange (S.ϕ ω).Completion x) = ξ.norm ω x)
    (hg : ∀ y, θ.norm ω (g.baseChange (S.ϕ ω).Completion y) = η.norm ω y)
    (z : (S.ϕ ω).Completion ⊗[K] (E ⊗[K] F)) :
    (ζ.orthogonalTensorPair θ hN hζ hθ).norm ω
        ((TensorProduct.map f g).baseChange (S.ϕ ω).Completion z) ≤
      (ξ.orthogonalTensorPair η hN hξ hη).norm ω z := by
  let ff : ∀ i, BinaryTensorFactors E F i →ₗ[K] BinaryTensorFactors G H i :=
    fun i ↦ match i with | .inl _ => f | .inr _ => g
  let a := binaryTensorEquiv K (BinaryTensorFactors E F)
  let b := binaryTensorEquiv K (BinaryTensorFactors G H)
  have hc : b.symm.toLinearMap.comp (TensorProduct.map f g) =
      (PiTensorProduct.map ff).comp a.symm.toLinearMap := by
    apply LinearMap.ext
    intro z
    obtain ⟨x, rfl⟩ := a.surjective z
    apply b.injective
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
      LinearEquiv.symm_apply_apply]
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r x => simp [a, b, ff, binaryTensorEquiv_tprod]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hz := DFunLike.congr_fun
    (congrArg (fun q ↦ q.baseChange (S.ϕ ω).Completion) hc) z
  simp only [LinearMap.baseChange_comp, LinearMap.comp_apply] at hz
  change (orthogonalTensor (tensorPairFactors ζ θ) hN (hζ.tensorPairFactors hθ)).norm ω
      (b.symm.toLinearMap.baseChange _ ((TensorProduct.map f g).baseChange _ z)) ≤
    (orthogonalTensor (tensorPairFactors ξ η) hN (hξ.tensorPairFactors hη)).norm ω
      (a.symm.toLinearMap.baseChange _ z)
  rw [hz]
  apply BostConjecture.Adelic.Contraction.orthogonalTensor_map_norm_le_of_finite_le_infinite_eq
    (tensorPairFactors ξ η) (tensorPairFactors ζ θ) hN
    (hξ.tensorPairFactors hη) (hζ.tensorPairFactors hθ) ff ω
  · rintro (i | i) x
    · exact (hf x).le
    · exact (hg x).le
  · intro _
    rintro (i | i) x
    · exact hf x
    · exact hg x

/-- Tensoring completed isometric linear equivalences preserves the full actual
orthogonal tensor norms, with independent source and target carrier universes. -/
theorem orthogonalTensorPair_norm_congr
    (ξ : NormFamily S E) (η : NormFamily S F) (ζ : NormFamily S G) (θ : NormFamily S H)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hξ : ξ.IsHermitian hN) (hη : η.IsHermitian hN)
    (hζ : ζ.IsHermitian hN) (hθ : θ.IsHermitian hN)
    (e : E ≃ₗ[K] G) (f : F ≃ₗ[K] H) (ω : S.Ω)
    (he : ∀ x, ζ.norm ω (e.toLinearMap.baseChange (S.ϕ ω).Completion x) = ξ.norm ω x)
    (hf : ∀ y, θ.norm ω (f.toLinearMap.baseChange (S.ϕ ω).Completion y) = η.norm ω y)
    (z : (S.ϕ ω).Completion ⊗[K] (E ⊗[K] F)) :
    (ζ.orthogonalTensorPair θ hN hζ hθ).norm ω
        ((TensorProduct.congr e f).toLinearMap.baseChange (S.ϕ ω).Completion z) =
      (ξ.orthogonalTensorPair η hN hξ hη).norm ω z := by
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
  apply le_antisymm (tensorPair_map_bound ξ η ζ θ hN hξ hη hζ hθ
    e.toLinearMap f.toLinearMap ω he hf z)
  let t := (TensorProduct.congr e f).baseChange K (S.ϕ ω).Completion _ _
  have h := tensorPair_map_bound ζ θ ξ η hN hζ hθ hξ hη
    e.symm.toLinearMap f.symm.toLinearMap ω he' hf' (t z)
  change (ξ.orthogonalTensorPair η hN hξ hη).norm ω (t.symm (t z)) ≤ _ at h
  rw [LinearEquiv.symm_apply_apply] at h
  exact h

end ArakelovGeometry.NormFamily
