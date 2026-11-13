/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.InvariantTheory.Binary.TensorTransport

/-!
# Completed norms under the Bool tensor convention

The finite-family geometric quotient criterion and the ordinary binary tensor
quotient use the same completed norms under the prescribed tensor equivalence.
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry

noncomputable section

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E F : Type*} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]

omit [FiniteDimensional K E] [FiniteDimensional K F] in
private theorem boolTensorEquiv_reindex_binary :
    (boolTensorPairEquiv K E F).toLinearMap.comp
      (PiTensorProduct.reindex K (LiftedTensorFactors E F)
        boolEquivUnitSumUnit.symm).toLinearMap =
    (tensorPairEquiv K E F).toLinearMap := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  change boolTensorPairEquiv K E F
    (PiTensorProduct.reindex K (LiftedTensorFactors E F) boolEquivUnitSumUnit.symm
      (⨂ₜ[K] i, x i)) = tensorPairEquiv K E F (⨂ₜ[K] i, x i)
  simp [PiTensorProduct.reindex_tprod, boolTensorPairEquiv, tensorPairEquiv,
    boolTensorEquiv_tprod, binaryTensorEquiv_tprod]
  rfl

namespace NormFamily

/-- The prescribed Bool-to-binary equivalence preserves every completed
orthogonal tensor norm. -/
theorem orthogonalTensor_norm_boolTensorEquiv
    (ξ : NormFamily S E) (η : NormFamily S F)
    [hN : S.IsArchimedeanNormalized]
    [hξ : ξ.IsHermitian] [hη : η.IsHermitian]
    (ω : S.Ω) (z : (S.ϕ ω).Completion ⊗[K] (⨂[K] i, LiftedBoolTensorFactors E F i)) :
    (ξ ⊗ʰ η).norm ω
      ((boolTensorPairEquiv K E F).toLinearMap.baseChange
        (S.ϕ ω).Completion z) =
    (orthogonalTensor (fun i ↦ tensorPairFactors ξ η (boolEquivUnitSumUnit i))).norm ω z := by
  let r := PiTensorProduct.reindex K (LiftedTensorFactors E F) boolEquivUnitSumUnit.symm
  obtain ⟨x, rfl⟩ := (r.baseChange K (S.ϕ ω).Completion _ _).surjective z
  have h := congrArg (fun f ↦ f.baseChange (S.ϕ ω).Completion x)
    (boolTensorEquiv_reindex_binary (K := K) (E := E) (F := F))
  simp only [LinearMap.baseChange_comp, LinearMap.comp_apply] at h
  change (ξ ⊗ʰ η).norm ω
    ((boolTensorPairEquiv K E F).toLinearMap.baseChange
      (S.ϕ ω).Completion (r.toLinearMap.baseChange (S.ϕ ω).Completion x)) = _
  rw [h]
  refine Eq.trans ?_ (orthogonalTensor_norm_reindex (tensorPairFactors ξ η)
     boolEquivUnitSumUnit.symm ω x).symm
  change (orthogonalTensor (tensorPairFactors ξ η)).norm ω
    ((tensorPairEquiv K E F).symm.toLinearMap.baseChange
      (S.ϕ ω).Completion
      ((tensorPairEquiv K E F).toLinearMap.baseChange
        (S.ϕ ω).Completion x)) = _
  congr 1
  exact (LinearEquiv.baseChange K (S.ϕ ω).Completion _ _
    (tensorPairEquiv K E F)).symm_apply_apply x

end NormFamily

end

end ArakelovGeometry
