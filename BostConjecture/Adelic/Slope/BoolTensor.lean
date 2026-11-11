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
  {E F : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]

omit [FiniteDimensional K E] [FiniteDimensional K F] in
private theorem boolTensorEquiv_reindex_binary :
    (boolTensorEquiv K (BoolTensorFactors E F)).toLinearMap.comp
      (PiTensorProduct.reindex K (BinaryTensorFactors E F)
        boolEquivUnitSumUnit.symm).toLinearMap =
    (binaryTensorEquiv K (BinaryTensorFactors E F)).toLinearMap := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  change boolTensorEquiv K (BoolTensorFactors E F)
    (PiTensorProduct.reindex K (BinaryTensorFactors E F) boolEquivUnitSumUnit.symm
      (⨂ₜ[K] i, x i)) = binaryTensorEquiv K (BinaryTensorFactors E F) (⨂ₜ[K] i, x i)
  simp only [PiTensorProduct.reindex_tprod, boolTensorEquiv_tprod, binaryTensorEquiv_tprod]
  rfl

namespace NormFamily

/-- The prescribed Bool-to-binary equivalence preserves every completed
orthogonal tensor norm. -/
theorem orthogonalTensor_norm_boolTensorEquiv
    (ξ : NormFamily S E) (η : NormFamily S F)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hξ : ξ.IsHermitian hN) (hη : η.IsHermitian hN)
    (ω : S.Ω) (z : (S.ϕ ω).Completion ⊗[K] (⨂[K] i, BoolTensorFactors E F i)) :
    (ξ.orthogonalTensorPair η hN hξ hη).norm ω
      ((boolTensorEquiv K (BoolTensorFactors E F)).toLinearMap.baseChange
        (S.ϕ ω).Completion z) =
    (orthogonalTensor (fun i ↦ tensorPairFactors ξ η (boolEquivUnitSumUnit i))
      hN (fun i ↦ hξ.tensorPairFactors hη (boolEquivUnitSumUnit i))).norm ω z := by
  let r := PiTensorProduct.reindex K (BinaryTensorFactors E F) boolEquivUnitSumUnit.symm
  obtain ⟨x, rfl⟩ := (r.baseChange K (S.ϕ ω).Completion _ _).surjective z
  have h := congrArg (fun f ↦ f.baseChange (S.ϕ ω).Completion x)
    (boolTensorEquiv_reindex_binary (K := K) (E := E) (F := F))
  simp only [LinearMap.baseChange_comp, LinearMap.comp_apply] at h
  change (ξ.orthogonalTensorPair η hN hξ hη).norm ω
    ((boolTensorEquiv K (BoolTensorFactors E F)).toLinearMap.baseChange
      (S.ϕ ω).Completion (r.toLinearMap.baseChange (S.ϕ ω).Completion x)) = _
  rw [h]
  refine Eq.trans ?_ (orthogonalTensor_norm_reindex (tensorPairFactors ξ η) hN
    (hξ.tensorPairFactors hη) boolEquivUnitSumUnit.symm ω x).symm
  change (orthogonalTensor (tensorPairFactors ξ η) hN (hξ.tensorPairFactors hη)).norm ω
    ((binaryTensorEquiv K (BinaryTensorFactors E F)).symm.toLinearMap.baseChange
      (S.ϕ ω).Completion
      ((binaryTensorEquiv K (BinaryTensorFactors E F)).toLinearMap.baseChange
        (S.ϕ ω).Completion x)) = _
  congr 1
  exact (LinearEquiv.baseChange K (S.ϕ ω).Completion _ _
    (binaryTensorEquiv K (BinaryTensorFactors E F))).symm_apply_apply x

end NormFamily

end

end ArakelovGeometry
