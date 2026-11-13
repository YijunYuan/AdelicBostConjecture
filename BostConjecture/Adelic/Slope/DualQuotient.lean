/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Tensor.Hermitian.Dual.Basic
public import ArakelovGeometry.AdelicVectorBundle.Dual.Map

/-!
# The actual tensor-quotient dual norm

Dualizing the quotient norm gives precisely the induced norm in the orthogonal
tensor product of the dual factors. This is the metric identification used when
passing from Theorem 6.2 of this paper to its quotient formulation (43).
-/

@[expose] public section

open scoped TensorProduct

namespace ArakelovGeometry.NormFamily

universe u v w w'

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {F : Type*} [AddCommGroup F] [Module K F] [FiniteDimensional K F]
  {Q : Type w'} [AddCommGroup Q] [Module K Q] [FiniteDimensional K Q]

/-- The dual of the actual tensor-quotient norm is the induced norm along the
transpose followed by the canonical inverse tensor-duality isomorphism. -/
theorem orthogonalTensorPair_pushforward_dual_norm
    (ξ : NormFamily S E) (η : NormFamily S F)
    [hN : S.IsArchimedeanNormalized]
    [hξ : ξ.IsHermitian] [hη : η.IsHermitian]
    (q : E ⊗[K] F →ₗ[K] Q) (hq : Function.Surjective q)
    (ω : S.Ω) (z : (S.ϕ ω).Completion ⊗[K] Module.Dual K Q) :
    ((ξ ⊗ʰ η).pushforward q hq).dual.norm ω z =
      (ξ.dual ⊗ʰ η.dual).norm ω
        (((TensorProduct.dualDistribEquiv K E F).symm.toLinearMap.comp q.dualMap).baseChange
          (S.ϕ ω).Completion z) := by
  rw [pushforward_dual_norm_eq, ← orthogonalTensorPair_dual_norm ξ η]
  congr 1
  rw [← TensorProduct.toLinearMap_dualDistribEquiv, ← LinearMap.comp_apply,
    ← LinearMap.baseChange_comp]
  congr 2
  ext x : 1
  exact ((TensorProduct.dualDistribEquiv K E F).apply_symm_apply (q.dualMap x)).symm

section FiniteFamily

variable {ι : Type*} [Fintype ι] (A : ι → Type w)
  [∀ i, AddCommGroup (A i)] [∀ i, Module K (A i)] [∀ i, FiniteDimensional K (A i)]

/-- Finite-family version, for the same tensor-dual inclusion as the algebraic
geometric quotient criterion. -/
theorem orthogonalTensor_pushforward_dual_norm
    (ξ : ∀ i, NormFamily S (A i))
    [hN : S.IsArchimedeanNormalized]
    [hξ : ∀ i, (ξ i).IsHermitian]
    (q : (⨂[K] i, A i) →ₗ[K] Q) (hq : Function.Surjective q)
    (ω : S.Ω) (z : (S.ϕ ω).Completion ⊗[K] Module.Dual K Q) :
    ((orthogonalTensor ξ).pushforward q hq).dual.norm ω z =
      (orthogonalTensor (fun i ↦ (ξ i).dual)).norm ω
        (((PiTensorProduct.dualDistribEquiv (R := K) (M := A)).symm.toLinearMap.comp
          q.dualMap).baseChange (S.ϕ ω).Completion z) := by
  rw [pushforward_dual_norm_eq, ← orthogonalTensor_dual_norm ξ]
  congr 1
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
  congr 2
  ext x : 1
  exact ((PiTensorProduct.dualDistribEquiv (R := K) (M := A)).apply_symm_apply
    (q.dualMap x)).symm

end FiniteFamily

end ArakelovGeometry.NormFamily
