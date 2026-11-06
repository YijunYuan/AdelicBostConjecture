/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Tensor.Compatibility
public import BostConjecture.Arithmetic.Tensor.ComplexQuotient

/-!
# Intrinsic quotient tensor metrics

Orthogonal tensor lifts on the complex fibers prove compatibility of the
existing arithmetic tensor metric with the actual quotient metric.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct
open scoped InnerProductSpace

namespace BostConjecture.Arithmetic.HermitianMetric

universe u
variable {K : Type*} [Field K] [NumberField K]
variable {M N P : Type u} [AddCommGroup M] [Module (𝓞 K) M]
    [AddCommGroup N] [Module (𝓞 K) N] [AddCommGroup P] [Module (𝓞 K) P]
    [Module.Finite (𝓞 K) M] [Module.Finite (𝓞 K) N]

/-- The actual quotient metric commutes with right tensoring. -/
lemma tensor_pushforward (h : HermitianMetric (K := K) M)
    (g : HermitianMetric (K := K) N) (f : M →ₗ[𝓞 K] P) (hf : Function.Surjective f) :
    (h.tensor g).pushforward (f.rTensor N) (LinearMap.rTensor_surjective N hf) =
      (h.pushforward f hf).tensor g := by
  apply ext_inner
  intro σ x y
  let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  let : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
  let := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
  let : InnerProductSpace.Core ℂ (ComplexFiber N σ) := g.fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber N σ)
  let := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber N σ))
  let : InnerProductSpace.Core ℂ (ComplexFiber (M ⊗[𝓞 K] N) σ) := (h.tensor g).fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber (M ⊗[𝓞 K] N) σ)
  let := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber (M ⊗[𝓞 K] N) σ))
  let e := binaryTensorFiberEquiv (M := M) (N := N) σ
  let j := binaryTensorFiberEquiv (M := P) (N := N) σ
  let q := fiberMap f σ
  have hn (z : ComplexFiber (P ⊗[𝓞 K] N) σ) :
      e ((h.tensor g).fiberLift (f.rTensor N) (LinearMap.rTensor_surjective N hf) σ z) =
        ComplexQuotient.lift (q.rTensor (ComplexFiber N σ))
          (LinearMap.rTensor_surjective _ (fiberMap_surjective f hf σ)) (j z) := by
    apply ComplexQuotient.lift_natural e.toLinearMap
      (fun u v => (tensor_inner h g σ u v).symm)
      (fiberMap (f.rTensor N) σ) (fiberMap_surjective _ (LinearMap.rTensor_surjective N hf) σ)
      (q.rTensor (ComplexFiber N σ)) (LinearMap.rTensor_surjective _ (fiberMap_surjective f hf σ))
      j.toLinearMap j.injective
    · intro z
      exact (binaryTensorFiberEquiv_rTensor f σ z).symm
    · intro z _
      exact ⟨e.symm z, e.apply_symm_apply z⟩
  change ((h.tensor g).fiber σ).inner
    ((h.tensor g).fiberLift (f.rTensor N) (LinearMap.rTensor_surjective N hf) σ x)
    ((h.tensor g).fiberLift (f.rTensor N) (LinearMap.rTensor_surjective N hf) σ y) = _
  rw [tensor_inner, tensor_inner]
  change inner ℂ (e _) (e _) = _
  rw [hn, hn]
  exact ComplexQuotient.core_rTensor_inner q (fiberMap_surjective f hf σ) (j x) (j y)

end BostConjecture.Arithmetic.HermitianMetric
