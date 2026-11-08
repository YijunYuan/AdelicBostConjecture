/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Main.TensorSemistability.ProjectionConjugation
public import BostConjecture.Main.TensorSemistability.TensorVariation

/-!
# Concrete arithmetic tensor subspaces and their partial traces

The range is that of the actual scalar-extension injection, transported by
canonical binary scalar extension. All projections use the given Hilbert metric.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace BostConjecture.Arithmetic

universe u
variable {K : Type*} [Field K] [NumberField K]
variable {M N : Type u} [AddCommGroup M] [Module (𝓞 K) M]
    [AddCommGroup N] [Module (𝓞 K) N]

/-- The actual tensor-submodule fiber in the binary complex tensor product. -/
def tensorSubmoduleFiber (P : Submodule (𝓞 K) (M ⊗[𝓞 K] N)) (σ : K →+* ℂ) :
    Submodule ℂ (ComplexFiber M σ ⊗[ℂ] ComplexFiber N σ) :=
  ((binaryTensorFiberEquiv σ).toLinearMap.comp (fiberMap P.subtype σ)).range

/-- The concrete complex subspace has the actual integral generic rank. -/
theorem finrank_tensorSubmoduleFiber (P : Submodule (𝓞 K) (M ⊗[𝓞 K] N))
    (σ : K →+* ℂ) : Module.finrank ℂ (tensorSubmoduleFiber P σ) =
      Module.finrank K (K ⊗[𝓞 K] P) := by
  let e := LinearEquiv.ofInjective
    ((binaryTensorFiberEquiv σ).toLinearMap.comp (fiberMap P.subtype σ))
    ((binaryTensorFiberEquiv σ).injective.comp (fiberMap_injective P.subtype P.injective_subtype σ))
  exact e.finrank_eq.symm.trans (complexFiber_finrank P σ)

omit [NumberField K] in
/-- Canonical tensor conjugation carries the actual submodule fiber onto its conjugate. -/
theorem mem_tensorSubmoduleFiber_conjugate
    (P : Submodule (𝓞 K) (M ⊗[𝓞 K] N)) (σ : K →+* ℂ)
    (z : ComplexFiber M σ ⊗[ℂ] ComplexFiber N σ) :
    TensorProduct.congr (fiberConjugate M σ) (fiberConjugate N σ) z ∈
      tensorSubmoduleFiber P (ComplexEmbedding.conjugate σ) ↔ z ∈ tensorSubmoduleFiber P σ := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := (fiberConjugate P σ).surjective y
    refine ⟨x, (TensorProduct.congr (fiberConjugate M σ) (fiberConjugate N σ)).injective ?_⟩
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, ← fiberConjugate_map,
      binaryTensorFiberEquiv_conjugate] using hy
  · rintro ⟨x, rfl⟩
    refine ⟨fiberConjugate P σ x, ?_⟩
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, ← fiberConjugate_map,
      binaryTensorFiberEquiv_conjugate]

namespace HermitianMetric

variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
    [Module.Finite (𝓞 K) N] [Module.Projective (𝓞 K) N]


/-- The orthogonal projection onto the concrete arithmetic tensor subspace. -/
def tensorSubmoduleProjection (h : HermitianMetric K M)
    (k : HermitianMetric K N) (P : Submodule (𝓞 K) (M ⊗[𝓞 K] N))
    (σ : K →+* ℂ) : Module.End ℂ (ComplexFiber M σ ⊗[ℂ] ComplexFiber N σ) := by
  let (σ : K →+* ℂ) : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  let (σ : K →+* ℂ) := InnerProductSpace.Core.toNormedAddCommGroup
    (𝕜 := ℂ) (F := ComplexFiber M σ)
  let (σ : K →+* ℂ) := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
  let (σ : K →+* ℂ) : InnerProductSpace.Core ℂ (ComplexFiber N σ) := k.fiber σ
  let (σ : K →+* ℂ) := InnerProductSpace.Core.toNormedAddCommGroup
    (𝕜 := ℂ) (F := ComplexFiber N σ)
  let (σ : K →+* ℂ) := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber N σ))
  exact (tensorSubmoduleFiber P σ).starProjection.toLinearMap

/-- Right partial trace of the actual tensor-submodule projection. -/
def tensorPartialTraceRight (h : HermitianMetric K M)
    (k : HermitianMetric K N) (P : Submodule (𝓞 K) (M ⊗[𝓞 K] N))
    (σ : K →+* ℂ) : Module.End ℂ (ComplexFiber M σ) :=
  Balanced.partialTraceRight ℂ (ComplexFiber M σ) (ComplexFiber N σ)
    (h.tensorSubmoduleProjection k P σ)

/-- Left partial trace of the actual tensor-submodule projection. -/
def tensorPartialTraceLeft (h : HermitianMetric K M)
    (k : HermitianMetric K N) (P : Submodule (𝓞 K) (M ⊗[𝓞 K] N))
    (σ : K →+* ℂ) : Module.End ℂ (ComplexFiber N σ) :=
  Balanced.partialTraceLeft ℂ (ComplexFiber M σ) (ComplexFiber N σ)
    (h.tensorSubmoduleProjection k P σ)

omit [NumberField K] [Module.Projective (𝓞 K) M] [Module.Projective (𝓞 K) N] in
/-- Canonical conjugation intertwines the actual orthogonal tensor projections. -/
theorem tensorSubmoduleProjection_conjugate (h : HermitianMetric K M)
    (k : HermitianMetric K N) (P : Submodule (𝓞 K) (M ⊗[𝓞 K] N))
    (σ : K →+* ℂ) (z : ComplexFiber M σ ⊗[ℂ] ComplexFiber N σ) :
    h.tensorSubmoduleProjection k P (ComplexEmbedding.conjugate σ)
      (TensorProduct.congr (fiberConjugate M σ) (fiberConjugate N σ) z) =
      TensorProduct.congr (fiberConjugate M σ) (fiberConjugate N σ)
        (h.tensorSubmoduleProjection k P σ z) := by
  let (σ : K →+* ℂ) : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  let (σ : K →+* ℂ) := InnerProductSpace.Core.toNormedAddCommGroup
    (𝕜 := ℂ) (F := ComplexFiber M σ)
  let (σ : K →+* ℂ) := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
  let (σ : K →+* ℂ) : InnerProductSpace.Core ℂ (ComplexFiber N σ) := k.fiber σ
  let (σ : K →+* ℂ) := InnerProductSpace.Core.toNormedAddCommGroup
    (𝕜 := ℂ) (F := ComplexFiber N σ)
  let (σ : K →+* ℂ) := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber N σ))
  exact Balanced.starProjection_conjugate
    (TensorProduct.congr (fiberConjugate M σ) (fiberConjugate N σ))
    (Balanced.inner_tensor_conjugate _ _ (h.inner_conjugate σ) (k.inner_conjugate σ))
    _ _ (mem_tensorSubmoduleFiber_conjugate P σ) z

/-- Right partial traces form a conjugation-compatible arithmetic family. -/
theorem tensorPartialTraceRight_conjugate (h : HermitianMetric K M)
    (k : HermitianMetric K N) (P : Submodule (𝓞 K) (M ⊗[𝓞 K] N))
    (σ : K →+* ℂ) (x : ComplexFiber M σ) :
    h.tensorPartialTraceRight k P (ComplexEmbedding.conjugate σ) (fiberConjugate M σ x) =
      fiberConjugate M σ (h.tensorPartialTraceRight k P σ x) := by
  let (σ : K →+* ℂ) : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  let (σ : K →+* ℂ) := InnerProductSpace.Core.toNormedAddCommGroup
    (𝕜 := ℂ) (F := ComplexFiber M σ)
  let (σ : K →+* ℂ) := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
  let (σ : K →+* ℂ) : InnerProductSpace.Core ℂ (ComplexFiber N σ) := k.fiber σ
  let (σ : K →+* ℂ) := InnerProductSpace.Core.toNormedAddCommGroup
    (𝕜 := ℂ) (F := ComplexFiber N σ)
  let (σ : K →+* ℂ) := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber N σ))
  exact Balanced.partialTraceRight_conjugate _ _ (h.inner_conjugate σ) (k.inner_conjugate σ)
    _ _ (h.tensorSubmoduleProjection_conjugate k P σ) x

/-- Left partial traces form a conjugation-compatible arithmetic family. -/
theorem tensorPartialTraceLeft_conjugate (h : HermitianMetric K M)
    (k : HermitianMetric K N) (P : Submodule (𝓞 K) (M ⊗[𝓞 K] N))
    (σ : K →+* ℂ) (x : ComplexFiber N σ) :
    h.tensorPartialTraceLeft k P (ComplexEmbedding.conjugate σ) (fiberConjugate N σ x) =
      fiberConjugate N σ (h.tensorPartialTraceLeft k P σ x) := by
  let (σ : K →+* ℂ) : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  let (σ : K →+* ℂ) := InnerProductSpace.Core.toNormedAddCommGroup
    (𝕜 := ℂ) (F := ComplexFiber M σ)
  let (σ : K →+* ℂ) := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
  let (σ : K →+* ℂ) : InnerProductSpace.Core ℂ (ComplexFiber N σ) := k.fiber σ
  let (σ : K →+* ℂ) := InnerProductSpace.Core.toNormedAddCommGroup
    (𝕜 := ℂ) (F := ComplexFiber N σ)
  let (σ : K →+* ℂ) := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber N σ))
  exact Balanced.partialTraceLeft_conjugate _ _ (h.inner_conjugate σ) (k.inner_conjugate σ)
    _ _ (h.tensorSubmoduleProjection_conjugate k P σ) x

omit [Module.Projective (𝓞 K) M] [Module.Projective (𝓞 K) N] in
/-- The arithmetic projection trace is the trace on the canonical binary fiber. -/
theorem fiberProjectionTrace_tensor_transport (h : HermitianMetric K M)
    (k : HermitianMetric K N) (P : Submodule (𝓞 K) (M ⊗[𝓞 K] N))
    (σ : K →+* ℂ) (C : Module.End ℂ (ComplexFiber M σ ⊗[ℂ] ComplexFiber N σ)) :
    (h ⊗[𝓞 K] k).fiberProjectionTrace P σ
      ((binaryTensorFiberEquiv σ).symm.toLinearMap.comp
        (C.comp (binaryTensorFiberEquiv σ).toLinearMap)) =
      (LinearMap.trace ℂ (ComplexFiber M σ ⊗[ℂ] ComplexFiber N σ)
        ((h.tensorSubmoduleProjection k P σ).comp C)).re := by
  let (σ : K →+* ℂ) : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  let (σ : K →+* ℂ) := InnerProductSpace.Core.toNormedAddCommGroup
    (𝕜 := ℂ) (F := ComplexFiber M σ)
  let (σ : K →+* ℂ) := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
  let (σ : K →+* ℂ) : InnerProductSpace.Core ℂ (ComplexFiber N σ) := k.fiber σ
  let (σ : K →+* ℂ) := InnerProductSpace.Core.toNormedAddCommGroup
    (𝕜 := ℂ) (F := ComplexFiber N σ)
  let (σ : K →+* ℂ) := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber N σ))
  let (σ : K →+* ℂ) : InnerProductSpace.Core ℂ (ComplexFiber (M ⊗[𝓞 K] N) σ) := (h ⊗[𝓞 K] k).fiber σ
  let (σ : K →+* ℂ) := InnerProductSpace.Core.toNormedAddCommGroup
    (𝕜 := ℂ) (F := ComplexFiber (M ⊗[𝓞 K] N) σ)
  let (σ : K →+* ℂ) := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber (M ⊗[𝓞 K] N) σ))
  let e : ComplexFiber (M ⊗[𝓞 K] N) σ ≃ₗᵢ[ℂ]
      ComplexFiber M σ ⊗[ℂ] ComplexFiber N σ :=
    (binaryTensorFiberEquiv σ).isometryOfInner (by
      intro x y
      change (Tensor.binaryCore (h.fiber σ) (k.fiber σ)).inner
        (binaryTensorFiberEquiv σ x) (binaryTensorFiberEquiv σ y) =
          ((h ⊗[𝓞 K] k).fiber σ).inner x y
      exact (h.tensor_inner k σ x y).symm)
  let S := (fiberMap P.subtype σ).range
  have hS : S.map e.toLinearEquiv.toLinearMap = tensorSubmoduleFiber P σ := by
    exact LinearMap.range_comp _ _ |>.symm
  have hp (x) : h.tensorSubmoduleProjection k P σ (e x) = e (S.starProjection x) := by
    change (tensorSubmoduleFiber P σ).starProjection (e x) = _
    rw [← hS]
    exact (e.toLinearIsometry.map_starProjection S x).symm
  have hh := LinearMap.trace_conj'
    (S.starProjection.toLinearMap.comp
      (e.symm.toLinearEquiv.toLinearMap.comp (C.comp e.toLinearEquiv.toLinearMap)))
    e.toLinearEquiv
  have ht : e.toLinearEquiv.conj
      (S.starProjection.toLinearMap.comp
        (e.symm.toLinearEquiv.toLinearMap.comp (C.comp e.toLinearEquiv.toLinearMap))) =
      (h.tensorSubmoduleProjection k P σ).comp C := by
    apply LinearMap.ext
    intro x
    change e (S.starProjection (e.symm (C (e (e.symm x))))) = _
    rw [e.apply_symm_apply, ← hp, e.apply_symm_apply]
    rfl
  rw [ht] at hh
  exact congrArg Complex.re hh.symm

end HermitianMetric
end BostConjecture.Arithmetic
