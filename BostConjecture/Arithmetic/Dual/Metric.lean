/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Dual.Fiber
public import BostConjecture.Tensor.Dual.Metric
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-!
# The intrinsic dual Hermitian metric

The operator dual metric is transported to the actual complex fiber of the
integral dual. Riesz uniqueness and the canonical evaluation formula prove
conjugation compatibility. No integral freeness assumption is used.
-/

@[expose] public section

noncomputable section

open scoped BostConjecture.Tensor

open NumberField Module

namespace BostConjecture.Arithmetic.HermitianMetric

variable {K : Type*} [Field K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]
    [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]

/-- Riesz representation of the actual fiber of the integral dual. -/
def dualRiesz (h : HermitianMetric K M) (σ : K →+* ℂ) :
    ComplexFiber (Dual (𝓞 K) M) σ ≃ₗ⋆[ℂ] ComplexFiber M σ := by
  letI : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  letI := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
  letI := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
  exact (dualFiberEquiv M σ).trans (Tensor.dualRieszEquiv (ComplexFiber M σ))

@[simp]
lemma dualRiesz_inner (h : HermitianMetric K M) (σ : K →+* ℂ)
    (f : ComplexFiber (Dual (𝓞 K) M) σ) (x : ComplexFiber M σ) :
    (h.fiber σ).inner (h.dualRiesz σ f) x = dualFiberEquiv M σ f x := by
  let : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
  let := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
  exact Tensor.dualRieszEquiv_inner _ _ _

/-- Canonical fiber conjugation commutes with Riesz representation. -/
lemma dualRiesz_conjugate (h : HermitianMetric K M) (σ : K →+* ℂ)
    (f : ComplexFiber (Dual (𝓞 K) M) σ) :
    fiberConjugate M σ (h.dualRiesz σ f) =
      h.dualRiesz (ComplexEmbedding.conjugate σ) (fiberConjugate (Dual (𝓞 K) M) σ f) := by
  let : InnerProductSpace.Core ℂ (ComplexFiber M (ComplexEmbedding.conjugate σ)) :=
    h.fiber (ComplexEmbedding.conjugate σ)
  let := InnerProductSpace.Core.toNormedAddCommGroup
    (𝕜 := ℂ) (F := ComplexFiber M (ComplexEmbedding.conjugate σ))
  let := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ
    (ComplexFiber M (ComplexEmbedding.conjugate σ)))
  apply ext_inner_right ℂ
  intro x
  obtain ⟨y, rfl⟩ := (fiberConjugate M σ).surjective x
  change (h.fiber (ComplexEmbedding.conjugate σ)).inner _ _ =
    (h.fiber (ComplexEmbedding.conjugate σ)).inner _ _
  rw [h.inner_conjugate, h.dualRiesz_inner, h.dualRiesz_inner,
    dualFiberEquiv_conjugate]

/-- The canonical dual form transported through the finite-projective base change. -/
@[instance_reducible]
def dualFiber (h : HermitianMetric K M) (σ : K →+* ℂ) :
    InnerProductSpace.Core ℂ (ComplexFiber (Dual (𝓞 K) M) σ) := by
  letI : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  letI := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
  letI := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
  exact
    { inner := fun f g => (Tensor.dualCore (ComplexFiber M σ)).inner
        (dualFiberEquiv M σ f) (dualFiberEquiv M σ g)
      conj_inner_symm := fun _ _ => (Tensor.dualCore _).conj_inner_symm _ _
      re_inner_nonneg := fun _ => (Tensor.dualCore _).re_inner_nonneg _
      add_left := by intros; simp only [map_add, InnerProductSpace.Core.inner_add_left]
      smul_left := by intros; simp only [map_smul, InnerProductSpace.Core.inner_smul_left]
      definite := by
        intro f hf
        apply (dualFiberEquiv M σ).injective
        simpa only [map_zero] using (Tensor.dualCore _).definite _ hf }

lemma dualFiber_inner (h : HermitianMetric K M) (σ : K →+* ℂ)
    (f g : ComplexFiber (Dual (𝓞 K) M) σ) :
    (h.dualFiber σ).inner f g = (h.fiber σ).inner (h.dualRiesz σ g) (h.dualRiesz σ f) := rfl

/-- The operator dual metric on the actual integral dual module. -/
def dual (h : HermitianMetric K M) : HermitianMetric K (Dual (𝓞 K) M) where
  fiber := h.dualFiber
  conjugate := by
    intro σ f g
    simp only [dualFiber_inner, ← fiberConjugate_section (Dual (𝓞 K) M) σ,
      ← h.dualRiesz_conjugate, h.inner_conjugate]

/-- The transported fiber norm equals the complex operator norm. -/
lemma dualFiber_norm (h : HermitianMetric K M) (σ : K →+* ℂ)
    (f : ComplexFiber (Dual (𝓞 K) M) σ) :
    letI : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
    letI := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
    letI := InnerProductSpace.ofCore
      (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
    Real.sqrt (((h.dual.fiber σ).inner f f).re) =
      ‖(dualFiberEquiv M σ f).toContinuousLinearMap‖ := by
  let : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
  let := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
  exact Tensor.dualCore_norm _ _

/-- Evaluation is bounded on every complex fiber vector. -/
lemma dual_evaluation_le (h : HermitianMetric K M) (σ : K →+* ℂ)
    (f : ComplexFiber (Dual (𝓞 K) M) σ) (x : ComplexFiber M σ) :
    ‖dualFiberEquiv M σ f x‖ ≤
      Real.sqrt (((h.dual.fiber σ).inner f f).re) *
        Real.sqrt (((h.fiber σ).inner x x).re) := by
  let : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
  let := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
  exact Tensor.dualCore_evaluation_le _ _ _

/-- The intrinsic dual metric bounds every integral evaluation at every embedding. -/
lemma dual_section_evaluation_le (h : HermitianMetric K M) (σ : K →+* ℂ)
    (f : Dual (𝓞 K) M) (x : M) :
    ‖σ (f x)‖ ≤ h.dual.sectionNorm σ f * h.sectionNorm σ x := by
  simpa only [dualFiberEquiv_section, sectionNorm] using
    h.dual_evaluation_le σ (fiberSection _ σ f) (fiberSection _ σ x)

end BostConjecture.Arithmetic.HermitianMetric
