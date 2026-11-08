/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.RestrictionCovolume.TraceSpace

/-!
# Conjugation and place weights in the real trace metric

Every vector in the actual real scalar extension has conjugate components
at conjugate embeddings. The given Hermitian compatibility therefore turns
the all-embeddings trace norm into the weighted infinite-place norm, with
weight one at real places and weight two at complex places.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace BostConjecture.Arithmetic.HermitianMetric

variable {K : Type*} [Field K] [NumberField K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]
variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
variable (h : HermitianMetric K M)

/-- All real trace-space vectors have the actual conjugate fiber components. -/
theorem traceInclusion_conjugate (x : h.TraceSpace) (σ : K →+* ℂ) :
    fiberConjugate M σ (h.traceInclusion x σ) =
      h.traceInclusion x (ComplexEmbedding.conjugate σ) := by
  obtain ⟨z, rfl⟩ := h.realTensorEquiv.surjective x
  induction z using TensorProduct.inductionOn with
  | tmul r m =>
    simp only [realTensorEquiv_tmul, map_smul, Pi.smul_apply, traceInclusion_section]
    change fiberConjugate M σ ((r : ℂ) • fiberSection M σ m) =
      (r : ℂ) • fiberSection M (ComplexEmbedding.conjugate σ) m
    rw [map_smulₛₗ, fiberConjugate_section]
    simp
  | add x y hx hy =>
    simp only [map_add, Pi.add_apply, hx, hy]

end BostConjecture.Arithmetic.HermitianMetric
