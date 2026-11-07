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

/-- Hermitian compatibility holds on all components of the real trace space. -/
lemma traceInclusion_inner_conjugate (x y : h.TraceSpace) (σ : K →+* ℂ) :
    (h.fiber (ComplexEmbedding.conjugate σ)).inner
        (h.traceInclusion x (ComplexEmbedding.conjugate σ))
        (h.traceInclusion y (ComplexEmbedding.conjugate σ)) =
      star ((h.fiber σ).inner (h.traceInclusion x σ) (h.traceInclusion y σ)) := by
  rw [← h.traceInclusion_conjugate, ← h.traceInclusion_conjugate, h.inner_conjugate]

/-- Real parts of the pairings depend only on the infinite place. -/
lemma traceInclusion_inner_re_eq_of_place_eq (x y : h.TraceSpace)
    {σ τ : K →+* ℂ} (heq : InfinitePlace.mk σ = InfinitePlace.mk τ) :
    ((h.fiber σ).inner (h.traceInclusion x σ) (h.traceInclusion y σ)).re =
      ((h.fiber τ).inner (h.traceInclusion x τ) (h.traceInclusion y τ)).re := by
  rcases InfinitePlace.mk_eq_iff.mp heq with heq | heq
  · rw [heq]
  · rw [← heq, h.traceInclusion_inner_conjugate]
    rfl

/-- The all-embeddings trace pairing equals the place-weighted real pairing. -/
theorem trace_inner_eq_sum_places (x y : h.TraceSpace) :
    inner ℝ x y = ∑ v : InfinitePlace K, (v.mult : ℝ) *
      ((h.fiber v.embedding).inner
        (h.traceInclusion x v.embedding) (h.traceInclusion y v.embedding)).re := by
  classical
  change (∑ σ : K →+* ℂ, ((h.fiber σ).inner
    (h.traceInclusion x σ) (h.traceInclusion y σ)).re) = _
  rw [← Finset.univ.sum_fiberwise (fun σ : K →+* ℂ => InfinitePlace.mk σ)]
  apply Finset.sum_congr rfl
  intro v _
  have hc (σ : K →+* ℂ)
      (hσ : σ ∈ Finset.univ.filter (fun σ => InfinitePlace.mk σ = v)) :
      ((h.fiber σ).inner (h.traceInclusion x σ) (h.traceInclusion y σ)).re =
        ((h.fiber v.embedding).inner
          (h.traceInclusion x v.embedding) (h.traceInclusion y v.embedding)).re := by
    apply h.traceInclusion_inner_re_eq_of_place_eq
    rw [(Finset.mem_filter.mp hσ).2, InfinitePlace.mk_embedding]
  rw [Finset.sum_congr rfl hc, Finset.sum_const, InfinitePlace.card_filter_mk_eq,
    nsmul_eq_mul]

/-- The squared trace norm has real-place weight one and complex-place weight two. -/
theorem trace_norm_sq_eq_sum_places (x : h.TraceSpace) :
    ‖x‖ ^ 2 = ∑ v : InfinitePlace K, (v.mult : ℝ) *
      (Real.sqrt ((h.fiber v.embedding).inner
        (h.traceInclusion x v.embedding) (h.traceInclusion x v.embedding)).re) ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℝ)]
  change inner ℝ x x = _
  rw [h.trace_inner_eq_sum_places]
  apply Finset.sum_congr rfl
  intro v _
  congr 1
  exact (Real.sq_sqrt ((h.fiber v.embedding).re_inner_nonneg _)).symm

end BostConjecture.Arithmetic.HermitianMetric
