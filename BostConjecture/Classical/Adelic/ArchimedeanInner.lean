/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Classical.Adelic.Bundle
public import ArakelovGeometry.Analysis.Hermitian.ComplexPolarization
public import ArakelovGeometry.AdelicVectorBundle.Tensor.Hermitian.InnerProduct

/-! # The original complex pairing and the completed Hermitian pairing -/

@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false

open NumberField TensorProduct
open scoped ComplexConjugate InnerProductSpace
open ArakelovGeometry ArakelovGeometry.AdelicStructure
  ArakelovGeometry.NumberFieldArchimedeanDiagonal

namespace BostConjecture.Arithmetic

attribute [local instance 2000] Algebra.toModule Algebra.toSMul

variable {K : Type*} [Field K] [NumberField K]

/-- The chosen complex embedding of a real completion has real image. -/
theorem classicalCompletionEmbedding_im_of_real {w : InfinitePlace K} (hw : w.IsReal)
    (a : ClassicalCompletion w) : (classicalCompletionEmbedding w a).im = 0 := by
  change (InfinitePlace.Completion.extensionEmbedding w _).im = 0
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw]
  rfl

/-- The chosen complex embedding of a complex completion is surjective. -/
theorem classicalCompletionEmbedding_surjective {w : InfinitePlace K} (hw : w.IsComplex) :
    Function.Surjective (classicalCompletionEmbedding w) :=
  (InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex hw).comp
    ((InfinitePlace.Completion.equiv w).symm.surjective.comp
      (normalizedInfiniteCompletionEquiv w).surjective)

namespace HermitianMetric

variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]

/-- Conjugation compatibility makes the original pairing real on a real completed fibre. -/
theorem completedFiber_inner_im_of_real (h : HermitianMetric K M)
    {w : InfinitePlace K} (hw : w.IsReal)
    (x y : ClassicalCompletion w ⊗[K] (K ⊗[𝓞 K] M)) :
    ((h.fiber w.embedding).inner
      (classicalCompletedFiberMap M w x) (classicalCompletedFiberMap M w y)).im = 0 := by
  let : Algebra K ℂ := w.embedding.toAlgebra
  let : InnerProductSpace.Core ℂ (ComplexFiber M w.embedding) := h.fiber w.embedding
  have hs (m n : M) : ((h.fiber w.embedding).inner
      (fiberSection M w.embedding m) (fiberSection M w.embedding n)).im = 0 := by
    have hc := h.conjugate w.embedding m n
    rw [InfinitePlace.conjugate_embedding_eq_of_isReal hw] at hc
    have hh := congrArg Complex.im hc
    simp only [Complex.star_def, Complex.conj_im] at hh
    linarith
  have hc (a : ClassicalCompletion w) (b : K) :
      (classicalCompletionEmbedding w a * w.embedding b).im = 0 := by
    rw [← classicalCompletionEmbedding_coe w b, ← map_mul]
    exact classicalCompletionEmbedding_im_of_real hw _
  induction x using TensorProduct.inductionOn with
  | add x z hx hz =>
    simp only [map_add, InnerProductSpace.Core.inner_add_left, Complex.add_im, hx, hz,
      add_zero]
  | tmul a x =>
    induction x using TensorProduct.inductionOn with
    | add x z hx hz =>
      simp only [tmul_add, map_add, InnerProductSpace.Core.inner_add_left,
        Complex.add_im, hx, hz, add_zero]
    | tmul b m =>
      induction y using TensorProduct.inductionOn with
      | add y z hy hz =>
        simp only [map_add, InnerProductSpace.Core.inner_add_right, Complex.add_im,
          hy, hz, add_zero]
      | tmul c y =>
        induction y using TensorProduct.inductionOn with
        | add y z hy hz =>
          simp only [tmul_add, map_add, InnerProductSpace.Core.inner_add_right,
            Complex.add_im, hy, hz, add_zero]
        | tmul d n =>
          simp only [classicalCompletedFiberMap_tmul, InnerProductSpace.Core.inner_smul_left,
            InnerProductSpace.Core.inner_smul_right,
            Complex.mul_im, Complex.conj_im, hc, hs,
            neg_zero, mul_zero, zero_mul, add_zero]

variable [Module.Finite (𝓞 K) M]

/-- Polarization identifies the actual completed pairing with the original complex one.
The real-place case uses the metric's original conjugation axiom. -/
theorem completedFiber_inner (h : HermitianMetric K M) (w : InfinitePlace K) :
    letI := (inferInstance : (normalizedNumberFieldAdelicStructure K).IsArchimedeanNormalized)
      (normalizedInfinitePlacePoint w) (normalizedInfinitePlacePoint_mem_inf w)
    letI := IsRCLikeNormedField.rclike (ClassicalCompletion w)
    letI := h.adelicNormFamily.fibreNormedAddCommGroup (normalizedInfinitePlacePoint w)
    letI := h.adelicNormFamily.fibreNormedSpace (normalizedInfinitePlacePoint w)
    letI := h.adelicNormFamily.fiberInnerProductSpace
      (normalizedInfinitePlacePoint w) (normalizedInfinitePlacePoint_mem_inf w)
    ∀ x y : ClassicalCompletion w ⊗[K] (K ⊗[𝓞 K] M),
      classicalCompletionEmbedding w (inner (ClassicalCompletion w) x y) =
        (h.fiber w.embedding).inner
          (classicalCompletedFiberMap M w x) (classicalCompletedFiberMap M w y) := by
  let := (inferInstance : (normalizedNumberFieldAdelicStructure K).IsArchimedeanNormalized)
    (normalizedInfinitePlacePoint w) (normalizedInfinitePlacePoint_mem_inf w)
  let := IsRCLikeNormedField.rclike (ClassicalCompletion w)
  let := h.adelicNormFamily.fibreNormedAddCommGroup (normalizedInfinitePlacePoint w)
  let := h.adelicNormFamily.fibreNormedSpace (normalizedInfinitePlacePoint w)
  let := h.adelicNormFamily.fiberInnerProductSpace
    (normalizedInfinitePlacePoint w) (normalizedInfinitePlacePoint_mem_inf w)
  let : Algebra K ℂ := w.embedding.toAlgebra
  let : InnerProductSpace.Core ℂ (ComplexFiber M w.embedding) := h.fiber w.embedding
  let := InnerProductSpace.Core.toNormedAddCommGroup
    (𝕜 := ℂ) (F := ComplexFiber M w.embedding)
  let := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M w.embedding))
  intro x y
  have hn (z : ClassicalCompletion w ⊗[K] (K ⊗[𝓞 K] M)) :
      ‖classicalCompletedFiberMap M w z‖ = ‖z‖ := by
    change _ = h.adelicNormFamily.norm (normalizedInfinitePlacePoint w) z
    rw [h.adelicNormFamily_norm_infinite_point]
    rfl
  apply Complex.ext
  · rw [complexEmbedding_inner_re _ (norm_classicalCompletionEmbedding w)]
    change _ = (inner ℂ (classicalCompletedFiberMap M w x)
      (classicalCompletedFiberMap M w y)).re
    have hp := complexEmbedding_inner_re (RingHom.id ℂ) (fun _ => rfl)
      (classicalCompletedFiberMap M w x) (classicalCompletedFiberMap M w y)
    change (inner ℂ (classicalCompletedFiberMap M w x)
      (classicalCompletedFiberMap M w y)).re = _ at hp
    rw [hp]
    simp only [← map_add, ← map_sub, hn]
  · rcases w.isReal_or_isComplex with hw | hw
    · rw [classicalCompletionEmbedding_im_of_real hw, h.completedFiber_inner_im_of_real hw]
    · obtain ⟨c, hc⟩ := classicalCompletionEmbedding_surjective hw Complex.I
      rw [complexEmbedding_inner_im _ (norm_classicalCompletionEmbedding w) c hc]
      have hm := complexEmbedding_inner_im (RingHom.id ℂ) (fun _ => rfl)
        Complex.I rfl (classicalCompletedFiberMap M w x) (classicalCompletedFiberMap M w y)
      change (inner ℂ (classicalCompletedFiberMap M w x)
        (classicalCompletedFiberMap M w y)).im = _ at hm
      change _ = (inner ℂ (classicalCompletedFiberMap M w x)
        (classicalCompletedFiberMap M w y)).im
      rw [hm, ← hc, ← classicalCompletedFiberMap_smul,
        ← map_sub, ← map_add, hn, hn]

end HermitianMetric
end BostConjecture.Arithmetic
