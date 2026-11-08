/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Main.TensorSemistability.ArithmeticDefect
public import BostConjecture.Main.TensorSemistability.ExtremalNeighborhood
public import BostConjecture.Main.TensorSemistability.VariationTopology

/-!
# Actual maximizing Hermitian metrics give balanced tensor fibers

The two global compatible scalar-defect variations force a sum of nonnegative
squared norms to vanish. Local maximality is obtained from the actual
strictly stable maximizing pair.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace BostConjecture.Arithmetic.HermitianMetric

universe u
variable {K : Type*} [Field K] [NumberField K]
variable {M N : Type u} [AddCommGroup M] [Module (𝓞 K) M]
    [AddCommGroup N] [Module (𝓞 K) N]
    [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
    [Module.Finite (𝓞 K) N] [Module.Projective (𝓞 K) N]

/-- Actual strict maximizing pairs have balanced concrete tensor-submodule fibers. -/
theorem isBalanced_of_maximizing_pair
    (h : HermitianMetric K M) (k : HermitianMetric K N)
    (P : Submodule (𝓞 K) (M ⊗[𝓞 K] N))
    [Module.IsTorsionFree (𝓞 K) ((M ⊗[𝓞 K] N) ⧸ P)]
    (hrM : 0 < Module.finrank K (K ⊗[𝓞 K] M))
    (hrN : 0 < Module.finrank K (K ⊗[𝓞 K] N))
    (hst : h.IsStable) (kst : k.IsStable) (h0 : h.degree = 0) (k0 : k.degree = 0)
    (hP : ((h ⊗[𝓞 K] k).submodule P).degree = (h ⊗[𝓞 K] k).maxDegree)
    (hmax : IsGreatest (Compactness.tensorMaxDegreeValues.{u} K
      (Module.finrank K (K ⊗[𝓞 K] M)) (Module.finrank K (K ⊗[𝓞 K] N)))
      (h ⊗[𝓞 K] k).maxDegree) (σ : K →+* ℂ) :
    letI : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
    letI := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
    letI := InnerProductSpace.ofCore
      (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
    letI : InnerProductSpace.Core ℂ (ComplexFiber N σ) := k.fiber σ
    letI := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber N σ)
    letI := InnerProductSpace.ofCore
      (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber N σ))
    Balanced.IsBalanced (tensorSubmoduleFiber P σ) := by
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
  let A := h.tensorRightDefect k P
  let B := h.tensorLeftDefect k P
  have hs := h.tensorRightDefect_symmetric k P
  have ks := h.tensorLeftDefect_symmetric k P
  have hc := h.tensorRightDefect_conjugate k P
  have kc := h.tensorLeftDefect_conjugate k P
  have ht := h.trace_tensorRightDefect k P hrM
  have kt := h.trace_tensorLeftDefect k P hrN
  have hm := h.isLocalMax_degree_of_maximizing_pair k P hst kst h0 k0 hP hmax
    (h.exponentialVariation A hs hc) (k.exponentialVariation B ks kc)
    (h.continuous_exponentialVariation A hs hc).continuousAt
    (k.continuous_exponentialVariation B ks kc).continuousAt
    (h.exponentialVariation_zero A hs hc) (k.exponentialVariation_zero B ks kc)
    (fun t => (h.degree_exponentialVariation A hs hc ht t).trans h0)
    (fun t => (k.degree_exponentialVariation B ks kc kt t).trans k0)
  have hz := h.sum_tensorFiberProjectionTrace_eq_zero_of_isLocalMax k P A B hs ks hc kc hm
  have hpair (τ : K →+* ℂ) :
      (h ⊗[𝓞 K] k).fiberProjectionTrace P τ (tensorFiberGenerator A B τ) =
        (LinearMap.trace ℂ (ComplexFiber M τ) ((A τ).comp (A τ))).re +
        (LinearMap.trace ℂ (ComplexFiber N τ) ((B τ).comp (B τ))).re := by
    rw [fiberProjectionTrace_tensor_eq]
    dsimp only [A, B, tensorRightDefect, tensorLeftDefect]
    rw [Balanced.trace_comp_sub_scalar_id _ _ (ht τ),
      Balanced.trace_comp_sub_scalar_id _ _ (kt τ)]
  simp_rw [hpair] at hz
  have hAn (τ : K →+* ℂ) :
      0 ≤ (LinearMap.trace ℂ (ComplexFiber M τ) ((A τ).comp (A τ))).re :=
    Balanced.re_trace_comp_self_nonneg (A τ) (hs τ)
  have hBn (τ : K →+* ℂ) :
      0 ≤ (LinearMap.trace ℂ (ComplexFiber N τ) ((B τ).comp (B τ))).re :=
    Balanced.re_trace_comp_self_nonneg (B τ) (ks τ)
  have hzσ := (Finset.sum_eq_zero_iff_of_nonneg (fun τ _ => add_nonneg (hAn τ) (hBn τ))).mp hz
    σ (Finset.mem_univ σ)
  have hAz : A σ = 0 := Balanced.eq_zero_of_re_trace_comp_self_eq_zero (A σ) (hs σ)
    (le_antisymm (by linarith [hBn σ]) (hAn σ))
  have hBz : B σ = 0 := Balanced.eq_zero_of_re_trace_comp_self_eq_zero (B σ) (ks σ)
    (le_antisymm (by linarith [hAn σ]) (hBn σ))
  change Balanced.IsBalanced (tensorSubmoduleFiber P σ)
  constructor
  · have he := sub_eq_zero.mp hAz
    simpa only [tensorRightDefect, tensorPartialTraceRight, tensorSubmoduleProjection,
      finrank_tensorSubmoduleFiber, complexFiber_finrank, Complex.ofReal_div,
      Complex.ofReal_natCast] using he
  · have he := sub_eq_zero.mp hBz
    simpa only [tensorLeftDefect, tensorPartialTraceLeft, tensorSubmoduleProjection,
      finrank_tensorSubmoduleFiber, complexFiber_finrank, Complex.ofReal_div,
      Complex.ofReal_natCast] using he

end BostConjecture.Arithmetic.HermitianMetric
