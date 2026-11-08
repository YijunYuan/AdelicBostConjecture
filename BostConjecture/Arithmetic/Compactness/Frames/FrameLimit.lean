/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Compactness.Frames.FrameMetric

/-!
# Reconstruction of actual Hermitian limits from nondegenerate real frames

The real trace Gram matrix determines the direct sum of all actual fiber
forms after complexification. Its nondegenerate limit therefore reconstructs
positive-definite fiber forms, and the conjugation equations pass to the limit.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct Matrix Filter
open scoped Topology

namespace BostConjecture.Arithmetic.Compactness

/-- Finite Gram expansion for an inner-product core without a fixed norm. -/
lemma core_inner_eq_sum {V ι : Type*} [AddCommGroup V] [Module ℂ V] [Fintype ι]
    (p : InnerProductSpace.Core ℂ V) (b : Module.Basis ι ℂ V) (x y : V) :
    p.inner x y = ∑ i, ∑ j, star (b.repr x i) * (b.repr y j * p.inner (b i) (b j)) := by
  let : InnerProductSpace.Core ℂ V := p
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := V)
  let := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ V)
  change inner ℂ x y = _
  conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Complex.star_def]
  ring

end BostConjecture.Arithmetic.Compactness

namespace BostConjecture.Arithmetic.HermitianMetric

open Compactness

variable {K : Type*} [Field K] [NumberField K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]
variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Actual fiber pairings are reconstructed from the trace Gram entries. -/
lemma fiber_inner_eq_frame (h g : HermitianMetric K M)
    (b : Module.Basis ι ℤ M) (B : GeneralLinearGroup ι ℝ)
    (hGram : ∀ i j, inner ℝ (g.traceSection (b i)) (g.traceSection (b j)) =
      ∑ k, B.val k i * B.val k j)
    (σ : K →+* ℂ) (x y : ComplexFiber M σ) :
    (g.fiber σ).inner x y = (h.frameFiberCore b B σ).inner x y := by
  classical
  have he (u v : (σ : K →+* ℂ) → ComplexFiber M σ) :
      g.fiberProductCore.inner u v = (h.frameProductCore b B).inner u v := by
    rw [core_inner_eq_sum g.fiberProductCore (h.complexTraceBasis b),
      core_inner_eq_sum (h.frameProductCore b B) (h.complexTraceBasis b)]
    simp only [fiberProductCore_basis, hGram, frameProductCore_basis]
  have hh := he (Pi.single σ x) (Pi.single σ y)
  change (∑ τ, (g.fiber τ).inner (Pi.single σ x τ) (Pi.single σ y τ)) =
    (h.frameFiberCore b B σ).inner x y at hh
  rw [Finset.sum_eq_single σ] at hh
  · simpa only [Pi.single_eq_same] using hh
  · intro τ _ hτ
    rw [Pi.single_eq_of_ne hτ]
    let := g.fiber τ
    exact InnerProductSpace.Core.inner_zero_left _
  · simp

/-- Each reconstructed pairing depends continuously on the real frame. -/
theorem continuous_frameProduct_inner (h : HermitianMetric K M)
    (b : Module.Basis ι ℤ M) (x y : (σ : K →+* ℂ) → ComplexFiber M σ) :
    Continuous (fun B : GeneralLinearGroup ι ℝ => (h.frameProductCore b B).inner x y) := by
  have he : (fun B : GeneralLinearGroup ι ℝ => (h.frameProductCore b B).inner x y) =
      (fun B => ∑ i, ∑ j, star ((h.complexTraceBasis b).repr x i) *
        ((h.complexTraceBasis b).repr y j * (∑ k, B.val k i * B.val k j : ℝ))) := by
    funext B
    rw [core_inner_eq_sum _ (h.complexTraceBasis b)]
    simp only [frameProductCore_basis]
  rw [he]
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  apply continuous_const.mul
  apply continuous_const.mul
  apply Complex.continuous_ofReal.comp
  apply continuous_finsetSum
  intro k _
  have hval : Continuous (fun B : GeneralLinearGroup ι ℝ => (B.val : Matrix ι ι ℝ)) :=
    Units.continuous_val
  have hcoord (k i : ι) : Continuous (fun B : GeneralLinearGroup ι ℝ => B.val k i) :=
    (continuous_apply i).comp ((continuous_apply k).comp hval)
  exact (hcoord k i).mul (hcoord k j)

/-- A convergent sequence of nondegenerate actual trace frames reconstructs
an actual conjugation-compatible Hermitian metric limit. -/
theorem exists_metric_limit_of_trace_frames
    (h : ℕ → HermitianMetric K M) (b : Module.Basis ι ℤ M)
    (B : ℕ → GeneralLinearGroup ι ℝ) (Blim : GeneralLinearGroup ι ℝ)
    (hB : Tendsto B atTop (𝓝 Blim))
    (hGram : ∀ n i j, inner ℝ ((h n).traceSection (b i)) ((h n).traceSection (b j)) =
      ∑ k, (B n).val k i * (B n).val k j) :
    ∃ g : HermitianMetric K M, Tendsto h atTop (𝓝 g) := by
  classical
  have ht (σ : K →+* ℂ) (x y : ComplexFiber M σ) :
      Tendsto (fun n => ((h n).fiber σ).inner x y) atTop
        (𝓝 (((h 0).frameFiberCore b Blim σ).inner x y)) := by
    have hc := ((h 0).continuous_frameProduct_inner b (Pi.single σ x) (Pi.single σ y))
    convert hc.continuousAt.tendsto.comp hB using 1
    funext n
    exact (h 0).fiber_inner_eq_frame (h n) b (B n) (hGram n) σ x y
  let g : HermitianMetric K M :=
    { fiber := fun σ => (h 0).frameFiberCore b Blim σ
      conjugate := by
        intro σ x y
        have hl := ht (ComplexEmbedding.conjugate σ)
          (fiberSection M _ x) (fiberSection M _ y)
        have hr := (ht σ (fiberSection M σ x) (fiberSection M σ y)).star
        simp only [HermitianMetric.conjugate] at hl
        exact tendsto_nhds_unique hl hr }
  refine ⟨g, ?_⟩
  have hi : Topology.IsInducing (fun g : HermitianMetric K M =>
      fun σ x y => (g.fiber σ).inner x y) := ⟨rfl⟩
  apply hi.tendsto_nhds_iff.mpr
  apply tendsto_pi_nhds.mpr
  intro σ
  apply tendsto_pi_nhds.mpr
  intro x
  apply tendsto_pi_nhds.mpr
  exact fun y => ht σ x y

end BostConjecture.Arithmetic.HermitianMetric
