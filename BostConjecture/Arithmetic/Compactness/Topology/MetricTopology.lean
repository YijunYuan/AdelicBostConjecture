/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Compactness.Topology.MetricComparison
public import Mathlib.Topology.Compactness.Compact

/-!
# The topology of intrinsic Hermitian metrics

Metrics carry pointwise convergence of their Hermitian forms on the actual
complex fibers. In finite dimension this gives locally uniform multiplicative
bounds for the fiber norms, with no choice of an integral basis.

Reference: this paper, pages 11–12.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct Filter
open scoped Topology

namespace BostConjecture.Arithmetic.HermitianMetric

variable {K : Type*} [Field K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]

/-- Pointwise convergence of the actual Hermitian forms on all complex fibers. -/
instance : TopologicalSpace (HermitianMetric K M) :=
  TopologicalSpace.induced (fun h : HermitianMetric K M =>
    fun σ x y => (h.fiber σ).inner x y) inferInstance

/-- Evaluating a fiber form at fixed vectors is continuous in the metric. -/
theorem continuous_inner_eval (σ : K →+* ℂ) (x y : ComplexFiber M σ) :
    Continuous (fun h : HermitianMetric K M => (h.fiber σ).inner x y) := by
  have hc : Continuous (fun h : HermitianMetric K M =>
      fun τ x y => (h.fiber τ).inner x y) := continuous_induced_dom
  exact (continuous_apply y).comp ((continuous_apply x).comp
    ((continuous_apply σ).comp hc))

/-- A fiber form is recovered from its finite Gram matrix in any complex basis. -/
lemma fiber_inner_eq_sum {ι : Type*} [Fintype ι]
    (h : HermitianMetric K M) (σ : K →+* ℂ)
    (b : Module.Basis ι ℂ (ComplexFiber M σ)) (x y : ComplexFiber M σ) :
    (h.fiber σ).inner x y = ∑ i, ∑ j,
      star (b.repr x i) * (b.repr y j * (h.fiber σ).inner (b i) (b j)) := by
  let : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
  let := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
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

variable [Module.Finite (𝓞 K) M]

omit [Module.Finite (𝓞 K) M] in
lemma fiberNorm_smul (h : HermitianMetric K M) (σ : K →+* ℂ)
    (c : ℂ) (x : ComplexFiber M σ) :
    h.fiberNorm σ (c • x) = ‖c‖ * h.fiberNorm σ x := by
  let : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
  let := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
  exact norm_smul c x

/-- Fiber norms vary jointly continuously with the metric and the vector.
The vector topology can be supplied by any one of the actual metrics. -/
theorem continuous_fiberNorm (h : HermitianMetric K M) (σ : K →+* ℂ) :
    letI : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
    letI := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
    Continuous (fun p : HermitianMetric K M × ComplexFiber M σ =>
      p.1.fiberNorm σ p.2) := by
  let : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
  let := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
  let : Module.Finite ℂ (ComplexFiber M σ) := by dsimp [ComplexFiber]; infer_instance
  let b := Module.finBasis ℂ (ComplexFiber M σ)
  have he : (fun p : HermitianMetric K M × ComplexFiber M σ =>
      p.1.fiberNorm σ p.2) = (fun p => Real.sqrt ((∑ i, ∑ j,
      star (b.repr p.2 i) * (b.repr p.2 j * (p.1.fiber σ).inner (b i) (b j))).re)) := by
    funext p
    unfold fiberNorm
    rw [fiber_inner_eq_sum _ σ b]
  rw [he]
  apply Real.continuous_sqrt.comp
  apply Complex.continuous_re.comp
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  exact (((b.coord i).continuous_of_finiteDimensional.comp continuous_snd).star).mul
    (((b.coord j).continuous_of_finiteDimensional.comp continuous_snd).mul
      ((continuous_inner_eval σ (b i) (b j)).comp continuous_fst))

/-- In one fiber, sufficiently close metrics have arbitrarily small
logarithmic distortion, uniformly over all vectors. -/
theorem eventually_fiberNorm_compare (h : HermitianMetric K M)
    (σ : K →+* ℂ) {t : ℝ} (ht : 0 < t) :
    ∀ᶠ g in 𝓝 h, ∀ x : ComplexFiber M σ,
      g.fiberNorm σ x ≤ Real.exp t * h.fiberNorm σ x ∧
      h.fiberNorm σ x ≤ Real.exp t * g.fiberNorm σ x := by
  let : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
  let := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
  let : Module.Finite ℂ (ComplexFiber M σ) := by dsimp [ComplexFiber]; infer_instance
  have hc := h.continuous_fiberNorm σ
  have hs : ∀ᶠ g in 𝓝 h, ∀ x ∈ Metric.sphere (0 : ComplexFiber M σ) 1,
      g.fiberNorm σ x < Real.exp t ∧ Real.exp (-t) < g.fiberNorm σ x := by
    apply (isCompact_sphere (0 : ComplexFiber M σ) 1).eventually_forall_of_forall_eventually
    intro x hx
    have hn : h.fiberNorm σ x = 1 := by
      change ‖x‖ = 1
      simpa only [Metric.mem_sphere, dist_zero_right] using hx
    have hupper : h.fiberNorm σ x < Real.exp t := by
      rw [hn]
      exact Real.one_lt_exp_iff.mpr ht
    have hlower : Real.exp (-t) < h.fiberNorm σ x := by
      rw [hn]
      exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht)
    exact ((hc.continuousAt (x := (h, x))).eventually_lt_const hupper).and
      ((hc.continuousAt (x := (h, x))).eventually_const_lt hlower)
  filter_upwards [hs] with g hg x
  by_cases hx : x = 0
  · subst x
    simp [fiberNorm, InnerProductSpace.Core.inner_zero_left]
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let u : ComplexFiber M σ := (‖x‖⁻¹ : ℂ) • x
  have hu : u ∈ Metric.sphere (0 : ComplexFiber M σ) 1 := by
    simp [u, norm_smul, hn.ne']
  have hgu := hg u hu
  have hscale : g.fiberNorm σ u = ‖x‖⁻¹ * g.fiberNorm σ x := by
    rw [fiberNorm_smul]
    simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn]
  rw [hscale] at hgu
  change g.fiberNorm σ x ≤ Real.exp t * ‖x‖ ∧ ‖x‖ ≤ Real.exp t * g.fiberNorm σ x
  constructor
  · have hb := mul_le_mul_of_nonneg_left hgu.1.le hn.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul, mul_comm] using hb
  · have hb := mul_le_mul_of_nonneg_left hgu.2.le (Real.exp_pos t).le
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at hb
    have hb' := mul_le_mul_of_nonneg_left hb hn.le
    calc
      ‖x‖ = ‖x‖ * 1 := (mul_one _).symm
      _ ≤ ‖x‖ * (Real.exp t * (‖x‖⁻¹ * g.fiberNorm σ x)) := hb'
      _ = Real.exp t * g.fiberNorm σ x := by field_simp

variable [NumberField K]

/-- The uniform comparison holds simultaneously at every archimedean embedding. -/
theorem eventually_all_fiberNorm_compare (h : HermitianMetric K M)
    {t : ℝ} (ht : 0 < t) :
    ∀ᶠ g in 𝓝 h, ∀ (σ : K →+* ℂ) (x : ComplexFiber M σ),
      g.fiberNorm σ x ≤ Real.exp t * h.fiberNorm σ x ∧
      h.fiberNorm σ x ≤ Real.exp t * g.fiberNorm σ x := by
  exact Filter.eventually_all.mpr (fun σ => h.eventually_fiberNorm_compare σ ht)

end BostConjecture.Arithmetic.HermitianMetric
