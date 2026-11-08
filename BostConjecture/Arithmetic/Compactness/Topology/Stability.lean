/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Compactness.Maximum.Comparison

/-!
# The degree gap at a normalized strictly stable metric

Strict stability is the strict slope inequality for every nonzero proper
saturated integral submodule. Arithmetic degree finiteness strengthens the
individual strict inequalities to a uniform negative gap when the ambient
degree is zero.

Reference: this paper, page 12.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace BostConjecture.Arithmetic.HermitianMetric

variable {K : Type*} [Field K] [NumberField K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]
variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]

/-- Strict slope inequality for every nonzero proper saturated submodule,
written without division by its positive rank. -/
def IsStable (h : HermitianMetric K M) : Prop :=
  ∀ P : Submodule (𝓞 K) M, Module.IsTorsionFree (𝓞 K) (M ⧸ P) →
    P ≠ ⊥ → P ≠ ⊤ → (h.submodule P).degree <
      (Module.finrank K (K ⊗[𝓞 K] P) : ℝ) * h.slope

omit [Module.Projective (𝓞 K) M] in
/-- At degree zero strict stability is precisely negativity of all proper
nonzero saturated induced degrees. -/
theorem isStable_iff_degree_neg (h : HermitianMetric K M) (h0 : h.degree = 0) :
    h.IsStable ↔ ∀ P : Submodule (𝓞 K) M,
      Module.IsTorsionFree (𝓞 K) (M ⧸ P) → P ≠ ⊥ → P ≠ ⊤ →
        (h.submodule P).degree < 0 := by
  simp only [IsStable, slope, h0, zero_div, mul_zero]

/-- Arithmetic finiteness turns the strict inequalities into a uniform gap. -/
theorem IsStable.exists_degree_gap {h : HermitianMetric K M}
    (hs : h.IsStable) (h0 : h.degree = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ P : Submodule (𝓞 K) M,
      Module.IsTorsionFree (𝓞 K) (M ⧸ P) → P ≠ ⊥ → P ≠ ⊤ →
        (h.submodule P).degree ≤ -δ := by
  classical
  have hneg := (h.isStable_iff_degree_neg h0).mp hs
  let S := {P : Submodule (𝓞 K) M | Module.IsTorsionFree (𝓞 K) (M ⧸ P) ∧
    -1 ≤ (h.submodule P).degree ∧ P ≠ ⊥ ∧ P ≠ ⊤}
  have hS : S.Finite := (h.finite_saturated_submodules_degree_ge (-1)).subset
    (fun P hP => ⟨hP.1, hP.2.1⟩)
  by_cases hne : S.Nonempty
  · obtain ⟨P, hP, hmax⟩ := hS.toFinset.exists_max_image
      (fun P => (h.submodule P).degree) (hS.toFinset_nonempty.mpr hne)
    have hPS := hS.mem_toFinset.mp hP
    have hn : (h.submodule P).degree < 0 := hneg P hPS.1 hPS.2.2.1 hPS.2.2.2
    refine ⟨min 1 (-(h.submodule P).degree), lt_min zero_lt_one (neg_pos.mpr hn), ?_⟩
    intro Q hQ hQb hQt
    by_cases hQ1 : -1 ≤ (h.submodule Q).degree
    · have hm := hmax Q (hS.mem_toFinset.mpr ⟨hQ, hQ1, hQb, hQt⟩)
      have hmin := min_le_right (1 : ℝ) (-(h.submodule P).degree)
      linarith
    · have hmin := min_le_left (1 : ℝ) (-(h.submodule P).degree)
      linarith
  · refine ⟨1, zero_lt_one, fun P hP hPb hPt => ?_⟩
    by_contra hn
    exact hne ⟨P, hP, le_of_not_ge hn, hPb, hPt⟩

/-- The uniform degree gap persists under sufficiently small changes of
the actual fiber norms, after restricting to normalized metrics. -/
theorem isStable_of_fiberNorm_compare {h g : HermitianMetric K M}
    {δ t : ℝ} (hgap : ∀ P : Submodule (𝓞 K) M,
      Module.IsTorsionFree (𝓞 K) (M ⧸ P) → P ≠ ⊥ → P ≠ ⊤ →
        (h.submodule P).degree ≤ -δ)
    (ht : 0 ≤ t) (hsmall : (Module.finrank K (K ⊗[𝓞 K] M) : ℝ) * t < δ)
    (hg0 : g.degree = 0)
    (hgh : ∀ (σ : K →+* ℂ) (x : ComplexFiber M σ),
      g.fiberNorm σ x ≤ Real.exp t * h.fiberNorm σ x)
    (hhg : ∀ (σ : K →+* ℂ) (x : ComplexFiber M σ),
      h.fiberNorm σ x ≤ Real.exp t * g.fiberNorm σ x) : g.IsStable := by
  apply (g.isStable_iff_degree_neg hg0).mpr
  intro P hP hPb hPt
  have hd := hgap P hP hPb hPt
  have hb := (abs_le.mp (h.abs_degree_submodule_sub_le_rank_mul g ht hgh hhg P)).2
  linarith

end BostConjecture.Arithmetic.HermitianMetric
