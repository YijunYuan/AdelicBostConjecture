/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.HN.Subspace
public import BostConjecture.Arithmetic.HN.QuotientSemistable
public import BostConjecture.Arithmetic.HN.MaxSlope

/-!
# Intrinsic Hermitian HN grades and maximal slope

Maximal slope and its finiteness are defined independently of the HN flag in
`HN/MaxSlope.lean`. The canonical flag has semistable actual quotient bundles,
and its first term attains the maximum over all positive-rank integral
submodules.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct HarderNarasimhan

namespace BostConjecture.Arithmetic.HermitianMetric

variable {K : Type*} [Field K] [NumberField K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]
variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
variable [Nontrivial (K ⊗[𝓞 K] M)]

@[simp]
lemma hnFlag_zero (h : HermitianMetric (K := K) M) : h.hnFlag 0 = ⊥ :=
  h.hnFlag.head_eq_bot

@[simp]
lemma hnFlag_at_length (h : HermitianMetric (K := K) M) :
    h.hnFlag h.hnFlag.length = ⊤ := h.hnFlag.length_eq_top

/-- Every grade of the canonical flag is semistable against all integral submodules. -/
theorem hn_quotient_isSemistable (h : HermitianMetric (K := K) M)
    (i : Fin h.hnFlag.length) :
    ((h.submodule (h.hnSubmodule (i + 1))).quotient
      ((h.hnSubmodule i).comap (h.hnSubmodule (i + 1)).subtype)).IsSemistable := by
  apply h.quotient_isSemistable_of_interval (h.hnStep i).lt
  exact h.hnStep_quotient_slope_le i

lemma hnFlag_length_pos (h : HermitianMetric (K := K) M) : 0 < h.hnFlag.length := by
  by_contra! hz
  have he := h.hnFlag.length_eq_top
  rw [Nat.eq_zero_of_le_zero hz, h.hnFlag.head_eq_bot] at he
  exact bot_ne_top he

/-- The first saturated HN term has positive generic rank. -/
lemma hnSubmodule_one_rank_pos (h : HermitianMetric (K := K) M) :
    0 < Module.finrank K (K ⊗[𝓞 K] h.hnSubmodule 1) := by
  rw [hnSubmodule, integralPart_generic_finrank]
  have ht := h.hnFlag.strictMonoOn (Nat.zero_le _) (h.hnFlag_length_pos) (Nat.zero_lt_one)
  rw [h.hnFlag.head_eq_bot] at ht
  simpa using Submodule.finrank_strictMono ht

/-- The slope payoff's supremum is the principal cut of the first HN slope. -/
theorem subspaceSlope_max_eq_principal_hnSubmodule (h : HermitianMetric (K := K) M) :
    (BostConjecture.Subspace.slope h.subspaceDegree).max ⊤ =
      DedekindCut.principal (h.submodule (h.hnSubmodule 1)).slope := by
  let μ := BostConjecture.Subspace.slope h.subspaceDegree
  have hx := (PayoffFunction.hnFiltration_succ_isGreatest_breakpoints (μ := μ)
    (n := 0) (h.hnFlag.head_eq_bot.trans_ne bot_ne_top)).1
  change μ.IsBreakpoint ⟨h.hnFlag 0, ⊤, _⟩ (h.hnFlag 1) at hx
  have hx : μ.IsBreakpoint ⊤ (h.hnFlag 1) := by
    simpa only [h.hnFlag_zero, StrictIntvl.mk_bot_top] using hx
  exact (BostConjecture.Slope.max_top_eq_of_isBreakpoint μ hx).trans
    (h.subspaceSlope_apply_bot _ hx.left_lt)

/-- The first saturated HN term attains maximal slope. -/
@[simp]
lemma slope_hnSubmodule_one (h : HermitianMetric (K := K) M) :
    (h.submodule (h.hnSubmodule 1)).slope = h.maxSlope :=
  DedekindCut.principal_inj.mp
    (h.subspaceSlope_max_eq_principal_hnSubmodule.symm.trans h.subspaceSlope_max_eq)

lemma hnSlope_zero (h : HermitianMetric (K := K) M) :
    h.hnSlope ⟨0, h.hnFlag_length_pos⟩ = h.maxSlope := by
  rw [← h.slope_hnSubmodule_one]
  have he := h.hnStep_payoff ⟨0, h.hnFlag_length_pos⟩
  have ht : ⊥ < h.hnFlag 1 := by
    have ht := (h.hnStep ⟨0, h.hnFlag_length_pos⟩).lt
    simpa [hnStep, h.hnFlag_zero] using ht
  have hs : h.hnStep ⟨0, h.hnFlag_length_pos⟩ = ⟨⊥, h.hnFlag 1, ht⟩ := by
    ext <;> simp [hnStep, h.hnFlag_zero]
  rw [hs, h.subspaceSlope_apply_bot] at he
  exact le_antisymm (DedekindCut.principal_le_principal.mp he.ge)
    (DedekindCut.principal_le_principal.mp he.le)

lemma hnSlope_le_maxSlope (h : HermitianMetric (K := K) M)
    (i : Fin h.hnFlag.length) : h.hnSlope i ≤ h.maxSlope := by
  obtain ⟨i, hi⟩ := i
  induction i with
  | zero => exact (h.hnSlope_zero).le
  | succ i ih => exact (h.hnSlope_succ_lt i hi).le.trans (ih (Nat.lt_of_succ_lt hi))

/-- Every initial subspace of an HN step satisfies the step's degree bound. -/
lemma hn_interval_degree_le (h : HermitianMetric (K := K) M)
    (i : Fin h.hnFlag.length) {Z : Submodule K (K ⊗[𝓞 K] M)}
    (hiz : h.hnFlag i < Z) (hzi : Z ≤ h.hnFlag (i + 1)) :
    h.subspaceDegree Z - h.subspaceDegree (h.hnFlag i) ≤
      h.hnSlope i * ((Module.finrank K Z : ℝ) - Module.finrank K (h.hnFlag i)) := by
  have hs := h.hnStep_quotient_slope_le i Z hiz hzi
  rw [hnSubmodule, slope, ← subspaceDegree_sub_eq_quotient h hiz.le,
    subspaceQuotient_finrank hiz.le] at hs
  have hr := Submodule.finrank_strictMono hiz
  rw [Nat.cast_sub hr.le] at hs
  exact (div_le_iff₀ (sub_pos.mpr (by exact_mod_cast hr))).mp hs

lemma hnSlope_lt_maxSlope (h : HermitianMetric (K := K) M)
    (i : Fin h.hnFlag.length) (hi : 0 < i.val) : h.hnSlope i < h.maxSlope := by
  obtain ⟨i, hi'⟩ := i
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
  exact (h.hnSlope_succ_lt j hi').trans_le (h.hnSlope_le_maxSlope ⟨j, Nat.lt_of_succ_lt hi'⟩)

/-- A subspace not contained in the first HN term has strictly smaller slope. -/
theorem subspaceDegree_lt_maxSlope (h : HermitianMetric (K := K) M)
    (X : Submodule K (K ⊗[𝓞 K] M)) (hX1 : ¬ X ≤ h.hnFlag 1) :
    h.subspaceDegree X < h.maxSlope * Module.finrank K X := by
  have hb : ∀ i, i ≤ h.hnFlag.length → X ≤ h.hnFlag i →
      h.subspaceDegree X < h.maxSlope * Module.finrank K X := by
    intro i
    induction i with
    | zero =>
      intro _ hi
      exact False.elim (hX1 (hi.trans (h.hnFlag.monotone (Nat.zero_le 1))))
    | succ i ih =>
      intro hi hXi
      by_cases hx : X ≤ h.hnFlag i
      · exact ih (Nat.le_of_succ_le hi) hx
      have hi0 : 0 < i := by
        by_contra! hz
        have he : i = 0 := Nat.eq_zero_of_le_zero hz
        subst i
        exact hX1 hXi
      have hinf := h.subspaceDegree_le_maxSlope (X ⊓ h.hnFlag i)
      have hs := h.hn_interval_degree_le ⟨i, hi⟩ (right_lt_sup.mpr hx)
        (sup_le hXi (h.hnFlag.monotone (Nat.le_succ i)))
      have hc := h.subspaceDegree_supermodular X (h.hnFlag i)
      have hr : (Module.finrank K ↥(X ⊔ h.hnFlag i) : ℝ) +
          Module.finrank K ↥(X ⊓ h.hnFlag i) = Module.finrank K X +
          Module.finrank K (h.hnFlag i) := by
        exact_mod_cast Submodule.finrank_sup_add_finrank_inf_eq X (h.hnFlag i)
      have hd : 0 < (Module.finrank K ↥(X ⊔ h.hnFlag i) : ℝ) -
          Module.finrank K (h.hnFlag i) := sub_pos.mpr (by
        exact_mod_cast Submodule.finrank_strictMono (right_lt_sup.mpr hx))
      have hm := mul_lt_mul_of_pos_right (h.hnSlope_lt_maxSlope ⟨i, hi⟩ hi0) hd
      change h.subspaceDegree (X ⊔ h.hnFlag i) - h.subspaceDegree (h.hnFlag i) ≤
        h.hnSlope ⟨i, hi⟩ * ((Module.finrank K ↥(X ⊔ h.hnFlag i) : ℝ) -
          Module.finrank K (h.hnFlag i)) at hs
      have hrm := congrArg (h.maxSlope * ·) hr
      nlinarith only [hinf, hc, hs, hm, hrm]
  exact hb h.hnFlag.length le_rfl (by rw [h.hnFlag_at_length]; exact le_top)

/-- Every maximal-slope integral submodule is contained in the first saturated term. -/
theorem le_hnSubmodule_one_of_slope_eq (h : HermitianMetric (K := K) M)
    (P : Submodule (𝓞 K) M) (hP : 0 < Module.finrank K (K ⊗[𝓞 K] P))
    (he : (h.submodule P).slope = h.maxSlope) : P ≤ h.hnSubmodule 1 := by
  have hX : P.baseChange K ≤ h.hnFlag 1 := by
    by_contra hn
    have hd := h.subspaceDegree_lt_maxSlope (P.baseChange K) hn
    have hr : 0 < Module.finrank K (P.baseChange K) :=
      (Submodule.toBaseChange.toLinearEquiv K P).finrank_eq ▸ hP
    have hs := (div_lt_iff₀ (show (0 : ℝ) < Module.finrank K (P.baseChange K) by
      exact_mod_cast hr)).mpr hd
    rw [subspaceDegree_div_finrank] at hs
    exact (he ▸ h.slope_le_saturation P).not_gt hs
  intro x hx
  exact hX (Submodule.tmul_mem_baseChange_of_mem 1 hx)

/-- The set of slopes of positive-rank integral submodules has this actual maximum. -/
theorem isGreatest_slopes (h : HermitianMetric (K := K) M) :
    IsGreatest {s : ℝ | ∃ P : Submodule (𝓞 K) M,
      0 < Module.finrank K (K ⊗[𝓞 K] P) ∧ (h.submodule P).slope = s} h.maxSlope := by
  refine ⟨⟨h.hnSubmodule 1, h.hnSubmodule_one_rank_pos, h.slope_hnSubmodule_one⟩, ?_⟩
  rintro s ⟨P, hP, rfl⟩
  exact h.slope_submodule_le_maxSlope P hP

/-- The first term is the largest, by inclusion, among all maximal-slope submodules. -/
theorem isGreatest_maximalSlope_submodules (h : HermitianMetric (K := K) M) :
    IsGreatest {P : Submodule (𝓞 K) M | 0 < Module.finrank K (K ⊗[𝓞 K] P) ∧
      (h.submodule P).slope = h.maxSlope} (h.hnSubmodule 1) := by
  refine ⟨⟨h.hnSubmodule_one_rank_pos, h.slope_hnSubmodule_one⟩, ?_⟩
  intro P hP
  exact h.le_hnSubmodule_one_of_slope_eq P hP.1 hP.2

/-- Among saturated maximal-slope submodules, maximal rank characterizes the first term. -/
theorem eq_hnSubmodule_one_of_slope_eq_of_rank (h : HermitianMetric (K := K) M)
    (P : Submodule (𝓞 K) M) [Module.IsTorsionFree (𝓞 K) (M ⧸ P)]
    (he : (h.submodule P).slope = h.maxSlope)
    (hr : Module.finrank K (K ⊗[𝓞 K] P) =
      Module.finrank K (K ⊗[𝓞 K] h.hnSubmodule 1)) : P = h.hnSubmodule 1 := by
  have hP : 0 < Module.finrank K (K ⊗[𝓞 K] P) := hr ▸ h.hnSubmodule_one_rank_pos
  have hle := h.le_hnSubmodule_one_of_slope_eq P hP he
  have heq : P.baseChange K = (h.hnSubmodule 1).baseChange K :=
    Submodule.eq_of_le_of_finrank_eq (Submodule.baseChange_mono K hle)
      (((Submodule.toBaseChange.toLinearEquiv K P).finrank_eq.symm.trans hr).trans
        (Submodule.toBaseChange.toLinearEquiv K (h.hnSubmodule 1)).finrank_eq)
  rw [← integralPart_baseChange P, heq]
  simp only [hnSubmodule, baseChange_integralPart]

end BostConjecture.Arithmetic.HermitianMetric
