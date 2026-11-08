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
lemma hnFlag_zero (h : HermitianMetric K M) : h.hnFlag 0 = ⊥ :=
  h.hnFlag.head_eq_bot

/-- Every grade of the canonical flag is semistable against all integral submodules. -/
theorem hn_quotient_isSemistable (h : HermitianMetric K M)
    (i : Fin h.hnFlag.length) :
    ((h.submodule (h.hnSubmodule (i + 1))).quotient
      ((h.hnSubmodule i).comap (h.hnSubmodule (i + 1)).subtype)).IsSemistable := by
  apply h.quotient_isSemistable_of_interval (h.hnStep i).lt
  exact h.hnStep_quotient_slope_le i

lemma hnFlag_length_pos (h : HermitianMetric K M) : 0 < h.hnFlag.length := by
  by_contra! hz
  have he := h.hnFlag.length_eq_top
  rw [Nat.eq_zero_of_le_zero hz, h.hnFlag.head_eq_bot] at he
  exact bot_ne_top he

/-- The first saturated HN term has positive generic rank. -/
lemma hnSubmodule_one_rank_pos (h : HermitianMetric K M) :
    0 < Module.finrank K (K ⊗[𝓞 K] h.hnSubmodule 1) := by
  rw [hnSubmodule, integralPart_generic_finrank]
  have ht := h.hnFlag.strictMonoOn (Nat.zero_le _) (h.hnFlag_length_pos) (Nat.zero_lt_one)
  rw [h.hnFlag.head_eq_bot] at ht
  simpa using Submodule.finrank_strictMono ht

/-- The slope payoff's supremum is the principal cut of the first HN slope. -/
theorem subspaceSlope_max_eq_principal_hnSubmodule (h : HermitianMetric K M) :
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
lemma slope_hnSubmodule_one (h : HermitianMetric K M) :
    (h.submodule (h.hnSubmodule 1)).slope = h.maxSlope :=
  DedekindCut.principal_inj.mp
    (h.subspaceSlope_max_eq_principal_hnSubmodule.symm.trans h.subspaceSlope_max_eq)

lemma hnSlope_zero (h : HermitianMetric K M) :
    h.hnSlope ⟨0, h.hnFlag_length_pos⟩ = h.maxSlope := by
  rw [← h.slope_hnSubmodule_one]
  have he := h.hnStep_payoff ⟨0, h.hnFlag_length_pos⟩
  have ht : ⊥ < h.hnFlag 1 := by
    simpa [hnStep, h.hnFlag_zero] using (h.hnStep ⟨0, h.hnFlag_length_pos⟩).lt
  have hs : h.hnStep ⟨0, h.hnFlag_length_pos⟩ = ⟨⊥, h.hnFlag 1, ht⟩ := by
    ext <;> simp [hnStep, h.hnFlag_zero]
  rw [hs, h.subspaceSlope_apply_bot] at he
  exact le_antisymm (DedekindCut.principal_le_principal.mp he.ge)
    (DedekindCut.principal_le_principal.mp he.le)

lemma hnSlope_le_maxSlope (h : HermitianMetric K M)
    (i : Fin h.hnFlag.length) : h.hnSlope i ≤ h.maxSlope := by
  obtain ⟨i, hi⟩ := i
  induction i with
  | zero => exact (h.hnSlope_zero).le
  | succ i ih => exact (h.hnSlope_succ_lt i hi).le.trans (ih (Nat.lt_of_succ_lt hi))

end BostConjecture.Arithmetic.HermitianMetric
