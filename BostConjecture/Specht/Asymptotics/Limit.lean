/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Specht.Asymptotics.LogExpectation
public import BostConjecture.Specht.Lattice.OneRow

/-!
# Sublinear normalized covolume of the canonical rectangular orbit lattice

The bulk separation estimate controls the actual finite average of the
seminormal logarithms. The integral Gram comparison then gives the limit.
Reference: this paper equation (6) and Proposition 5.2, pages 7–8.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Specht

open OAI.Saxl Finset Filter
open scoped BigOperators Topology

/-- The normalized logarithmic norm average of actual standard tableaux tends to zero. -/
theorem tendsto_average_log_prefixNormProduct_div {a : ℕ} (ha : 2 ≤ a) :
    Tendsto (fun k : ℕ =>
      (𝔼 T : {T : Tableau (a * k) (rectangle a k) // IsStandard T},
        Real.log (prefixNormProduct T.val)) / (a * k : ℕ)) atTop (𝓝 0) := by
  let C : ℝ := (a - 1 : ℕ) * Real.log 2
  have hC : 0 ≤ C := mul_nonneg (by positivity) (Real.log_nonneg (by norm_num))
  have hn (k : ℕ) : 0 ≤
      (𝔼 T : {T : Tableau (a * k) (rectangle a k) // IsStandard T},
        Real.log (prefixNormProduct T.val)) / (a * k : ℕ) := by
    apply div_nonneg _ (Nat.cast_nonneg _)
    apply expect_nonneg
    intro T _
    rw [log_prefixNormProduct T.property]
    exact sum_nonneg (fun m _ => log_prefixInsertionFactor_nonneg T.property m)
  apply tendsto_order.mpr
  constructor
  · intro x hx
    exact Eventually.of_forall (fun k => hx.trans_le (hn k))
  · intro η hη
    let e : ℝ := η / (8 * (C + 1))
    have he : 0 < e := div_pos hη (by positivity)
    let L : ℝ := 2 + 4 * (a - 1 : ℕ) / η
    have hL : 2 ≤ L := by
      dsimp [L]
      have : (0 : ℝ) ≤ 4 * (a - 1 : ℕ) / η := by positivity
      linarith
    have heC : e * C ≤ η / 8 := by
      dsimp [e]
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ (by positivity : 0 < 8 * (C + 1))).mpr
      nlinarith
    have hLbound : (a - 1 : ℕ) / (L - 1) ≤ η / 4 := by
      apply (div_le_iff₀ (by linarith : 0 < L - 1)).mpr
      dsimp [L]
      field_simp
      nlinarith
    obtain ⟨K, hK⟩ := average_log_prefixNormProduct_eventually_le ha he he hL
    have hinv : Tendsto (fun k : ℕ => (2 / (a : ℝ)) / k) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    have hinv' : Tendsto (fun k : ℕ => (2 : ℝ) / (a * k : ℕ)) atTop (𝓝 0) := by
      simpa only [Nat.cast_mul, div_div] using hinv
    filter_upwards [eventually_ge_atTop K, (tendsto_order.mp hinv').2 e he] with k hk hi
    have hb := hK k hk
    change _ ≤ (2 * e + 2 / (a * k : ℕ)) * C + (a - 1 : ℕ) / (L - 1) + C * e at hb
    have hsmall := mul_le_mul_of_nonneg_right hi.le hC
    nlinarith

/-- The canonical integral orbit lattice has sublinear rank-normalized logarithmic
covolume in every fixed positive rectangular height. -/
theorem tendsto_rectangleLogCovolume_div {a : ℕ} (ha : 0 < a) :
    Tendsto (fun k : ℕ => rectangleLogCovolume a k / (a * k : ℕ)) atTop (𝓝 0) := by
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt ha) with h | h
  · have : a = 1 := h.symm
    subst a
    simpa only [Nat.one_mul] using tendsto_rectangleLogCovolume_one_div
  · apply squeeze_zero
      (fun k => div_nonneg (rectangleLogCovolume_nonneg a k) (Nat.cast_nonneg _))
      (fun k => ?_) (tendsto_average_log_prefixNormProduct_div (by omega : 2 ≤ a))
    have hbound := two_mul_rectangleLogCovolume_le_average_log_prefixNormProduct a k
    have hn := rectangleLogCovolume_nonneg a k
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    rw [expect_eq_sum_div_card, card_univ]
    linarith

end BostConjecture.Specht
