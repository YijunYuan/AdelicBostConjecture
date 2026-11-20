/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Specht.Asymptotics.LogInsertion
public import BostConjecture.Specht.Asymptotics.Separation

/-!
# Averaging logarithmic insertions over actual standard tableaux

Finite averages of the seminormal logarithmic factors are bounded using
the prefix distribution and gap estimates. The resulting expectation
controls the normalized logarithmic Gram determinant.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Specht

open OAI.Saxl Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Express the existing actual prefix-event probability with a fixed tableau size. -/
theorem expect_prefixGap_eq {a k n m : ℕ} (hm : m ≤ n) (L : ℝ) :
    (𝔼 T : {T : Tableau n (rectangle a k) // IsStandard T},
      if HasSmallGap (fun i : Fin a =>
        (shiftedRowLength (prefixShape T.val m hm) a i.val : ℝ)) L then 1 else 0) =
      rectanglePrefixGapProbability a k m (n - m) L := by
  classical
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [Nat.add_sub_cancel_left]
  simp only [rectanglePrefixGapProbability,
    rectanglePrefixShape, expect_eq_sum_div_card, card_univ]
  congr 1

/-- Bulk separation bounds the finite average of the actual bad-prefix indicator. -/
theorem expect_prefixGap_uniform {a : ℕ} (ha : 2 ≤ a) {ε : ℝ} (hε : 0 < ε)
    (L : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℕ, ∀ k ≥ K, ∀ m : Fin (a * k),
      ε * (a * k : ℕ) ≤ m.val → ε * (a * k : ℕ) ≤ a * k - m.val →
      (𝔼 T : {T : Tableau (a * k) (rectangle a k) // IsStandard T},
        if HasSmallGap (fun i : Fin a =>
          (shiftedRowLength (prefixShape T.val m.val (Nat.le_of_lt m.isLt)) a i.val : ℝ)) L
          then 1 else 0) < δ := by
  obtain ⟨K, hK⟩ := rectanglePrefixGapProbability_uniform ha hε L hδ
  refine ⟨K, ?_⟩
  intro k hk m hm hl
  rw [expect_prefixGap_eq (Nat.le_of_lt m.isLt)]
  exact hK k hk m.val (a * k - m.val) (by omega) hm (by
    simpa only [Nat.cast_sub (Nat.le_of_lt m.isLt), Nat.cast_mul] using hl)

/-- An insertion's average is bounded by the small-gap-free bound plus the
uniform bound times the actual bad-prefix probability. -/
theorem expect_logInsertion_le {a k : ℕ} (hk : 0 < k) (m : Fin (a * k))
    {L : ℝ} (hL : 2 ≤ L) :
    (𝔼 T : {T : Tableau (a * k) (rectangle a k) // IsStandard T},
      Real.log (prefixInsertionFactor T.val m)) ≤
      (a - 1 : ℕ) / (L - 1) + (a - 1 : ℕ) * Real.log 2 *
        (𝔼 T : {T : Tableau (a * k) (rectangle a k) // IsStandard T},
          if HasSmallGap (fun i : Fin a =>
            (shiftedRowLength (prefixShape T.val m.val (Nat.le_of_lt m.isLt)) a i.val : ℝ)) L
            then 1 else 0) := by
  classical
  have hcard : 0 < Fintype.card {T : Tableau (a * k) (rectangle a k) // IsStandard T} := by
    exact_mod_cast card_standard_rectangle_pos a hk
  have hne : (univ : Finset {T : Tableau (a * k) (rectangle a k) // IsStandard T}).Nonempty :=
    card_pos.mp (by simpa using hcard)
  have hB : (0 : ℝ) ≤ (a - 1 : ℕ) / (L - 1) := div_nonneg (by positivity) (by linarith)
  calc
    _ ≤ 𝔼 T : {T : Tableau (a * k) (rectangle a k) // IsStandard T},
        ((a - 1 : ℕ) / (L - 1) + (a - 1 : ℕ) * Real.log 2 *
          (if HasSmallGap (fun i : Fin a =>
            (shiftedRowLength (prefixShape T.val m.val (Nat.le_of_lt m.isLt)) a i.val : ℝ)) L
            then 1 else 0)) := by
      apply expect_le_expect
      intro T _
      split_ifs with hgap
      · simpa only [mul_one] using (log_prefixInsertionFactor_le (t := T.val) m).trans
          (le_add_of_nonneg_left hB)
      · simpa only [mul_zero, add_zero] using
          log_prefixInsertionFactor_le_of_not_gap (t := T.val) m hL hgap
    _ = _ := by rw [expect_add_distrib, expect_const hne, mul_expect]

private theorem sum_indicator_lt_le {d : ℕ} (b : ℕ) (g : Fin d → Fin d)
    (hg : Function.Injective g) :
    (∑ m : Fin d, if (g m).val < b then (1 : ℝ) else 0) ≤ b := by
  rw [sum_boole]
  have h := card_le_card_of_injOn (fun m : Fin d => (g m).val)
    (s := univ.filter fun m => (g m).val < b) (t := range b)
    (fun m hm => mem_range.mpr (mem_filter.mp hm).2)
    (fun i _ j _ hij => hg (Fin.ext hij))
  exact_mod_cast (by simpa only [card_range] using h)

/-- A finite sequence bounded everywhere and more sharply in the bulk has
only two short boundary intervals contributing the larger bound. -/
theorem sum_le_of_bulk {d : ℕ} (f : Fin d → ℝ) {ε C B : ℝ}
    (hε : 0 ≤ ε) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hf : ∀ m, f m ≤ C)
    (hbulk : ∀ m, ε * d ≤ m.val → ε * d ≤ (d : ℝ) - m.val → f m ≤ B) :
    ∑ m, f m ≤ (d : ℝ) * B + (2 * ε * d + 2) * C := by
  let b := ⌈ε * d⌉₊
  have hb : ε * d ≤ (b : ℝ) := Nat.le_ceil _
  have hpoint (m : Fin d) : f m ≤ B +
      C * (if m.val < b then 1 else 0) + C * (if (Fin.rev m).val < b then 1 else 0) := by
    split_ifs with hm hr
    · simp only [mul_one]; linarith [hf m]
    · simp only [mul_one, mul_zero, add_zero]; linarith [hf m]
    · simp only [mul_one, mul_zero, add_zero]; linarith [hf m]
    · rename_i hr
      simp only [mul_zero, add_zero]
      apply hbulk
      · have hm' : (b : ℝ) ≤ m.val := by exact_mod_cast (le_of_not_gt hm)
        linarith
      · have hr' : b ≤ (Fin.rev m).val := le_of_not_gt hr
        have hnat : b + m.val ≤ d := by
          rw [Fin.val_rev] at hr'
          omega
        have hreal : (b : ℝ) + m.val ≤ d := by exact_mod_cast hnat
        linarith
  have hleft := sum_indicator_lt_le b (id : Fin d → Fin d) Function.injective_id
  have hright := sum_indicator_lt_le (d := d) b Fin.rev Fin.rev_injective
  have hb' : (b : ℝ) ≤ ε * d + 1 := (Nat.ceil_lt_add_one (by positivity : 0 ≤ ε * (d : ℝ))).le
  calc
    _ ≤ ∑ m : Fin d, (B + C * (if m.val < b then 1 else 0) +
        C * (if (Fin.rev m).val < b then 1 else 0)) := sum_le_sum (fun m _ => hpoint m)
    _ = (d : ℝ) * B + C * (∑ m : Fin d, if m.val < b then 1 else 0) +
        C * (∑ m : Fin d, if (Fin.rev m).val < b then 1 else 0) := by
      simp only [sum_add_distrib, ← mul_sum, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ (d : ℝ) * B + C * b + C * b := by
      gcongr
      simpa only [id_eq] using hleft
    _ ≤ _ := by nlinarith

/-- This paper, equation (5.13).

The normalized total logarithmic norm is eventually bounded by the
bulk, boundary, and small-gap contributions, with no probabilistic hypotheses. -/
theorem average_log_prefixNormProduct_eventually_le {a : ℕ} (ha : 2 ≤ a)
    {ε δ L : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hL : 2 ≤ L) :
    ∃ K : ℕ, ∀ k ≥ K,
      (𝔼 T : {T : Tableau (a * k) (rectangle a k) // IsStandard T},
        Real.log (prefixNormProduct T.val)) / (a * k : ℕ) ≤
      (2 * ε + 2 / (a * k : ℕ)) * ((a - 1 : ℕ) * Real.log 2) +
        (a - 1 : ℕ) / (L - 1) + ((a - 1 : ℕ) * Real.log 2) * δ := by
  obtain ⟨K, hK⟩ := expect_prefixGap_uniform ha hε L hδ
  refine ⟨max K 1, ?_⟩
  intro k hk
  have hk0 : 0 < k := by omega
  have hd : (0 : ℝ) < (a * k : ℕ) := by positivity
  have hcard : 0 < Fintype.card {T : Tableau (a * k) (rectangle a k) // IsStandard T} := by
    exact_mod_cast card_standard_rectangle_pos a hk0
  have hne : (univ : Finset {T : Tableau (a * k) (rectangle a k) // IsStandard T}).Nonempty :=
    card_pos.mp (by simpa using hcard)
  let C : ℝ := (a - 1 : ℕ) * Real.log 2
  let B : ℝ := (a - 1 : ℕ) / (L - 1) + C * δ
  have hC : 0 ≤ C := mul_nonneg (by positivity) (Real.log_nonneg (by norm_num))
  have hB : 0 ≤ B := add_nonneg (div_nonneg (by positivity) (by linarith))
    (mul_nonneg hC hδ.le)
  have hsum := sum_le_of_bulk
    (fun m : Fin (a * k) => 𝔼 T : {T : Tableau (a * k) (rectangle a k) // IsStandard T},
      Real.log (prefixInsertionFactor T.val m)) hε.le hC hB
    (fun m => expect_le hne (fun T _ => log_prefixInsertionFactor_le (t := T.val) m))
    (fun m hm hl => (expect_logInsertion_le hk0 m hL).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hK k (by omega) m hm (by
        simpa only [Nat.cast_mul] using hl)).le hC)))
  have he : (𝔼 T : {T : Tableau (a * k) (rectangle a k) // IsStandard T},
      Real.log (prefixNormProduct T.val)) =
      ∑ m : Fin (a * k), 𝔼 T : {T : Tableau (a * k) (rectangle a k) // IsStandard T},
        Real.log (prefixInsertionFactor T.val m) := by
    simp_rw [show ∀ T : {T : Tableau (a * k) (rectangle a k) // IsStandard T},
      Real.log (prefixNormProduct T.val) = ∑ m, Real.log (prefixInsertionFactor T.val m)
      from fun T => log_prefixNormProduct (t := T.val)]
    exact expect_sum_comm _ _ _
  rw [he]
  calc
    _ ≤ ((a * k : ℕ) * B + (2 * ε * (a * k : ℕ) + 2) * C) / (a * k : ℕ) :=
      div_le_div_of_nonneg_right hsum hd.le
    _ = _ := by dsimp [B, C]; field_simp; ring

end BostConjecture.Specht
