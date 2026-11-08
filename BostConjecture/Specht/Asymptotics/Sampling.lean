/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Algebra.BigOperators.Field

/-!
# Binomial moments for sampling without replacement

Counting pairs of a sample and a distinguished subset of its successes gives
the finite moment identity needed by the labelled occupancy concentration bound.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Specht

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Removing the prescribed subset counts samples containing it. -/
theorem card_samples_containing (u : Finset α) {A : ℕ} (hu : u.card ≤ A) :
    ((univ.powersetCard A).filter fun s => u ⊆ s).card =
      (Fintype.card α - u.card).choose (A - u.card) := by
  change _ = ((univ : Finset α).card - u.card).choose (A - u.card)
  rw [← card_sdiff_of_subset (subset_univ u), ← card_powersetCard]
  apply card_bij (fun s _ => s \ u)
  · intro s hs
    obtain ⟨hs, hus⟩ := mem_filter.mp hs
    obtain ⟨_, hcard⟩ := mem_powersetCard.mp hs
    exact mem_powersetCard.mpr ⟨sdiff_subset_sdiff (subset_univ s) (Subset.refl u),
      by rw [card_sdiff_of_subset hus, hcard]⟩
  · intro s hs t ht h
    have hus := (mem_filter.mp hs).2
    have hut := (mem_filter.mp ht).2
    simpa only [sdiff_union_of_subset hus, sdiff_union_of_subset hut] using
      congrArg (fun v : Finset α => v ∪ u) h
  · intro v hv
    obtain ⟨hv, hcard⟩ := mem_powersetCard.mp hv
    have hd : Disjoint v u := disjoint_of_subset_left hv sdiff_disjoint
    refine ⟨v ∪ u, mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _, ?_⟩,
      subset_union_right⟩, ?_⟩
    · rw [card_union_of_disjoint hd, hcard, Nat.sub_add_cancel hu]
    · exact union_sdiff_cancel_right hd

/-- Double counting sample/subset incidences gives the exact binomial moments. -/
theorem sum_choose_inter (t : Finset α) {A r : ℕ} (hr : r ≤ A) :
    ∑ s ∈ univ.powersetCard A, (s ∩ t).card.choose r =
      t.card.choose r * (Fintype.card α - r).choose (A - r) := by
  have hf (s : Finset α) :
      (t.powersetCard r).filter (fun u => u ⊆ s) = (s ∩ t).powersetCard r := by
    ext u
    simp only [mem_filter, mem_powersetCard, subset_inter_iff]
    tauto
  calc
    _ = ∑ s ∈ univ.powersetCard A, ∑ u ∈ t.powersetCard r,
        if u ⊆ s then 1 else 0 := by
      apply sum_congr rfl
      intro s _
      rw [← card_powersetCard, ← hf s]
      simp
    _ = ∑ u ∈ t.powersetCard r, ∑ s ∈ univ.powersetCard A,
        if u ⊆ s then 1 else 0 := sum_comm
    _ = ∑ u ∈ t.powersetCard r, (Fintype.card α - r).choose (A - r) := by
      apply sum_congr rfl
      intro u hu
      have hc := (mem_powersetCard.mp hu).2
      have h := card_samples_containing u (hc ▸ hr)
      simpa only [hc, card_filter] using h
    _ = _ := by simp

/-- The normalized incidence count is the usual falling-factorial moment. -/
theorem sampling_binomialMoment_eq (t : Finset α) {A r : ℕ}
    (hA : A ≤ Fintype.card α) (hr : r ≤ A) :
    (∑ s ∈ univ.powersetCard A, ((s ∩ t).card.choose r : ℝ)) /
        ((Fintype.card α).choose A : ℝ) =
      (A.choose r : ℝ) * (t.card.descFactorial r : ℝ) /
        ((Fintype.card α).descFactorial r : ℝ) := by
  have hs : (∑ s ∈ univ.powersetCard A, ((s ∩ t).card.choose r : ℝ)) =
      (t.card.choose r : ℝ) * ((Fintype.card α - r).choose (A - r) : ℝ) := by
    exact_mod_cast sum_choose_inter t hr
  rw [hs, Nat.descFactorial_eq_factorial_mul_choose,
    Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  have hNA : ((Fintype.card α).choose A : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hA).ne'
  have hNr : ((Fintype.card α).choose r : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (hr.trans hA)).ne'
  have hrf : (r.factorial : ℝ) ≠ 0 := by positivity
  have hc : ((Fintype.card α).choose A : ℝ) * (A.choose r : ℝ) =
      ((Fintype.card α).choose r : ℝ) *
        ((Fintype.card α - r).choose (A - r) : ℝ) := by
    exact_mod_cast Nat.choose_mul (n := Fintype.card α) hr
  field_simp
  nlinarith [hc]

/-- Sampling without replacement reduces every normalized factorial moment. -/
theorem descFactorial_ratio_le_pow {M N r : ℕ} (hN : 0 < N)
    (hM : M ≤ N) (hr : r ≤ N) :
    (M.descFactorial r : ℝ) / (N.descFactorial r : ℝ) ≤ (M / N : ℝ) ^ r := by
  by_cases hMr : r ≤ M
  · rw [Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_prod_range,
      Nat.cast_prod, Nat.cast_prod, ← prod_div_distrib]
    calc
      _ ≤ ∏ _j ∈ range r, (M / N : ℝ) := by
        apply prod_le_prod₀ (fun _ _ => by positivity)
        intro j hj
        have hjr := mem_range.mp hj
        have hjM : j ≤ M := by omega
        have hjN : j < N := by omega
        have hd : (0 : ℝ) < (N - j : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hjN
        apply (div_le_div_iff₀ hd (by positivity)).mpr
        rw [Nat.cast_sub hjM, Nat.cast_sub hjN.le]
        have hMN : (M : ℝ) ≤ N := by exact_mod_cast hM
        nlinarith [mul_nonneg (Nat.cast_nonneg j) (sub_nonneg.mpr hMN)]
      _ = _ := by simp [div_pow]
  · rw [Nat.descFactorial_of_lt (Nat.lt_of_not_ge hMr), Nat.cast_zero, zero_div]
    positivity

/-- Binomial moments of an actual uniform subset are bounded by Bernoulli moments. -/
theorem sampling_binomialMoment_le (t : Finset α) {A r : ℕ}
    (hN : 0 < Fintype.card α) (hA : A ≤ Fintype.card α) (hr : r ≤ A) :
    (∑ s ∈ univ.powersetCard A, ((s ∩ t).card.choose r : ℝ)) /
        ((Fintype.card α).choose A : ℝ) ≤
      (A.choose r : ℝ) * (t.card / Fintype.card α : ℝ) ^ r := by
  simpa only [sampling_binomialMoment_eq t hA hr, mul_div_assoc] using mul_le_mul_of_nonneg_left
    (descFactorial_ratio_le_pow hN (card_le_univ t) (hr.trans hA)) (by positivity)

private theorem one_add_pow_eq_sum_choose (z : ℝ) {b A : ℕ} (hb : b ≤ A) :
    (1 + z) ^ b = ∑ r ∈ range (A + 1), (b.choose r : ℝ) * z ^ r := by
  calc
    _ = ∑ r ∈ range (b + 1), (b.choose r : ℝ) * z ^ r := by
      rw [add_comm, add_pow]
      simp only [one_pow, mul_one, mul_comm]
    _ = _ := sum_subset (range_mono (Nat.add_le_add_right hb 1)) (by
      intro r _ hr
      have hbr : b < r := by simp only [mem_range] at hr; omega
      simp [Nat.choose_eq_zero_of_lt hbr])

/-- The generating function of an actual sample is bounded by that of independent trials. -/
theorem sampling_one_add_pow_le (t : Finset α) {A : ℕ}
    (hN : 0 < Fintype.card α) (hA : A ≤ Fintype.card α) {z : ℝ} (hz : 0 ≤ z) :
    (∑ s ∈ univ.powersetCard A, (1 + z) ^ (s ∩ t).card) /
        ((Fintype.card α).choose A : ℝ) ≤
      (1 + (t.card / Fintype.card α : ℝ) * z) ^ A := by
  have he : (∑ s ∈ univ.powersetCard A, (1 + z) ^ (s ∩ t).card) =
      ∑ r ∈ range (A + 1),
        (∑ s ∈ univ.powersetCard A, ((s ∩ t).card.choose r : ℝ)) * z ^ r := by
    calc
      _ = ∑ s ∈ univ.powersetCard A, ∑ r ∈ range (A + 1),
          ((s ∩ t).card.choose r : ℝ) * z ^ r := by
        apply sum_congr rfl
        intro s hs
        apply one_add_pow_eq_sum_choose
        exact (card_le_card inter_subset_left).trans_eq (mem_powersetCard.mp hs).2
      _ = _ := by rw [sum_comm]; simp_rw [sum_mul]
  rw [he, sum_div, one_add_pow_eq_sum_choose _ (le_refl A)]
  apply sum_le_sum
  intro r hr
  have hrA : r ≤ A := by simpa using mem_range.mp hr
  calc
    _ = ((∑ s ∈ univ.powersetCard A, ((s ∩ t).card.choose r : ℝ)) /
        ((Fintype.card α).choose A : ℝ)) * z ^ r := by ring
    _ ≤ ((A.choose r : ℝ) * (t.card / Fintype.card α : ℝ) ^ r) * z ^ r :=
      mul_le_mul_of_nonneg_right (sampling_binomialMoment_le t hN hA hrA)
        (pow_nonneg hz r)
    _ = _ := by rw [mul_pow]; ring

/-- Positive-parameter moment-generating bound for a finite sample. -/
theorem sampling_exp_le_of_nonneg (t : Finset α) {A : ℕ}
    (hN : 0 < Fintype.card α) (hA : A ≤ Fintype.card α) {θ : ℝ} (hθ : 0 ≤ θ) :
    (∑ s ∈ univ.powersetCard A, Real.exp ((s ∩ t).card * θ)) /
        ((Fintype.card α).choose A : ℝ) ≤
      (1 + (t.card / Fintype.card α : ℝ) * (Real.exp θ - 1)) ^ A := by
  have h := sampling_one_add_pow_le t hN hA
    (z := Real.exp θ - 1) (sub_nonneg.mpr (Real.one_le_exp_iff.mpr hθ))
  simpa only [add_sub_cancel, Real.exp_nat_mul] using h

/-- The same Bernoulli bound holds for negative parameters by complementing successes. -/
theorem sampling_exp_le (t : Finset α) {A : ℕ}
    (hN : 0 < Fintype.card α) (hA : A ≤ Fintype.card α) (θ : ℝ) :
    (∑ s ∈ univ.powersetCard A, Real.exp ((s ∩ t).card * θ)) /
        ((Fintype.card α).choose A : ℝ) ≤
      (1 + (t.card / Fintype.card α : ℝ) * (Real.exp θ - 1)) ^ A := by
  by_cases hθ : 0 ≤ θ
  · exact sampling_exp_le_of_nonneg t hN hA hθ
  have h := sampling_exp_le_of_nonneg (univ \ t) hN hA (neg_nonneg.mpr (le_of_not_ge hθ))
  have he (s : Finset α) (hs : s ∈ univ.powersetCard A) :
      Real.exp ((s ∩ t).card * θ) =
        Real.exp (A * θ) * Real.exp ((s ∩ (univ \ t)).card * -θ) := by
    have hset : s ∩ (univ \ t) = s \ t := by ext x; simp
    have hc : (s ∩ t).card + (s ∩ (univ \ t)).card = A := by
      rw [hset, add_comm, card_sdiff_add_card_inter, (mem_powersetCard.mp hs).2]
    rw [← Real.exp_add]
    congr 1
    have hc' : ((s ∩ t).card : ℝ) + ((s ∩ (univ \ t)).card : ℝ) = A := by
      exact_mod_cast hc
    nlinarith
  have hbase : Real.exp θ *
      (1 + ((univ \ t).card / Fintype.card α : ℝ) * (Real.exp (-θ) - 1)) =
      1 + (t.card / Fintype.card α : ℝ) * (Real.exp θ - 1) := by
    rw [card_sdiff_of_subset (subset_univ t), card_univ,
      Nat.cast_sub (card_le_univ t), Real.exp_neg]
    have hn : (Fintype.card α : ℝ) ≠ 0 := by positivity
    have hexp : Real.exp θ ≠ 0 := (Real.exp_pos θ).ne'
    field_simp
    ring
  calc
    _ = Real.exp (A * θ) *
        ((∑ s ∈ univ.powersetCard A, Real.exp ((s ∩ (univ \ t)).card * -θ)) /
          ((Fintype.card α).choose A : ℝ)) := by
      rw [← mul_div_assoc, mul_sum]
      congr 1
      exact sum_congr rfl he
    _ ≤ Real.exp (A * θ) *
        (1 + ((univ \ t).card / Fintype.card α : ℝ) * (Real.exp (-θ) - 1)) ^ A :=
      mul_le_mul_of_nonneg_left h (Real.exp_nonneg _)
    _ = _ := by rw [Real.exp_nat_mul, ← mul_pow, hbase]

end BostConjecture.Specht
