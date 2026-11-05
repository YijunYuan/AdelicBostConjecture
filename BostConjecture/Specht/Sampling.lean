module

public import BostConjecture.Specht.Hypergeometric
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

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
    have he := congrArg (fun v : Finset α => v ∪ u) h
    simpa only [sdiff_union_of_subset hus, sdiff_union_of_subset hut] using he
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
  rw [sampling_binomialMoment_eq t hA hr, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left
    (descFactorial_ratio_le_pow hN (card_le_univ t) (hr.trans hA)) (by positivity)

end BostConjecture.Specht
