/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Specht.Asymptotics.WeightedGap
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Uniform bounds for small gaps in the rectangular bulk

The probability of a small occupancy gap is bounded uniformly away
from the two ends of the tableau. The estimates separate central
occupancies from their exponentially small tails.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Specht

open Finset Filter
open scoped Topology

/-- Probability of a bounded pairwise gap under the actual weighted occupancy law. -/
def occupancyGapProbability (a M A : ℕ) (L : ℝ) : ℝ :=
  (∑ b ∈ (univ : Finset (Occupancy a M A)).filter
    (fun b => ∃ i j : Fin a, i < j ∧ |((b.val j).val : ℝ) - (b.val i).val| ≤ L),
      occupancyWeight b) / (∑ b : Occupancy a M A, occupancyWeight b)

theorem occupancyGapProbability_nonneg (a M A : ℕ) (L : ℝ) :
    0 ≤ occupancyGapProbability a M A L := by
  apply div_nonneg <;> apply sum_nonneg <;> intro b _ <;>
    exact mul_nonneg (sq_nonneg _) (occupancyMass_nonneg b)

theorem staircaseSum_pos {a : ℕ} (ha : 2 ≤ a) : 0 < staircaseSum a := by
  rw [staircaseSum_eq]
  apply Nat.div_pos _ (by decide)
  have h : 1 ≤ a - 1 := by omega
  nlinarith

/-- The finite gap estimate with every prefix-time-dependent parameter eliminated. -/
theorem occupancyGapProbability_bulk_le {a k : ℕ} (ha : 2 ≤ a) (hk : 0 < k)
    (m l : ℕ) (hml : m + l = a * k) {ε : ℝ} (hε : 0 < ε)
    (hm : ε * (a * k : ℕ) ≤ m) (hl : ε * (a * k : ℕ) ≤ l)
    (L : ℝ) {u : ℝ} (hu : 0 < u) :
    occupancyGapProbability a (k + a - 1) (m + staircaseSum a) L ≤
      (L ^ 2 * (2 * u) ^ (2 * (staircaseSum a - 1)) +
        2 * a * ((a : ℝ) * k) ^ (2 * staircaseSum a) *
          Real.exp (-u ^ 2 / (4 * (a : ℝ) ^ 2 * k))) /
      ((a.factorial : ℝ) * (∏ j ∈ range a, (j.factorial : ℝ)) *
        (ε / a) ^ (2 * staircaseSum a) * (k : ℝ) ^ staircaseSum a) := by
  have ha0 : 0 < a := by omega
  have hM : 0 < k + a - 1 := by omega
  have hA0 : 0 < m + staircaseSum a := by have := staircaseSum_pos ha; omega
  have hA : m + staircaseSum a ≤ a * (k + a - 1) := by
    rw [rectangle_occupancy_population]
    omega
  have hpop := rectangle_occupancy_population_le ha0 hk
  have hMle : (k + a - 1 : ℕ) ≤ a * k := by nlinarith
  have hAle : ((m + staircaseSum a : ℕ) : ℝ) ≤ (a : ℝ) ^ 2 * k := by
    have h := hA.trans hpop
    push_cast at h ⊢
    exact_mod_cast (by simpa only [pow_two, mul_assoc] using h)
  have hexp : Real.exp (-u ^ 2 / (4 * ((m + staircaseSum a : ℕ) : ℝ))) ≤
      Real.exp (-u ^ 2 / (4 * (a : ℝ) ^ 2 * k)) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div, neg_div]
    apply neg_le_neg
    apply div_le_div_of_nonneg_left (sq_nonneg u) (by positivity)
    nlinarith
  have hpow : ((k + a - 1 : ℕ) : ℝ) ^ (2 * staircaseSum a) ≤
      ((a : ℝ) * k) ^ (2 * staircaseSum a) :=
    pow_le_pow_left₀ (by positivity) (by exact_mod_cast hMle) _
  have hnum := add_le_add (le_refl (L ^ 2 * (2 * u) ^ (2 * (staircaseSum a - 1))))
    (mul_le_mul (mul_le_mul_of_nonneg_left hpow (show 0 ≤ 2 * (a : ℝ) by positivity)) hexp
      (Real.exp_nonneg _) (by positivity))
  have hden := sum_occupancyWeight_bulk_lower ha0 hk m l hml hε.le hm hl
  have hden0 : 0 < (a.factorial : ℝ) * (∏ j ∈ range a, (j.factorial : ℝ)) *
      (ε / a) ^ (2 * staircaseSum a) * (k : ℝ) ^ staircaseSum a := by positivity
  exact (occupancyWeight_gap_probability_le ha0 hM hA0 hA
    (hden0.trans_le hden) L hu).trans
      (div_le_div₀ (by positivity) hnum hden0 hden)

end BostConjecture.Specht
