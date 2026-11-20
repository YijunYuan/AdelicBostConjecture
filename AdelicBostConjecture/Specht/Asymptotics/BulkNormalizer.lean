/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import AdelicBostConjecture.Specht.Asymptotics.PrefixNormalizer

/-!
# Uniform bulk lower bound for the rectangular prefix normalizer

The exact binomial ratio is a quotient of rising factorials. In the bulk,
bounding each factor yields the polynomial lower bound needed for separation.
-/

@[expose] public section

noncomputable section

namespace AdelicBostConjecture.Specht

open Finset

private theorem cast_choose_add (m l : ℕ) :
    ((m + l).choose m : ℝ) =
      ((m + l).factorial : ℝ) / ((m.factorial : ℝ) * (l.factorial : ℝ)) := by
  apply (eq_div_iff (by positivity)).mpr
  have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right m l)
  rw [Nat.add_sub_cancel_left] at h
  exact_mod_cast (by simpa only [Nat.mul_assoc] using h :
    (m + l).choose m * (m.factorial * l.factorial) = (m + l).factorial)

/-- Adding the same shift to both binomial parts gives a rising-factorial ratio. -/
theorem choose_ratio_eq_ascFactorial (m l c : ℕ) :
    ((m + l).choose m : ℝ) / ((m + l + 2 * c).choose (m + c) : ℝ) =
      ((m + 1).ascFactorial c : ℝ) * ((l + 1).ascFactorial c : ℝ) /
        ((m + l + 1).ascFactorial (2 * c) : ℝ) := by
  have hs : m + l + 2 * c = (m + c) + (l + c) := by omega
  rw [cast_choose_add, hs, cast_choose_add, ← hs]
  have hf (n r : ℕ) : ((n + r).factorial : ℝ) =
      (n.factorial : ℝ) * ((n + 1).ascFactorial r : ℝ) := by
    exact_mod_cast (Nat.factorial_mul_ascFactorial n r).symm
  rw [hf (m + l) (2 * c), hf m c, hf l c]
  have hm : (m.factorial : ℝ) ≠ 0 := by positivity
  have hl : (l.factorial : ℝ) ≠ 0 := by positivity
  have hn : ((m + l).factorial : ℝ) ≠ 0 := by positivity
  field_simp

private theorem pow_le_cast_ascFactorial {x : ℝ} (hx : 0 ≤ x)
    {m : ℕ} (hm : x ≤ m + 1) (c : ℕ) :
    x ^ c ≤ ((m + 1).ascFactorial c : ℝ) := by
  rw [Nat.ascFactorial_eq_prod_range, Nat.cast_prod]
  calc
    x ^ c = ∏ _j ∈ range c, x := by simp
    _ ≤ _ := prod_le_prod₀ (fun _ _ => hx) (fun j _ => by push_cast; linarith)

/-- A factorwise lower bound for a symmetrically shifted binomial ratio. -/
theorem pow_le_choose_ratio (m l c : ℕ) {x y : ℝ} (hx : 0 ≤ x)
    (hm : x ≤ m + 1) (hl : x ≤ l + 1) (hn : (m + l + 2 * c : ℕ) ≤ y) :
    (x / y) ^ (2 * c) ≤
      ((m + l).choose m : ℝ) / ((m + l + 2 * c).choose (m + c) : ℝ) := by
  rw [choose_ratio_eq_ascFactorial]
  have hnum : x ^ (2 * c) ≤
      ((m + 1).ascFactorial c : ℝ) * ((l + 1).ascFactorial c : ℝ) := by
    simpa only [two_mul, pow_add] using mul_le_mul (pow_le_cast_ascFactorial hx hm c)
      (pow_le_cast_ascFactorial hx hl c) (pow_nonneg hx c) (by positivity)
  have hden : ((m + l + 1).ascFactorial (2 * c) : ℝ) ≤ y ^ (2 * c) := by
    calc
      _ ≤ ((m + l + 2 * c : ℕ) : ℝ) ^ (2 * c) := by
        exact_mod_cast Nat.ascFactorial_le_pow_add (m + l) (2 * c)
      _ ≤ _ := pow_le_pow_left₀ (by positivity) hn _
  simpa only [div_pow] using div_le_div₀ (by positivity) hnum (by positivity) hden

/-- The expanded occupancy population is at most `a` times the rectangle size. -/
theorem rectangle_occupancy_population_le {a k : ℕ} (ha : 0 < a) (hk : 0 < k) :
    a * (k + a - 1) ≤ a * (a * k) := by
  apply Nat.mul_le_mul_left
  have h := Nat.mul_le_mul_right (a - 1) hk
  have ha' : a - 1 + 1 = a := by omega
  have hk' : k + a - 1 + 1 = k + a := by omega
  nlinarith

/-- The polynomial factor in the normalizer has degree equal to the staircase size. -/
theorem pow_staircaseSum_le_prod (a k : ℕ) :
    (k : ℝ) ^ staircaseSum a ≤ ∏ j ∈ range a, (k + j : ℝ) ^ j := by
  have hs : staircaseSum a = ∑ j ∈ range a, j := by
    rw [staircaseSum_eq, sum_range_id]
  simpa only [hs, ← prod_pow_eq_pow_sum] using prod_le_prod₀ (fun _ _ => by positivity)
    (fun j _ => pow_le_pow_left₀ (by positivity)
      (le_add_of_nonneg_right (Nat.cast_nonneg j)) j)

/-- This paper, equation (5.11).

Uniform polynomial lower bound on the exact normalizer in the rectangular bulk. -/
theorem sum_occupancyWeight_bulk_lower {a k : ℕ} (ha : 0 < a) (hk : 0 < k)
    (m l : ℕ) (hml : m + l = a * k) {ε : ℝ} (hε : 0 ≤ ε)
    (hm : ε * (a * k : ℕ) ≤ m) (hl : ε * (a * k : ℕ) ≤ l) :
    (a.factorial : ℝ) * (∏ j ∈ range a, (j.factorial : ℝ)) *
        (ε / a) ^ (2 * staircaseSum a) * (k : ℝ) ^ staircaseSum a ≤
      ∑ b : Occupancy a (k + a - 1) (m + staircaseSum a), occupancyWeight b := by
  have ha0 : (a : ℝ) ≠ 0 := by positivity
  have hd0 : (a * k : ℝ) ≠ 0 := by positivity
  have hratio := pow_le_choose_ratio m l (staircaseSum a)
    (x := ε * (a * k : ℕ)) (y := (a : ℝ) * (a * k : ℕ))
    (by positivity) (by linarith) (by linarith) (by
      rw [hml, ← rectangle_occupancy_population]
      exact_mod_cast rectangle_occupancy_population_le ha hk)
  have hcancel : ε * (a * k : ℕ) / ((a : ℝ) * (a * k : ℕ)) = ε / a := by
    push_cast
    field_simp
  rw [hcancel, hml, ← rectangle_occupancy_population] at hratio
  rw [sum_occupancyWeight_eq_closed a hk m l hml]
  have hp := pow_staircaseSum_le_prod a k
  have hc : 0 ≤ (a.factorial : ℝ) * (∏ j ∈ range a, (j.factorial : ℝ)) := by
    positivity
  calc
    _ = ((a.factorial : ℝ) * (∏ j ∈ range a, (j.factorial : ℝ))) *
        ((k : ℝ) ^ staircaseSum a * (ε / a) ^ (2 * staircaseSum a)) := by ring
    _ ≤ ((a.factorial : ℝ) * (∏ j ∈ range a, (j.factorial : ℝ))) *
        ((∏ j ∈ range a, (k + j : ℝ) ^ j) *
          (((a * k).choose m : ℝ) /
            ((a * (k + a - 1)).choose (m + staircaseSum a) : ℝ))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul hp hratio (by positivity) (by positivity)) hc
    _ = _ := by ring

end AdelicBostConjecture.Specht
