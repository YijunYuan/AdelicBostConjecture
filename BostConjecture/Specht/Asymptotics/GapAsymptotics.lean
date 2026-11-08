/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Decay of the central and tail bounds for small gaps

The explicit central and tail bounds tend to zero as the rectangle
width grows with fixed height. These analytic limits complete the
probabilistic gap estimate in Section 5 of this paper.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Specht

open Filter
open scoped Topology

/-- Any positive power in an exponential dominates every polynomial power. -/
theorem tendsto_rpow_mul_exp_neg_rpow (p : ℝ) {q b : ℝ} (hq : 0 < q) (hb : 0 < b) :
    Tendsto (fun x : ℝ => x ^ p * Real.exp (-b * x ^ q)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (p / q) b hb).comp
    (tendsto_rpow_atTop hq)
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  dsimp
  rw [← Real.rpow_mul hx, mul_div_cancel₀ _ hq.ne']

/-- The explicit central-plus-tail majorant tends to zero for a suitable cutoff power. -/
theorem tendsto_gap_majorant {a c : ℕ} (ha : 0 < a)
    {C : ℝ} (hC : 0 < C) (L : ℝ) {r : ℝ}
    (hr : 1 / 2 < r) (hrc : r * (2 * (c - 1 : ℕ)) < c) :
    Tendsto (fun x : ℝ =>
      (L ^ 2 * (2 * x ^ r) ^ (2 * (c - 1)) +
        2 * a * ((a : ℝ) * x) ^ (2 * c) *
          Real.exp (-(x ^ r) ^ 2 / (4 * (a : ℝ) ^ 2 * x))) /
      (C * x ^ c)) atTop (𝓝 0) := by
  have haR : (0 : ℝ) < a := by positivity
  have hq : 0 < 2 * r - 1 := by linarith
  have hcentral : Tendsto (fun x : ℝ => x ^ (r * (2 * (c - 1 : ℕ)) - c))
      atTop (𝓝 0) := by
    simpa only [neg_sub] using tendsto_rpow_neg_atTop (sub_pos.mpr hrc)
  have htail := tendsto_rpow_mul_exp_neg_rpow (c : ℝ) hq
    (show (0 : ℝ) < 1 / (4 * (a : ℝ) ^ 2) by positivity)
  have h := (hcentral.const_mul (L ^ 2 * 2 ^ (2 * (c - 1)) / C)).add
    (htail.const_mul (2 * a * (a : ℝ) ^ (2 * c) / C))
  simp only [mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hx0 : x ≠ 0 := hx.ne'
  have hC0 : C ≠ 0 := hC.ne'
  have ha0 : (a : ℝ) ≠ 0 := haR.ne'
  have hcentral_eq : x ^ (r * (2 * (c - 1 : ℕ)) - c) =
      (x ^ r) ^ (2 * (c - 1)) / x ^ c := by
    rw [Real.rpow_sub_natCast hx0, ← Real.rpow_mul_natCast hx.le]
    norm_cast
  have hexponent : -(x ^ r) ^ 2 / (4 * (a : ℝ) ^ 2 * x) =
      -(1 / (4 * (a : ℝ) ^ 2)) * x ^ (2 * r - 1) := by
    rw [Real.rpow_sub_one hx0, ← Real.rpow_mul_natCast hx.le]
    norm_num only [Nat.cast_ofNat]
    rw [mul_comm r 2]
    field_simp
  rw [hcentral_eq, hexponent, Real.rpow_natCast, mul_pow, mul_pow]
  have hpow : x ^ (2 * c) = x ^ c * x ^ c := by rw [two_mul, pow_add]
  rw [hpow]
  field_simp

/-- The cutoff in this paper grows faster than a square root while leaving a negative
central exponent after division by the normalizer. -/
theorem gap_cutoff_exponent {c : ℕ} (hc : 0 < c) :
    1 / 2 < (1 / 2 + 1 / (4 * (c : ℝ))) ∧
      (1 / 2 + 1 / (4 * (c : ℝ))) * (2 * (c - 1 : ℕ)) < c := by
  have hcR : (0 : ℝ) < c := by positivity
  constructor
  · have : (0 : ℝ) < 1 / (4 * (c : ℝ)) := by positivity
    linarith
  · rw [Nat.cast_sub (by omega : 1 ≤ c), Nat.cast_one]
    apply (mul_lt_mul_iff_of_pos_right (show (0 : ℝ) < 4 * c by positivity)).mp
    field_simp
    nlinarith

end BostConjecture.Specht
