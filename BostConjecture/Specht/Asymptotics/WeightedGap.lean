/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Specht.Asymptotics.BulkNormalizer
public import BostConjecture.Specht.Asymptotics.OccupancyMGF

/-!
# Small gaps under squared Vandermonde weighting

The actual labelled occupancy law has small weighted mass on collisions or
bounded gaps: isolate a small Vandermonde factor in the central region and
use the checked simultaneous concentration estimate on its complement.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Specht

open Finset

/-- Ordered pairs of distinct row indices, with the smaller index first. -/
private def gapPairs (a : ℕ) : Finset ((_i : Fin a) × Fin a) :=
  univ.sigma fun i => Ioi i

private theorem card_gapPairs (a : ℕ) : (gapPairs a).card = staircaseSum a := by
  simp only [gapPairs, card_sigma, Fin.card_Ioi, staircaseSum]
  apply sum_congr rfl
  intro i _
  omega

private theorem vandermonde_sq_eq_prod {a : ℕ} (x : Fin a → ℝ) :
    (Matrix.vandermonde x).det ^ 2 =
      ∏ p ∈ gapPairs a, (x p.2 - x p.1) ^ 2 := by
  simp only [gapPairs, prod_sigma, Matrix.det_vandermonde, prod_pow]

/-- A uniform pairwise gap bound controls the squared Vandermonde. -/
theorem vandermonde_sq_le_pow {a : ℕ} (x : Fin a → ℝ) {D : ℝ}
    (hx : ∀ i j, i < j → |x j - x i| ≤ D) :
    (Matrix.vandermonde x).det ^ 2 ≤ D ^ (2 * staircaseSum a) := by
  rw [vandermonde_sq_eq_prod]
  calc
    _ ≤ ∏ _p ∈ gapPairs a, D ^ 2 := prod_le_prod₀
      (fun _ _ => sq_nonneg _) (fun p hp => by
        have hp' : p.1 < p.2 := (mem_sigma.mp hp).2 |> mem_Ioi.mp
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hx _ _ hp') 2)
    _ = _ := by rw [prod_const, card_gapPairs, ← pow_mul]

/-- Isolating one small pairwise gap saves one squared Vandermonde factor. -/
theorem vandermonde_sq_le_of_gap {a : ℕ} (x : Fin a → ℝ) {D L : ℝ}
    (hx : ∀ i j, i < j → |x j - x i| ≤ D)
    (hgap : ∃ i j, i < j ∧ |x j - x i| ≤ L) :
    (Matrix.vandermonde x).det ^ 2 ≤ L ^ 2 * D ^ (2 * (staircaseSum a - 1)) := by
  obtain ⟨i, j, hij, hgap⟩ := hgap
  let p : (i : Fin a) × Fin a := ⟨i, j⟩
  have hp : p ∈ gapPairs a := by simp [gapPairs, p, hij]
  rw [vandermonde_sq_eq_prod, ← mul_prod_erase _ _ hp]
  have hsmall : (x j - x i) ^ 2 ≤ L ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hgap 2
  have hrest : (∏ q ∈ (gapPairs a).erase p, (x q.2 - x q.1) ^ 2) ≤
      D ^ (2 * (staircaseSum a - 1)) := by
    calc
      _ ≤ ∏ _q ∈ (gapPairs a).erase p, D ^ 2 := prod_le_prod₀
        (fun _ _ => sq_nonneg _) (fun q hq => by
          have hq' : q.1 < q.2 := (mem_sigma.mp (mem_of_mem_erase hq)).2 |> mem_Ioi.mp
          simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hx _ _ hq') 2)
      _ = _ := by rw [prod_const, card_erase_of_mem hp, card_gapPairs, ← pow_mul]
  exact mul_le_mul hsmall hrest (prod_nonneg fun _ _ => sq_nonneg _) (sq_nonneg L)

/-- On the occupancy box every pairwise gap is at most the block size. -/
theorem occupancy_vandermonde_sq_le {a M A : ℕ} (b : Occupancy a M A) :
    (Matrix.vandermonde (fun i => ((b.val i).val : ℝ))).det ^ 2 ≤
      (M : ℝ) ^ (2 * staircaseSum a) := by
  apply vandermonde_sq_le_pow
  intro i j _
  have hi : ((b.val i).val : ℝ) ≤ M := by exact_mod_cast Nat.le_of_lt_succ (b.val i).isLt
  have hj : ((b.val j).val : ℝ) ≤ M := by exact_mod_cast Nat.le_of_lt_succ (b.val j).isLt
  have hi0 : (0 : ℝ) ≤ (b.val i).val := by positivity
  have hj0 : (0 : ℝ) ≤ (b.val j).val := by positivity
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The unnormalized Vandermonde-weighted mass of bounded coordinate gaps. -/
theorem sum_occupancyWeight_gap_le {a M A : ℕ} (ha : 0 < a) (hM : 0 < M)
    (hA0 : 0 < A) (hA : A ≤ a * M) (L : ℝ) {u : ℝ} (hu : 0 < u) :
    ∑ b ∈ (univ : Finset (Occupancy a M A)).filter
        (fun b => ∃ i j : Fin a, i < j ∧ |((b.val j).val : ℝ) - (b.val i).val| ≤ L),
        occupancyWeight b ≤
      L ^ 2 * (2 * u) ^ (2 * (staircaseSum a - 1)) +
        2 * a * (M : ℝ) ^ (2 * staircaseSum a) * Real.exp (-u ^ 2 / (4 * (A : ℝ))) := by
  classical
  let C := L ^ 2 * (2 * u) ^ (2 * (staircaseSum a - 1))
  let D := (M : ℝ) ^ (2 * staircaseSum a)
  let E (b : Occupancy a M A) := ∃ i : Fin a, u ≤ |((b.val i).val : ℝ) - A / a|
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hpoint (b : Occupancy a M A) :
      (if ∃ i j : Fin a, i < j ∧ |((b.val j).val : ℝ) - (b.val i).val| ≤ L
        then occupancyWeight b else 0) ≤
      C * occupancyMass b + D * (if E b then occupancyMass b else 0) := by
    by_cases hb : ∃ i j : Fin a, i < j ∧ |((b.val j).val : ℝ) - (b.val i).val| ≤ L
    · simp only [hb, ↓reduceIte]
      by_cases he : E b
      · simp only [he, ↓reduceIte]
        exact (mul_le_mul_of_nonneg_right (occupancy_vandermonde_sq_le b)
          (occupancyMass_nonneg b)).trans
            (le_add_of_nonneg_left (mul_nonneg hC (occupancyMass_nonneg b)))
      · simp only [he, ↓reduceIte, mul_zero, add_zero]
        apply mul_le_mul_of_nonneg_right _ (occupancyMass_nonneg b)
        apply vandermonde_sq_le_of_gap _ _ hb
        intro i j _
        have hi : |((b.val i).val : ℝ) - A / a| < u := lt_of_not_ge (fun h => he ⟨i, h⟩)
        have hj : |((b.val j).val : ℝ) - A / a| < u := lt_of_not_ge (fun h => he ⟨j, h⟩)
        calc
          _ = |(((b.val j).val : ℝ) - A / a) - (((b.val i).val : ℝ) - A / a)| := by congr 1; ring
          _ ≤ |((b.val j).val : ℝ) - A / a| + |((b.val i).val : ℝ) - A / a| := abs_sub _ _
          _ ≤ 2 * u := by linarith
    · simp only [hb, ↓reduceIte]
      exact add_nonneg (mul_nonneg hC (occupancyMass_nonneg b))
        (mul_nonneg hD (by split_ifs <;> simp [occupancyMass_nonneg]))
  calc
    _ ≤ ∑ b : Occupancy a M A,
        (C * occupancyMass b + D * (if E b then occupancyMass b else 0)) := by
      simpa only [sum_filter] using sum_le_sum (fun b _ => hpoint b)
    _ = C + D * ∑ b ∈ (univ : Finset (Occupancy a M A)).filter E,
        occupancyMass b := by
      rw [sum_add_distrib, ← mul_sum, ← mul_sum, sum_occupancyMass hA, mul_one, sum_filter]
    _ ≤ C + D * (2 * a * Real.exp (-u ^ 2 / (4 * (A : ℝ)))) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (occupancyMass_max_concentration ha hM hA0 hA hu) hD)
    _ = _ := by dsimp [C, D]; ring

/-- Finite bad-gap bound for the normalized squared-Vandermonde occupancy law. -/
theorem occupancyWeight_gap_probability_le {a M A : ℕ} (ha : 0 < a) (hM : 0 < M)
    (hA0 : 0 < A) (hA : A ≤ a * M)
    (hZ : 0 < ∑ b : Occupancy a M A, occupancyWeight b) (L : ℝ) {u : ℝ} (hu : 0 < u) :
    (∑ b ∈ (univ : Finset (Occupancy a M A)).filter
        (fun b => ∃ i j : Fin a, i < j ∧ |((b.val j).val : ℝ) - (b.val i).val| ≤ L),
        occupancyWeight b) / (∑ b : Occupancy a M A, occupancyWeight b) ≤
      (L ^ 2 * (2 * u) ^ (2 * (staircaseSum a - 1)) +
        2 * a * (M : ℝ) ^ (2 * staircaseSum a) * Real.exp (-u ^ 2 / (4 * (A : ℝ)))) /
      (∑ b : Occupancy a M A, occupancyWeight b) :=
  div_le_div_of_nonneg_right (sum_occupancyWeight_gap_le ha hM hA0 hA L hu) hZ.le

end BostConjecture.Specht
