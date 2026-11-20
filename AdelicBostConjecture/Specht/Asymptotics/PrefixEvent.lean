/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import AdelicBostConjecture.Specht.Asymptotics.BulkGap

/-!
# Symmetric observables and gap events of the actual tableau prefix law
-/

@[expose] public section

noncomputable section

namespace AdelicBostConjecture.Specht

open OAI.Saxl Finset

/-- This paper, equation (5.10).

Exact transport of every symmetric observable from uniform tableaux to
the labelled squared-Vandermonde occupancy law. -/
theorem rectanglePrefix_average_eq_weighted (a : ℕ) {k : ℕ} (hk : 0 < k)
    (m l : ℕ) (hml : m + l = a * k)
    (f : Occupancy a (k + a - 1) (m + staircaseSum a) → ℝ)
    (hf : ∀ b σ, f (occupancyPerm b σ) = f b) :
    (∑ T : {T : Tableau (m + l) (rectangle a k) // IsStandard T},
      f (rectangleShapeOccupancy (rectanglePrefixShape a k m l T)).val) /
      (Fintype.card {T : Tableau (m + l) (rectangle a k) // IsStandard T} : ℝ) =
    (∑ b, occupancyWeight b * f b) /
      (∑ b : Occupancy a (k + a - 1) (m + staircaseSum a), occupancyWeight b) := by
  classical
  have hfiber := (Equiv.sigmaFiberEquiv (rectanglePrefixShape a k m l)).sum_comp
    (fun T => f (rectangleShapeOccupancy (rectanglePrefixShape a k m l T)).val)
  change (∑ x : (Σ μ : RectangleShape a k m,
      {T // rectanglePrefixShape a k m l T = μ}),
      f (rectangleShapeOccupancy (rectanglePrefixShape a k m l x.2.val)).val) = _ at hfiber
  rw [Fintype.sum_sigma] at hfiber
  simp_rw [show ∀ (μ : RectangleShape a k m)
      (T : {T // rectanglePrefixShape a k m l T = μ}),
      rectanglePrefixShape a k m l T.val = μ from fun _ T => T.property] at hfiber
  simp only [sum_const, card_univ, nsmul_eq_mul] at hfiber
  have hcard (μ : RectangleShape a k m) :
      Fintype.card {T // rectanglePrefixShape a k m l T = μ} =
      Nat.card {T : {T : Tableau (m + l) (rectangle a k) // IsStandard T} //
        prefixShape T.val m (Nat.le_add_right m l) = μ.val} := by
    simp only [rectanglePrefixShape, Subtype.ext_iff, Nat.card_eq_fintype_card]
  simp_rw [hcard] at hfiber
  rw [← hfiber, sum_div]
  have hsort := sum_occupancy_eq_factorial_mul_sorted (fun b => occupancyWeight b * f b)
    (fun b σ => by rw [occupancyWeight_perm, hf])
    (fun b hb => by rw [occupancyWeight_eq_zero_of_not_injective b hb, zero_mul])
  rw [hsort, ← (rectangleShapeEquivSortedOccupancy a k m).sum_comp]
  change _ = (a.factorial : ℝ) *
    (∑ μ : RectangleShape a k m, occupancyWeight (rectangleShapeOccupancy μ).val *
      f (rectangleShapeOccupancy μ).val) / _
  rw [mul_sum, sum_div]
  apply sum_congr rfl
  intro μ _
  have hp := rectanglePrefix_probability_eq_weighted a hk m l hml μ
  calc
    _ = ((Nat.card {T : {T : Tableau (m + l) (rectangle a k) // IsStandard T} //
          prefixShape T.val m (Nat.le_add_right m l) = μ.val} : ℝ) /
        (Fintype.card {T : Tableau (m + l) (rectangle a k) // IsStandard T} : ℝ)) *
          f (rectangleShapeOccupancy μ).val := by ring
    _ = _ := by rw [hp]; ring

/-- A small absolute gap, expressed using each unordered pair once. -/
def HasSmallGap {a : ℕ} (x : Fin a → ℝ) (L : ℝ) : Prop :=
  ∃ i j : Fin a, i < j ∧ |x j - x i| ≤ L

theorem hasSmallGap_perm_iff {a : ℕ} (x : Fin a → ℝ) (L : ℝ)
    (σ : Equiv.Perm (Fin a)) : HasSmallGap (x ∘ σ) L ↔ HasSmallGap x L := by
  have h (x : Fin a → ℝ) (σ : Equiv.Perm (Fin a)) :
      HasSmallGap (x ∘ σ) L → HasSmallGap x L := by
    rintro ⟨i, j, hij, hgap⟩
    rcases lt_or_gt_of_ne (σ.injective.ne hij.ne) with hσ | hσ
    · exact ⟨σ i, σ j, hσ, hgap⟩
    · exact ⟨σ j, σ i, hσ, by simpa only [Function.comp_apply, abs_sub_comm] using hgap⟩
  constructor
  · exact h x σ
  · intro hx
    have he : (x ∘ σ) ∘ σ.symm = x := by ext i; simp
    exact h (x ∘ σ) σ.symm (he.symm ▸ hx)

/-- The small-gap probability for the prefix of an actual uniform standard tableau. -/
def rectanglePrefixGapProbability (a k m l : ℕ) (L : ℝ) : ℝ := by
  classical
  exact (∑ T : {T : Tableau (m + l) (rectangle a k) // IsStandard T},
    if HasSmallGap (fun i : Fin a =>
      (shiftedRowLength (rectanglePrefixShape a k m l T).val a i.val : ℝ)) L
      then 1 else 0) /
    (Fintype.card {T : Tableau (m + l) (rectangle a k) // IsStandard T} : ℝ)

/-- The symmetric bad-gap event has exactly the actual weighted occupancy probability. -/
theorem rectanglePrefixGapProbability_eq (a : ℕ) {k : ℕ} (hk : 0 < k)
    (m l : ℕ) (hml : m + l = a * k) (L : ℝ) :
    rectanglePrefixGapProbability a k m l L =
      occupancyGapProbability a (k + a - 1) (m + staircaseSum a) L := by
  classical
  have h := rectanglePrefix_average_eq_weighted a hk m l hml
    (fun b => if HasSmallGap (fun i => ((b.val i).val : ℝ)) L then 1 else 0)
    (fun b σ => by
      change (if HasSmallGap ((fun i => ((b.val i).val : ℝ)) ∘ σ) L then 1 else 0) = _
      rw [hasSmallGap_perm_iff])
  have hpoint (b : Occupancy a (k + a - 1) (m + staircaseSum a)) :
      occupancyWeight b *
          (if HasSmallGap (fun i => ((b.val i).val : ℝ)) L then 1 else 0) =
        (if HasSmallGap (fun i => ((b.val i).val : ℝ)) L then occupancyWeight b else 0) := by
    split_ifs <;> simp
  simp_rw [hpoint] at h
  calc
    _ = (∑ b : Occupancy a (k + a - 1) (m + staircaseSum a),
        if HasSmallGap (fun i => ((b.val i).val : ℝ)) L then occupancyWeight b else 0) /
        (∑ b : Occupancy a (k + a - 1) (m + staircaseSum a), occupancyWeight b) := by
      convert h using 1
      simp only [rectanglePrefixGapProbability, rectangleShapeOccupancy_apply]
      congr 1
    _ = _ := by
      unfold occupancyGapProbability
      rw [sum_filter]
      congr 1
      apply sum_congr rfl
      intro b _
      unfold HasSmallGap
      split_ifs <;> rfl

end AdelicBostConjecture.Specht
