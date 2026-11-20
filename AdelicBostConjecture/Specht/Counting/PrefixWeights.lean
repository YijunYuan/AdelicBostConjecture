/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import AdelicBostConjecture.Specht.Counting.PrefixCount
public import AdelicBostConjecture.Specht.Counting.ComplementCount

/-!
# Exact binomial weights of rectangular prefix fibers

The concrete prefix count is a shape-independent constant times the square
of the shifted Vandermonde and a product of binomial coefficients.
-/

@[expose] public section

noncomputable section

namespace AdelicBostConjecture.Specht

open OAI.Saxl Finset

variable {μ : YoungDiagram} {a k m l : ℕ}

private theorem height_le_rectangle (hμ : μ ≤ rectangle a k) : μ.colLen 0 ≤ a := by
  by_contra h
  have hm : (a, 0) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
  have := (mem_rectangle.mp (hμ hm)).1
  omega

/-- The actual prefix count times its two factorial denominators is the squared
Vandermonde numerator. -/
theorem card_rectanglePrefix_mul_factorials (hμ : μ ≤ rectangle a k)
    (hm : μ.card = m) (hl : (rectangleComplement μ a k).card = l) :
    Nat.card {T : {T : Tableau (m + l) (rectangle a k) // IsStandard T} //
      prefixShape T.val m (Nat.le_add_right m l) = μ} *
      (∏ r ∈ range a, (shiftedRowLength μ a r).factorial *
        (k + a - 1 - shiftedRowLength μ a r).factorial) =
    m.factorial * l.factorial *
      (∏ r ∈ range a, ∏ j ∈ Ioo r a,
        (shiftedRowLength μ a r - shiftedRowLength μ a j)) ^ 2 := by
  have ht := card_standard_mul_shiftedFactorials μ hm (height_le_rectangle hμ)
  have hu := card_standard_mul_shiftedFactorials (rectangleComplement μ a k) hl
    (height_le_rectangle (rectangleComplement_le μ a k))
  rw [shiftedFactorials_rectangleComplement hμ, shiftedVandermonde_rectangleComplement hμ] at hu
  rw [card_rectanglePrefix hμ, prod_mul_distrib]
  calc
    _ = (Fintype.card {t : Tableau m μ // IsStandard t} *
        (∏ r ∈ range a, (shiftedRowLength μ a r).factorial)) *
        (Fintype.card {u : Tableau l (rectangleComplement μ a k) // IsStandard u} *
        (∏ r ∈ range a, (k + a - 1 - shiftedRowLength μ a r).factorial)) := by ring
    _ = _ := by rw [ht, hu]; ring

/-- Factorial form of the exact squared-Vandermonde binomial weight. -/
theorem card_rectanglePrefix_mul_factorial_pow (hμ : μ ≤ rectangle a k)
    (hm : μ.card = m) (hl : (rectangleComplement μ a k).card = l) :
    Nat.card {T : {T : Tableau (m + l) (rectangle a k) // IsStandard T} //
      prefixShape T.val m (Nat.le_add_right m l) = μ} *
        (k + a - 1).factorial ^ a =
    (m.factorial * l.factorial *
      (∏ r ∈ range a, ∏ j ∈ Ioo r a,
        (shiftedRowLength μ a r - shiftedRowLength μ a j)) ^ 2) *
      (∏ r ∈ range a, (k + a - 1).choose (shiftedRowLength μ a r)) := by
  have hbin :
      (∏ r ∈ range a, (k + a - 1).choose (shiftedRowLength μ a r)) *
      (∏ r ∈ range a, (shiftedRowLength μ a r).factorial *
        (k + a - 1 - shiftedRowLength μ a r).factorial) = (k + a - 1).factorial ^ a := by
    rw [← prod_mul_distrib]
    calc
      _ = ∏ _r ∈ range a, (k + a - 1).factorial := by
        apply prod_congr rfl
        intro r _
        rw [← mul_assoc]
        apply Nat.choose_mul_factorial_mul_factorial
        have hb := rowLen_le_of_le_rectangle (r := r) hμ
        unfold shiftedRowLength
        omega
      _ = _ := by simp
  rw [← hbin]
  calc
    _ = (Nat.card {T : {T : Tableau (m + l) (rectangle a k) // IsStandard T} //
      prefixShape T.val m (Nat.le_add_right m l) = μ} *
      (∏ r ∈ range a, (shiftedRowLength μ a r).factorial *
        (k + a - 1 - shiftedRowLength μ a r).factorial)) *
      (∏ r ∈ range a, (k + a - 1).choose (shiftedRowLength μ a r)) := by ring
    _ = _ := by rw [card_rectanglePrefix_mul_factorials hμ hm hl]

end AdelicBostConjecture.Specht
