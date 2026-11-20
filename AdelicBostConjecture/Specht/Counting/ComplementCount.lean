/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import AdelicBostConjecture.Specht.Tableau.Complement
public import AdelicBostConjecture.Specht.Counting.ShiftedCount

/-!
# Shifted coordinates of rectangular complements

Complementation reverses the shifted coordinates and subtracts them from
`k + a - 1`. In particular its Vandermonde product is unchanged.
-/

@[expose] public section

noncomputable section

namespace AdelicBostConjecture.Specht

open OAI.Saxl Finset

variable {μ : YoungDiagram} {a k : ℕ}

/-- Shifted complementary coordinates are reflected in `k + a - 1`. -/
theorem shiftedRowLength_rectangleComplement (hμ : μ ≤ rectangle a k) {r : ℕ}
    (hr : r < a) :
    shiftedRowLength (rectangleComplement μ a k) a r =
      k + a - 1 - shiftedRowLength μ a (a - 1 - r) := by
  unfold shiftedRowLength
  rw [rowLen_rectangleComplement hμ hr]
  have hb := rowLen_le_of_le_rectangle (r := a - 1 - r) hμ
  omega

/-- A pairwise complementary gap equals the corresponding reversed original gap. -/
theorem shiftedDifference_rectangleComplement (hμ : μ ≤ rectangle a k) {r j : ℕ}
    (hr : r < a) (hj : j < a) :
    shiftedRowLength (rectangleComplement μ a k) a r -
        shiftedRowLength (rectangleComplement μ a k) a j =
      shiftedRowLength μ a (a - 1 - j) - shiftedRowLength μ a (a - 1 - r) := by
  rw [shiftedRowLength_rectangleComplement hμ hr, shiftedRowLength_rectangleComplement hμ hj]
  have hrb := rowLen_le_of_le_rectangle (r := a - 1 - r) hμ
  have hjb := rowLen_le_of_le_rectangle (r := a - 1 - j) hμ
  unfold shiftedRowLength
  omega

private theorem prod_upperTriangle (b : ℕ → ℕ) (a : ℕ) :
    (∏ r ∈ range a, ∏ j ∈ Ioo r a, (b r - b j)) =
      ∏ r ∈ range a, ∏ j ∈ range a, if r < j then b r - b j else 1 := by
  apply prod_congr rfl
  intro r _
  rw [← prod_filter]
  congr 1
  ext j
  simp only [mem_Ioo, mem_filter, mem_range]
  tauto

/-- Complementation preserves the positive shifted Vandermonde product. -/
theorem shiftedVandermonde_rectangleComplement (hμ : μ ≤ rectangle a k) :
    (∏ r ∈ range a, ∏ j ∈ Ioo r a,
      (shiftedRowLength (rectangleComplement μ a k) a r -
        shiftedRowLength (rectangleComplement μ a k) a j)) =
    ∏ r ∈ range a, ∏ j ∈ Ioo r a,
      (shiftedRowLength μ a r - shiftedRowLength μ a j) := by
  rw [prod_upperTriangle, prod_upperTriangle]
  have hgap : ∀ r ∈ range a, ∀ j ∈ range a,
      (if r < j then shiftedRowLength (rectangleComplement μ a k) a r -
        shiftedRowLength (rectangleComplement μ a k) a j else 1) =
      if r < j then shiftedRowLength μ a (a - 1 - j) -
        shiftedRowLength μ a (a - 1 - r) else 1 := by
    intro r hr j hj
    split_ifs <;> simp_all only [shiftedDifference_rectangleComplement hμ (mem_range.mp hr)
      (mem_range.mp hj)]
  simp_rw [prod_congr rfl (fun r hr => prod_congr rfl (fun j hj => hgap r hr j hj))]
  rw [← prod_range_reflect]
  refine Eq.trans (b := ∏ r ∈ range a, ∏ j ∈ range a,
    if j < r then shiftedRowLength μ a j - shiftedRowLength μ a r else 1) ?_ prod_comm
  apply prod_congr rfl
  intro r hr
  rw [← prod_range_reflect]
  apply prod_congr rfl
  intro j hj
  have hr' := mem_range.mp hr
  have hj' := mem_range.mp hj
  have hrr : a - 1 - (a - 1 - r) = r := by omega
  have hjj : a - 1 - (a - 1 - j) = j := by omega
  rw [hrr, hjj]
  have he : a - 1 - r < a - 1 - j ↔ j < r := by omega
  simp only [he]


/-- The complementary factorial product uses the unreflected coordinates. -/
theorem shiftedFactorials_rectangleComplement (hμ : μ ≤ rectangle a k) :
    (∏ r ∈ range a, (shiftedRowLength (rectangleComplement μ a k) a r).factorial) =
      ∏ r ∈ range a, (k + a - 1 - shiftedRowLength μ a r).factorial := by
  calc
    _ = ∏ r ∈ range a, (k + a - 1 - shiftedRowLength μ a (a - 1 - r)).factorial := by
      apply prod_congr rfl
      intro r hr
      rw [shiftedRowLength_rectangleComplement hμ (mem_range.mp hr)]
    _ = _ := prod_range_reflect (fun r => (k + a - 1 - shiftedRowLength μ a r).factorial) a

end AdelicBostConjecture.Specht

