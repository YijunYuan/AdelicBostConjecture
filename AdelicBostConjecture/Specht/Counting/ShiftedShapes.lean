/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import AdelicBostConjecture.Specht.Counting.OccupancySort
public import AdelicBostConjecture.Specht.Counting.ShiftedCount
public import AdelicBostConjecture.Specht.Tableau.Complement

/-!
# Rectangular subdiagrams as decreasing occupancies

Subtracting the staircase from a strictly decreasing bounded tuple produces
the actual Young diagram whose shifted row lengths are that tuple.
-/

@[expose] public section

noncomputable section

namespace AdelicBostConjecture.Specht

open OAI.Saxl Finset

/-- Sum of the staircase added to the row lengths. -/
def staircaseSum (a : ℕ) : ℕ := ∑ i : Fin a, (a - i.val - 1)

private theorem strictAnti_gap {a : ℕ} (b : Fin a → ℕ) (hb : StrictAnti b)
    (i j : Fin a) (hij : i ≤ j) : b j + (j.val - i.val) ≤ b i := by
  have h (n : ℕ) : ∀ hn : i.val + n < a,
      b ⟨i.val + n, hn⟩ + n ≤ b i := by
    induction n with
    | zero => intro hn; simp
    | succ n ih =>
      intro hn
      have hn' : i.val + n < a := by omega
      have hp := ih hn'
      have hl := hb (show (⟨i.val + n, hn'⟩ : Fin a) < ⟨i.val + (n + 1), hn⟩ by
        simp only [Fin.lt_def]; omega)
      omega
  simpa only [Nat.add_sub_of_le hij] using h (j.val - i.val) (by omega)

/-- Unshifted row length of a decreasing occupancy. -/
def unshiftOccupancy {a M A : ℕ} (b : SortedOccupancy a M A) (i : Fin a) : ℕ :=
  (b.val.val i).val - (a - i.val - 1)

theorem staircase_le_occupancy {a M A : ℕ} (b : SortedOccupancy a M A) (i : Fin a) :
    a - i.val - 1 ≤ (b.val.val i).val := by
  have ha : 0 < a := Nat.zero_lt_of_lt i.isLt
  have h := strictAnti_gap (fun r => (b.val.val r).val)
    (Fin.val_strictMono.comp_strictAnti b.property) i ⟨a - 1, by omega⟩ (by
      simp only [Fin.le_def]; omega)
  dsimp at h
  omega

theorem unshiftOccupancy_antitone {a M A : ℕ} (b : SortedOccupancy a M A) :
    Antitone (unshiftOccupancy b) := by
  intro i j hij
  have h := strictAnti_gap (fun r => (b.val.val r).val)
    (Fin.val_strictMono.comp_strictAnti b.property) i j hij
  have hi := i.isLt
  have hj := j.isLt
  have hs := staircase_le_occupancy b i
  unfold unshiftOccupancy
  omega

theorem unshiftOccupancy_le {a k A : ℕ} (b : SortedOccupancy a (k + a - 1) A)
    (i : Fin a) : unshiftOccupancy b i ≤ k := by
  have ha : 0 < a := Nat.zero_lt_of_lt i.isLt
  have h := strictAnti_gap (fun r => (b.val.val r).val)
    (Fin.val_strictMono.comp_strictAnti b.property) ⟨0, ha⟩ i (by
      change 0 ≤ i.val
      exact Nat.zero_le _)
  have h0 := (b.val.val ⟨0, ha⟩).isLt
  have hi := i.isLt
  unfold unshiftOccupancy
  dsimp at h
  omega

/-- The Young diagram obtained by removing the staircase. -/
def occupancyShape {a k A : ℕ} (b : SortedOccupancy a (k + a - 1) A) : YoungDiagram :=
  YoungDiagram.ofRowLens (List.ofFn (unshiftOccupancy b))
    (unshiftOccupancy_antitone b).sortedGE_ofFn

theorem rowLen_occupancyShape {a k A : ℕ} (b : SortedOccupancy a (k + a - 1) A)
    (i : Fin a) : (occupancyShape b).rowLen i.val = unshiftOccupancy b i := by
  simpa [occupancyShape] using YoungDiagram.rowLen_ofRowLens
    (hw := (unshiftOccupancy_antitone b).sortedGE_ofFn)
    (⟨i.val, by simp⟩ : Fin (List.ofFn (unshiftOccupancy b)).length)

theorem occupancyShape_le {a k A : ℕ} (b : SortedOccupancy a (k + a - 1) A) :
    occupancyShape b ≤ rectangle a k := by
  intro c hc
  obtain ⟨hr, hq⟩ := YoungDiagram.mem_ofRowLens.mp hc
  have hr' : c.1 < a := by simpa using hr
  have hq' : c.2 < unshiftOccupancy b ⟨c.1, hr'⟩ := by simpa using hq
  exact mem_rectangle.mpr ⟨hr', hq'.trans_le (unshiftOccupancy_le b _)⟩

theorem shiftedRowLength_occupancyShape {a k A : ℕ}
    (b : SortedOccupancy a (k + a - 1) A) (i : Fin a) :
    shiftedRowLength (occupancyShape b) a i.val = (b.val.val i).val := by
  have hs := staircase_le_occupancy b i
  have hi := i.isLt
  unfold shiftedRowLength
  rw [rowLen_occupancyShape]
  unfold unshiftOccupancy
  omega

/-- Counting cells by rows, with padding up to the enclosing height. -/
theorem sum_rowLen_rectangle {μ : YoungDiagram} {a k : ℕ} (hμ : μ ≤ rectangle a k) :
    ∑ i : Fin a, μ.rowLen i.val = μ.card := by
  have hm : Set.MapsTo Prod.fst (μ.cells : Set (ℕ × ℕ)) (range a) :=
    fun c hc => mem_range.mpr (mem_rectangle.mp (hμ hc)).1
  change (∑ i : Fin a, μ.rowLen i.val) = μ.cells.card
  rw [Fin.sum_univ_eq_sum_range, card_eq_sum_card_fiberwise hm]
  apply sum_congr rfl
  exact fun r _ => μ.rowLen_eq_card

theorem card_occupancyShape_add_staircase {a k A : ℕ}
    (b : SortedOccupancy a (k + a - 1) A) :
    (occupancyShape b).card + staircaseSum a = A := by
  rw [← sum_rowLen_rectangle (occupancyShape_le b)]
  unfold staircaseSum
  rw [← sum_add_distrib]
  calc
    _ = ∑ i : Fin a, (b.val.val i).val := by
      apply sum_congr rfl
      intro i _
      rw [rowLen_occupancyShape]
      exact Nat.sub_add_cancel (staircase_le_occupancy b i)
    _ = A := b.val.property

/-- Young subdiagrams of a fixed rectangle with fixed cardinality. -/
abbrev RectangleShape (a k m : ℕ) :=
  {μ : YoungDiagram // μ ≤ rectangle a k ∧ μ.card = m}

/-- Shift the row lengths of the actual subdiagram. -/
def rectangleShapeOccupancy {a k m : ℕ} (μ : RectangleShape a k m) :
    SortedOccupancy a (k + a - 1) (m + staircaseSum a) := by
  let b : Fin a → Fin (k + a - 1 + 1) := fun i =>
    ⟨shiftedRowLength μ.val a i.val, by
      have hk := rowLen_le_of_le_rectangle (r := i.val) μ.property.1
      have hi := i.isLt
      unfold shiftedRowLength
      omega⟩
  refine ⟨⟨b, ?_⟩, ?_⟩
  · have hs (i : Fin a) : (b i).val = μ.val.rowLen i.val + (a - i.val - 1) := by
      have hi := i.isLt
      dsimp [b, shiftedRowLength]
      omega
    simp_rw [hs]
    rw [sum_add_distrib, sum_rowLen_rectangle μ.property.1, μ.property.2]
    rfl
  · intro i j hij
    exact shiftedRowLength_strictAnti μ.val hij j.isLt

@[simp] theorem rectangleShapeOccupancy_apply {a k m : ℕ}
    (μ : RectangleShape a k m) (i : Fin a) :
    ((rectangleShapeOccupancy μ).val.val i).val = shiftedRowLength μ.val a i.val := rfl

theorem occupancyShape_rectangleShapeOccupancy {a k m : ℕ}
    (μ : RectangleShape a k m) : occupancyShape (rectangleShapeOccupancy μ) = μ.val := by
  ext c
  simp only [YoungDiagram.mem_cells]
  by_cases hr : c.1 < a
  · have hrow : (occupancyShape (rectangleShapeOccupancy μ)).rowLen c.1 = μ.val.rowLen c.1 := by
      rw [rowLen_occupancyShape _ ⟨c.1, hr⟩]
      unfold unshiftOccupancy
      rw [rectangleShapeOccupancy_apply]
      unfold shiftedRowLength
      dsimp only
      omega
    rw [YoungDiagram.mem_iff_lt_rowLen, YoungDiagram.mem_iff_lt_rowLen, hrow]
  · have hn₁ : c ∉ occupancyShape (rectangleShapeOccupancy μ) :=
      fun hc => hr (mem_rectangle.mp (occupancyShape_le _ hc)).1
    have hn₂ : c ∉ μ.val := fun hc => hr (mem_rectangle.mp (μ.property.1 hc)).1
    simp [hn₁, hn₂]

/-- Removing and adding the staircase identify shapes with decreasing occupancies. -/
def rectangleShapeEquivSortedOccupancy (a k m : ℕ) :
    RectangleShape a k m ≃ SortedOccupancy a (k + a - 1) (m + staircaseSum a) where
  toFun := rectangleShapeOccupancy
  invFun b := ⟨occupancyShape b, occupancyShape_le b, by
    have h := card_occupancyShape_add_staircase b
    omega⟩
  left_inv μ := Subtype.ext (occupancyShape_rectangleShapeOccupancy μ)
  right_inv b := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    apply Fin.ext
    exact shiftedRowLength_occupancyShape b i

instance (a k m : ℕ) : Fintype (RectangleShape a k m) :=
  Fintype.ofEquiv _ (rectangleShapeEquivSortedOccupancy a k m).symm

end AdelicBostConjecture.Specht
