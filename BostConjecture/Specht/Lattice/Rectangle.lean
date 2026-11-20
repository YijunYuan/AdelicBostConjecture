/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Specht.Lattice.Norm

/-!
# Rectangular polytabloid lattices

The rectangle is a concrete Young diagram. Its column group is a product of
symmetric groups, one for each column. Reference: this paper, Section 3.2 and equation (3.16).
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Specht

open OAI.Saxl

/-- The Young diagram with `a` rows of length `k`. -/
def rectangle (a k : ℕ) : YoungDiagram where
  cells := Finset.range a ×ˢ Finset.range k
  isLowerSet := by
    intro x y hxy hy
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range] at hy ⊢
    exact ⟨lt_of_le_of_lt hxy.1 hy.1, lt_of_le_of_lt hxy.2 hy.2⟩

@[simp] theorem mem_rectangle {a k i j : ℕ} :
    (i, j) ∈ rectangle a k ↔ i < a ∧ j < k := by
  simp [rectangle]

@[simp] theorem card_rectangle (a k : ℕ) : (rectangle a k).card = a * k := by
  simp [rectangle, YoungDiagram.card]

theorem colLen_rectangle {a k j : ℕ} (hj : j < k) :
    (rectangle a k).colLen j = a := by
  apply eq_of_forall_lt_iff
  intro i
  rw [← YoungDiagram.mem_iff_lt_colLen, mem_rectangle]
  simp [hj]

theorem rowLen_rectangle {a k i : ℕ} (hi : i < a) :
    (rectangle a k).rowLen i = k := by
  apply eq_of_forall_lt_iff
  intro j
  rw [← YoungDiagram.mem_iff_lt_rowLen, mem_rectangle]
  simp [hi]

/-- Rectangle cells are pairs of a row and a column. -/
def rectangleCellsEquiv (a k : ℕ) : (rectangle a k).cells ≃ Fin a × Fin k where
  toFun x := ⟨⟨x.val.1, (mem_rectangle.mp x.property).1⟩,
    ⟨x.val.2, (mem_rectangle.mp x.property).2⟩⟩
  invFun x := ⟨(x.1.val, x.2.val), mem_rectangle.mpr ⟨x.1.isLt, x.2.isLt⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Row-reading enumeration of the rectangle; the orbit lattice is independent of it. -/
def rectangleTableau (a k : ℕ) : Tableau (a * k) (rectangle a k) :=
  finProdFinEquiv.symm.trans (rectangleCellsEquiv a k).symm

/-- Row and column coordinates of entries of a rectangular tableau. -/
def rectangleCoordinates {n a k : ℕ} (t : Tableau n (rectangle a k)) :
    Fin n ≃ Fin a × Fin k := t.trans (rectangleCellsEquiv a k)

theorem rectangleCoordinates_column {n a k : ℕ} (t : Tableau n (rectangle a k))
    (g : columnGroup t) (x : Fin n) :
    (rectangleCoordinates t ((g : Equiv.Perm (Fin n)) x)).2 = (rectangleCoordinates t x).2 :=
  Fin.ext (g.property x)

/-- Restrict a column permutation to the row indices in one column. -/
def rectangleColumnPerm {n a k : ℕ} (t : Tableau n (rectangle a k))
    (g : columnGroup t) (j : Fin k) : Equiv.Perm (Fin a) where
  toFun i :=
    (rectangleCoordinates t ((g : Equiv.Perm (Fin n)) ((rectangleCoordinates t).symm (i, j)))).1
  invFun i :=
    (rectangleCoordinates t ((g : Equiv.Perm (Fin n))⁻¹ ((rectangleCoordinates t).symm (i, j)))).1
  left_inv i := by
    have hp :
        ((rectangleCoordinates t ((g : Equiv.Perm (Fin n))
          ((rectangleCoordinates t).symm (i, j)))).1, j) =
        rectangleCoordinates t ((g : Equiv.Perm (Fin n))
          ((rectangleCoordinates t).symm (i, j))) := by
      refine Prod.ext rfl ?_
      simpa using (rectangleCoordinates_column t g ((rectangleCoordinates t).symm (i, j))).symm
    change (rectangleCoordinates t
      ((g : Equiv.Perm (Fin n))⁻¹ ((rectangleCoordinates t).symm _))).1 = i
    rw [hp]
    simp
  right_inv i := by
    have hp :
        ((rectangleCoordinates t ((g : Equiv.Perm (Fin n))⁻¹
          ((rectangleCoordinates t).symm (i, j)))).1, j) =
        rectangleCoordinates t ((g : Equiv.Perm (Fin n))⁻¹
          ((rectangleCoordinates t).symm (i, j))) := by
      refine Prod.ext rfl ?_
      simpa using (rectangleCoordinates_column t g⁻¹ ((rectangleCoordinates t).symm (i, j))).symm
    change (rectangleCoordinates t
      ((g : Equiv.Perm (Fin n)) ((rectangleCoordinates t).symm _))).1 = i
    rw [hp]
    simp

/-- Independently permute rows inside each column. -/
def rectangleColumnGroupOf {n a k : ℕ} (t : Tableau n (rectangle a k))
    (f : Fin k → Equiv.Perm (Fin a)) : columnGroup t :=
  ⟨{ toFun x := (rectangleCoordinates t).symm
        (f (rectangleCoordinates t x).2 (rectangleCoordinates t x).1,
          (rectangleCoordinates t x).2)
     invFun x := (rectangleCoordinates t).symm
        ((f (rectangleCoordinates t x).2).symm (rectangleCoordinates t x).1,
          (rectangleCoordinates t x).2)
     left_inv x := by simp
     right_inv x := by simp }, by
    intro x
    change ((rectangleCoordinates t ((rectangleCoordinates t).symm _)).2 : ℕ) = _
    simp
    rfl⟩

/-- The column group of an `a × k` rectangle is a product of `k` symmetric groups. -/
def rectangleColumnGroupEquiv {n a k : ℕ} (t : Tableau n (rectangle a k)) :
    columnGroup t ≃ (Fin k → Equiv.Perm (Fin a)) where
  toFun g := rectangleColumnPerm t g
  invFun f := rectangleColumnGroupOf t f
  left_inv g := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    apply (rectangleCoordinates t).injective
    change rectangleCoordinates t ((rectangleCoordinates t).symm
      ((rectangleCoordinates t ((g : Equiv.Perm (Fin n)) ((rectangleCoordinates t).symm
        ((rectangleCoordinates t x).1, (rectangleCoordinates t x).2)))).1,
        (rectangleCoordinates t x).2)) = _
    simp only [Prod.mk.eta, Equiv.symm_apply_apply, Equiv.apply_symm_apply]
    exact Prod.ext rfl (rectangleCoordinates_column t g x).symm
  right_inv f := by
    funext j
    apply Equiv.ext
    intro i
    change (rectangleCoordinates t ((rectangleCoordinates t).symm
      (f (rectangleCoordinates t ((rectangleCoordinates t).symm (i, j))).2
        (rectangleCoordinates t ((rectangleCoordinates t).symm (i, j))).1,
        (rectangleCoordinates t ((rectangleCoordinates t).symm (i, j))).2))).1 = _
    simp

theorem card_rectangle_columnGroup {n a k : ℕ} (t : Tableau n (rectangle a k)) :
    Nat.card (columnGroup t) = a.factorial ^ k := by
  rw [Nat.card_congr (rectangleColumnGroupEquiv t)]
  simp [Fintype.card_perm]

/-- This paper, equation (3.16). The factorial normalization agrees with [Chen–Moriwaki, Remark
A.2.9][cmp].

The initial seminormal squared norm of a rectangular polytabloid. -/
theorem norm_rectangle_polytabloidInt_sq {n a k : ℕ} (t : Tableau n (rectangle a k)) :
    ‖realCast n (rectangle a k |>.colLen 0) (polytabloidInt t)‖ ^ 2 =
      (a.factorial : ℝ) ^ k := by
  rw [norm_polytabloidInt_sq, card_rectangle_columnGroup, Nat.cast_pow]

/-- The canonical all-polytabloid lattice of a rectangle. -/
abbrev rectangleLattice (a k : ℕ) := orbitLattice (rectangleTableau a k)

/-- Rank of the canonical integral rectangular lattice. -/
def rectangleRank (a k : ℕ) : ℕ := Module.finrank ℤ (rectangleLattice a k)

/-- Logarithmic covolume per rank in the inherited orthonormal word metric. -/
def rectangleLogCovolume (a k : ℕ) : ℝ :=
  Real.log (ZLattice.covolume (spanLattice (rectangleTableau a k))) / rectangleRank a k

theorem rectangleLogCovolume_nonneg (a k : ℕ) : 0 ≤ rectangleLogCovolume a k :=
  div_nonneg (log_covolume_nonneg _) (Nat.cast_nonneg _)

end BostConjecture.Specht
