/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.ExternalCode.Stacks.LinearAlgebra.Matrix.AlternatingTensorPower
public import BostConjecture.Specht.Lattice.Rectangle

/-!
# Rectangular polytabloids are products of alternating columns

The existing integral word coefficients, after identifying the rectangle's
row alphabet with `Fin a`, factor as unnormalized alternating vectors.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Specht

open OAI.Saxl

variable {n a k : ℕ}

/-- The sign of a column permutation is the product of its column signs. -/
theorem rectangleColumnGroupOf_sign (t : Tableau n (rectangle a k))
    (f : Fin k → Equiv.Perm (Fin a)) :
    Equiv.Perm.sign (rectangleColumnGroupOf t f : Equiv.Perm (Fin n)) =
      ∏ j, Equiv.Perm.sign (f j) := by
  let e := (Equiv.prodComm (Fin k) (Fin a)).trans (rectangleCoordinates t).symm
  have he : (rectangleColumnGroupOf t f : Equiv.Perm (Fin n)) =
      e.permCongr (Equiv.prodCongrRight f) := by
    ext x
    rfl
  rw [he, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_prodCongrRight]

/-- Relabeling the row alphabet does not change the underlying word lattice. -/
def rectangleAlphabetEquiv (hk : 0 < k) :
    (Fin n → Fin (rectangle a k |>.colLen 0)) ≃ (Fin n → Fin a) :=
  Equiv.piCongrRight fun _ => finCongr (colLen_rectangle hk)

/-- Read a word one column at a time, with the rows as column positions. -/
def rectangleColumnWordEquiv (t : Tableau n (rectangle a k)) :
    (Fin n → Fin a) ≃ (Fin k → Fin a → Fin a) where
  toFun w j i := w ((rectangleCoordinates t).symm (i, j))
  invFun f q := f (rectangleCoordinates t q).2 (rectangleCoordinates t q).1
  left_inv w := by funext q; simp
  right_inv f := by funext j i; simp

private theorem rectangle_rowWord_columnGroupOf (hk : 0 < k)
    (t : Tableau n (rectangle a k)) (f : Fin k → Equiv.Perm (Fin a)) :
    rectangleAlphabetEquiv hk
      (rowWord t ∘ (rectangleColumnGroupOf t f : Equiv.Perm (Fin n)).symm) =
      (rectangleColumnWordEquiv t).symm (fun j => (f j).symm) := by
  funext q
  apply Fin.ext
  change ((rectangleCoordinates t ((rectangleCoordinates t).symm
    ((f (rectangleCoordinates t q).2).symm (rectangleCoordinates t q).1,
      (rectangleCoordinates t q).2))).1).val = _
  simp [rectangleColumnWordEquiv]

/-- This paper, equation (3.8). The alternating tensor convention is [Chen–Moriwaki, Section
A.1.2][cmp].

The coefficient of an actual integral polytabloid is the product of its
column alternating coefficients. -/
theorem polytabloidInt_rectangle_eq_prod (hk : 0 < k)
    (t : Tableau n (rectangle a k)) (w : Fin n → Fin a) :
    polytabloidInt t ((rectangleAlphabetEquiv hk).symm w) =
      ∏ j, Matrix.altVec ℤ (rectangleColumnWordEquiv t w j) := by
  classical
  let := Fintype.ofFinite (columnGroup t)
  unfold polytabloidInt
  simp only [Finset.sum_apply, Pi.smul_apply, wordRepInt_single, Pi.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [← (rectangleColumnGroupEquiv t).symm.sum_comp]
  change (∑ f : Fin k → Equiv.Perm (Fin a),
    if (rectangleAlphabetEquiv hk).symm w =
      rowWord t ∘ (rectangleColumnGroupOf t f : Equiv.Perm (Fin n)).symm
    then (Equiv.Perm.sign (rectangleColumnGroupOf t f : Equiv.Perm (Fin n)) : ℤ)
    else 0) = _
  have hword (f : Fin k → Equiv.Perm (Fin a)) :
      (rectangleAlphabetEquiv hk).symm w =
        rowWord t ∘ (rectangleColumnGroupOf t f : Equiv.Perm (Fin n)).symm ↔
      ∀ j, (fun i => (f j).symm i) = rectangleColumnWordEquiv t w j := by
    rw [← (rectangleAlphabetEquiv hk).apply_eq_iff_eq, Equiv.apply_symm_apply,
      rectangle_rowWord_columnGroupOf hk, ← (rectangleColumnWordEquiv t).apply_eq_iff_eq,
      Equiv.apply_symm_apply]
    exact ⟨fun h j => (congrFun h j).symm, fun h => (funext h).symm⟩
  simp_rw [hword, rectangleColumnGroupOf_sign, Units.coe_prod]
  have hp (f : Fin k → Equiv.Perm (Fin a)) :
      (if ∀ j, (fun i => (f j).symm i) = rectangleColumnWordEquiv t w j
        then ∏ j, (Equiv.Perm.sign (f j) : ℤ) else 0) =
      ∏ j, if (fun i => (f j).symm i) = rectangleColumnWordEquiv t w j
        then (Equiv.Perm.sign (f j) : ℤ) else 0 := by
    convert! (Fintype.prod_ite_zero
      (p := fun j => (fun i => (f j).symm i) = rectangleColumnWordEquiv t w j)
      (f := fun j => (Equiv.Perm.sign (f j) : ℤ))).symm using 1
    split_ifs <;> rfl
  simp_rw [hp]
  rw [← Fintype.prod_sum (fun j (σ : Equiv.Perm (Fin a)) =>
    if (fun i => σ.symm i) = rectangleColumnWordEquiv t w j
    then (Equiv.Perm.sign σ : ℤ) else 0)]
  apply Finset.prod_congr rfl
  intro j _
  rw [← Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin a)))]
  simp [Matrix.altVec, Equiv.Perm.sign_inv, ← Equiv.Perm.inv_def]

end BostConjecture.Specht
