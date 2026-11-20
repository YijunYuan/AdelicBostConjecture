/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Specht.Lattice.ColumnTensor

/-!
# Determinant covariance of the rectangular word lattice

The matrix action on word coordinates is the Kronecker action, with one
matrix entry for each tensor position. The existing rectangular polytabloids
are eigenvectors with eigenvalue `det u ^ k`, over every commutative ring.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Specht

open OAI.Saxl

variable {n a k : ℕ} {R : Type*} [CommRing R]

/-- The tensor-power matrix action in the word basis. -/
def wordTensorAction (n : ℕ) (u : Matrix (Fin a) (Fin a) R) :
    ((Fin n → Fin a) → R) →ₗ[R] ((Fin n → Fin a) → R) where
  toFun x w := ∑ v, (∏ q, u (w q) (v q)) * x v
  map_add' x y := by ext w; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by ext w; simp [Finset.mul_sum, mul_left_comm]

/-- On a pure tensor, the word action applies the matrix independently to
its factors. -/
theorem wordTensorAction_prod (u : Matrix (Fin a) (Fin a) R)
    (v : Fin n → Fin a → R) :
    wordTensorAction n u (fun w => ∏ q, v q (w q)) =
      fun w => ∏ q, ∑ i, u (w q) i * v q i := by
  classical
  ext w
  change (∑ x : Fin n → Fin a, (∏ q, u (w q) (x q)) * ∏ q, v q (x q)) = _
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun q i => u (w q) i * v q i)).symm

private theorem rectangle_prod_positions (t : Tableau n (rectangle a k)) (F : Fin n → R) :
    (∏ q, F q) = ∏ j, ∏ i, F ((rectangleCoordinates t).symm (i, j)) := by
  rw [← (rectangleCoordinates t).symm.prod_comp]
  exact Fintype.prod_prod_type_right' (fun i j => F ((rectangleCoordinates t).symm (i, j)))

private theorem cast_altVec (f : Fin a → Fin a) :
    (Matrix.altVec ℤ f : R) = Matrix.altVec R f := by
  simp only [Matrix.altVec, Int.cast_sum, apply_ite, Int.cast_zero, Int.cast_id]

/-- The integral column factorization persists under coefficient extension. -/
theorem cast_polytabloidInt_rectangle_eq_prod (hk : 0 < k)
    (t : Tableau n (rectangle a k)) (w : Fin n → Fin a) :
    (polytabloidInt t ((rectangleAlphabetEquiv hk).symm w) : R) =
      ∏ j, Matrix.altVec R (rectangleColumnWordEquiv t w j) := by
  rw [polytabloidInt_rectangle_eq_prod hk, Int.cast_prod]
  simp only [cast_altVec]

/-- Every rectangular polytabloid transforms by the `k`th determinant power. -/
theorem wordTensorAction_polytabloid (hk : 0 < k)
    (t : Tableau n (rectangle a k)) (u : Matrix (Fin a) (Fin a) R) :
    wordTensorAction n u (fun w => (polytabloidInt t ((rectangleAlphabetEquiv hk).symm w) : R)) =
      u.det ^ k • (fun w => (polytabloidInt t ((rectangleAlphabetEquiv hk).symm w) : R)) := by
  classical
  ext w
  change (∑ v, (∏ q, u (w q) (v q)) *
      (polytabloidInt t ((rectangleAlphabetEquiv hk).symm v) : R)) = _
  simp_rw [cast_polytabloidInt_rectangle_eq_prod hk t]
  rw [← (rectangleColumnWordEquiv t).symm.sum_comp]
  simp only [Equiv.apply_symm_apply]
  simp_rw [rectangle_prod_positions t]
  have hc (v : Fin k → Fin a → Fin a) (i : Fin a) (j : Fin k) :
      (rectangleColumnWordEquiv t).symm v ((rectangleCoordinates t).symm (i, j)) = v j i := by
    simp [rectangleColumnWordEquiv]
  simp_rw [hc]
  change (∑ v : Fin k → Fin a → Fin a,
      (∏ j, ∏ i, u (rectangleColumnWordEquiv t w j i) (v j i)) *
        ∏ j, Matrix.altVec R (v j)) =
      u.det ^ k * ∏ j, Matrix.altVec R (rectangleColumnWordEquiv t w j)
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun j (v : Fin a → Fin a) =>
    (∏ i, u (rectangleColumnWordEquiv t w j i) (v i)) * Matrix.altVec R v)]
  change (∏ j, ∑ v, Matrix.tensorPow u (rectangleColumnWordEquiv t w j) v * Matrix.altVec R v) = _
  simp_rw [Matrix.sum_tensorPow_mul_altVec]
  rw [Finset.prod_mul_distrib]
  simp [mul_comm]

/-- This paper, equation (3.9) and proof of Lemma 6.1. See [Chen–Moriwaki, Section A.1.2][cmp].

Determinant covariance holds for every vector of the actual integral
orbit lattice after coefficient extension. -/
theorem wordTensorAction_of_mem_orbitLattice (hk : 0 < k)
    (t : Tableau n (rectangle a k)) (u : Matrix (Fin a) (Fin a) R)
    {x : (Fin n → Fin (rectangle a k |>.colLen 0)) → ℤ} (hx : x ∈ orbitLattice t) :
    wordTensorAction n u (fun w => (x ((rectangleAlphabetEquiv hk).symm w) : R)) =
      u.det ^ k • (fun w => (x ((rectangleAlphabetEquiv hk).symm w) : R)) := by
  let C : ((Fin n → Fin (rectangle a k |>.colLen 0)) → ℤ) →ₗ[ℤ]
      ((Fin n → Fin a) → R) :=
    { toFun := fun y w => (y ((rectangleAlphabetEquiv hk).symm w) : R)
      map_add' := by intros; ext w; simp
      map_smul' := by intros; ext w; simp [← Int.cast_smul_eq_zsmul R] }
  change wordTensorAction n u (C x) = u.det ^ k • C x
  rw [orbitLattice_eq_span_polytabloids] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, rfl⟩ := hx
    exact wordTensorAction_polytabloid hk s u
  | zero => simp
  | add x y hx hy ihx ihy => simp only [map_add, ihx, ihy, smul_add]
  | smul c x hx ih => rw [C.map_smul, map_zsmul, ih, smul_comm]

/-- The whole scalar span of the canonical integral lattice is determinant
isotypic, with no invariant-space equality assumed. -/
theorem wordTensorAction_of_mem_span (hk : 0 < k)
    (t : Tableau n (rectangle a k)) (u : Matrix (Fin a) (Fin a) R)
    {x : (Fin n → Fin a) → R}
    (hx : x ∈ Submodule.span R (Set.range fun y : orbitLattice t =>
      fun w => (y.val ((rectangleAlphabetEquiv hk).symm w) : R))) :
    wordTensorAction n u x = u.det ^ k • x := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, rfl⟩ := hx
    exact wordTensorAction_of_mem_orbitLattice hk t u y.property
  | zero => simp
  | add x y hx hy ihx ihy => simp only [map_add, ihx, ihy, smul_add]
  | smul c x hx ih => rw [map_smul, ih, smul_comm]

end BostConjecture.Specht
