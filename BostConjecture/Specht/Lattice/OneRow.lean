/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Specht.Lattice.Rectangle

/-!
# The one-row rectangular lattice

There is one row word and its polytabloid is a unit vector. Consequently the
one-row lattice has covolume one. Reference: this paper, Example 3.12 and the proof of Proposition
5.1.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Specht

open OAI.Saxl Module

theorem oneRow_colLen_le_one (k : ℕ) : (rectangle 1 k).colLen 0 ≤ 1 := by
  by_contra h
  have hmem : (1, 0) ∈ rectangle 1 k := YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
  have := (mem_rectangle.mp hmem).1
  omega

/-- Evaluating at the unique row word identifies a one-row integral lattice with `ℤ`. -/
def oneRowIntegralEquiv {n k : ℕ} (t : Tableau n (rectangle 1 k)) :
    orbitLattice t ≃ₗ[ℤ] ℤ := by
  let : Subsingleton (Fin ((rectangle 1 k).colLen 0)) :=
    Fin.subsingleton_iff_le_one.mpr (oneRow_colLen_le_one k)
  exact
    { toFun := fun x => x.val (rowWord t)
      invFun := fun z => ⟨z • polytabloidInt t,
        Submodule.smul_mem _ z (polytabloidInt_mem_orbitLattice t)⟩
      left_inv := fun x => by
        apply Subtype.ext
        ext w
        have hw : w = rowWord t := Subsingleton.elim _ _
        simp [hw, polytabloidInt_rowWord]
      right_inv := fun z => by simp [polytabloidInt_rowWord]
      map_add' := fun x y => rfl
      map_smul' := fun z x => by simp }

/-- The sole polytabloid is an integral basis of the one-row lattice. -/
def oneRowIntegralBasis {n k : ℕ} (t : Tableau n (rectangle 1 k)) :
    Basis Unit ℤ (orbitLattice t) :=
  (Basis.singleton Unit ℤ).map (oneRowIntegralEquiv t).symm

@[simp] theorem oneRowIntegralBasis_val {n k : ℕ} (t : Tableau n (rectangle 1 k)) (i : Unit) :
    (oneRowIntegralBasis t i).val = polytabloidInt t := by
  simp [oneRowIntegralBasis, oneRowIntegralEquiv]

theorem oneRow_covolume_eq_one {n k : ℕ} (t : Tableau n (rectangle 1 k)) :
    ZLattice.covolume (spanLattice t) = 1 := by
  have hgram := ZLattice.covolume_sq_eq_det_gram (spanLattice t)
    ((oneRowIntegralBasis t).map (latticeEquiv t))
  rw [Matrix.det_unique, Matrix.gram_apply, real_inner_self_eq_norm_sq] at hgram
  have hn : ‖((oneRowIntegralBasis t).map (latticeEquiv t) default : realSpan t)‖ ^ 2 = 1 := by
    change ‖realCast n ((rectangle 1 k).colLen 0)
      (oneRowIntegralBasis t default).val‖ ^ 2 = 1
    rw [oneRowIntegralBasis_val, norm_rectangle_polytabloidInt_sq]
    simp
  rw [hn] at hgram
  have hp := one_le_covolume t
  nlinarith

@[simp] theorem rectangleLogCovolume_one (k : ℕ) : rectangleLogCovolume 1 k = 0 := by
  simp [rectangleLogCovolume, oneRow_covolume_eq_one]

/-- The one-row normalized logarithmic covolume vanishes at every tensor degree. -/
theorem tendsto_rectangleLogCovolume_one_div :
    Filter.Tendsto (fun k : ℕ => rectangleLogCovolume 1 k / (k : ℝ))
      Filter.atTop (nhds 0) := by
  simp

end BostConjecture.Specht
