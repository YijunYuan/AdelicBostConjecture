module

public import BostConjecture.Specht.Adjacent
public import BostConjecture.Specht.Rectangle

/-!
# The column-reading initial vector

The column-reading tableau is the least standard tableau in colexicographic
order. Its monic orthogonal vector is therefore the original polytabloid.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Specht

open OAI.Saxl
open scoped StandardColex

/-- Enumerate a rectangle down successive columns, without changing the orbit lattice. -/
def rectangleColumnTableau (a k : ℕ) : Tableau (a * k) (rectangle a k) :=
  (((rectangleCellsEquiv a k).trans (Equiv.prodComm _ _)).trans
    (finProdFinEquiv.trans (finCongr (Nat.mul_comm k a)))).symm

@[simp] theorem rectangleColumnTableau_symm_val (a k : ℕ) (b : rectangle a k) :
    ((rectangleColumnTableau a k).symm b).val = b.val.1 + a * b.val.2 := rfl

theorem rectangleColumnTableau_label (a k : ℕ) (j : Fin (a * k)) :
    j.val = (rectangleColumnTableau a k j).val.1 +
      a * (rectangleColumnTableau a k j).val.2 := by
  simpa only [Equiv.symm_apply_apply] using
    rectangleColumnTableau_symm_val a k (rectangleColumnTableau a k j)

/-- Column reading increases both along rows and down columns. -/
theorem rectangleColumnTableau_isStandard (a k : ℕ) :
    IsStandard (rectangleColumnTableau a k) := by
  have hlabel := rectangleColumnTableau_label a k
  have ha (i : Fin (a * k)) : 0 < a := by
    have := (mem_rectangle.mp (rectangleColumnTableau a k i).property).1
    omega
  constructor
  · intro i j hr hc
    have hm := Nat.mul_lt_mul_of_pos_left hc (ha i)
    have hi := hlabel i
    have hj := hlabel j
    change i.val < j.val
    omega
  · intro i j hc hr
    have hi := hlabel i
    have hj := hlabel j
    rw [← hc] at hj
    change i.val < j.val
    omega

/-- At the last changed box, every other standard tableau has a strictly later row. -/
theorem rectangleColumnTableau_colexLT {a k : ℕ}
    (u : Tableau (a * k) (rectangle a k)) (hu : IsStandard u)
    (hne : u ≠ rectangleColumnTableau a k) :
    TableauColexLT (rectangleColumnTableau a k) u := by
  classical
  let v := rectangleColumnTableau a k
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image
    (Finset.univ.filter fun j => u j ≠ v j) id (by
      by_contra! he
      apply hne
      apply Equiv.ext
      intro j
      by_contra hj
      have hm : j ∈ Finset.univ.filter (fun j => u j ≠ v j) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
      rw [he] at hm
      exact Finset.notMem_empty j hm)
  have hdiff : u j ≠ v j := (Finset.mem_filter.mp hj).2
  have htail : ∀ l, j < l → u l = v l := by
    intro l hl
    by_contra he
    exact (not_le_of_gt hl) (hmax l (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩))
  have hle : v.symm (u j) ≤ j := by
    by_contra he
    have hh := htail (v.symm (u j)) (lt_of_not_ge he)
    have heq : v.symm (u j) = j := u.injective (by simpa using hh)
    exact he heq.le
  have hcol : (u j).val.2 ≤ (v j).val.2 := by
    have hlabels := rectangleColumnTableau_label a k j
    have hle' : (u j).val.1 + a * (u j).val.2 ≤ j.val := hle
    have hrange : (v j).val.1 < a := (mem_rectangle.mp (v j).property).1
    by_contra hc
    have hm := Nat.mul_le_mul_left a (show (v j).val.2 + 1 ≤ (u j).val.2 by omega)
    change j.val = (v j).val.1 + a * (v j).val.2 at hlabels
    nlinarith
  refine ⟨j, ?_, fun l hl => congrArg (fun b : rectangle a k => b.val.1) (htail l hl).symm⟩
  by_contra hr
  have hrow : (u j).val.1 ≤ (v j).val.1 := le_of_not_gt hr
  have hjle : j ≤ u.symm (v j) := by simpa using hu.label_mono ⟨hrow, hcol⟩
  rcases hjle.eq_or_lt with he | he
  · exact hdiff (by simpa using congrArg u he)
  · have hh := htail (u.symm (v j)) he
    have heq : j = u.symm (v j) := v.injective (by simpa using hh)
    exact he.ne heq

/-- The column-reading standard tableau is first in the order used for orthogonalization. -/
theorem rectangleColumnTableau_isLeast (a k : ℕ)
    (U : {u : Tableau (a * k) (rectangle a k) // IsStandard u}) :
    ¬U < ⟨rectangleColumnTableau a k, rectangleColumnTableau_isStandard a k⟩ := by
  intro h
  have hne : U.val ≠ rectangleColumnTableau a k := fun he =>
    h.ne (Subtype.ext he)
  have hrev := rectangleColumnTableau_colexLT U.val U.property hne
  exact (not_lt_of_gt h) ((standardColex_lt_iff _ _).mpr hrev)

/-- The actual initial orthogonal vector is the column-reading polytabloid. -/
theorem orthogonalStandardBasis_rectangleColumnTableau
    (a k : ℕ) (t : Tableau (a * k) (rectangle a k)) :
    orthogonalStandardBasis t
        ⟨rectangleColumnTableau a k, rectangleColumnTableau_isStandard a k⟩ =
      standardRealBasis t
        ⟨rectangleColumnTableau a k, rectangleColumnTableau_isStandard a k⟩ :=
  orthogonalStandardBasis_eq_of_isLeast t _ (rectangleColumnTableau_isLeast a k)

/-- The initial monic squared norm is the cardinality of the rectangular column group. -/
theorem norm_orthogonalStandardBasis_rectangleColumnTableau_sq
    (a k : ℕ) (t : Tableau (a * k) (rectangle a k)) :
    ‖orthogonalStandardBasis t
      ⟨rectangleColumnTableau a k, rectangleColumnTableau_isStandard a k⟩‖ ^ 2 =
      (Nat.factorial a : ℝ) ^ k := by
  rw [orthogonalStandardBasis_rectangleColumnTableau]
  change ‖(standardRealBasis t
    ⟨rectangleColumnTableau a k, rectangleColumnTableau_isStandard a k⟩).val‖ ^ 2 = _
  rw [standardRealBasis_coe, norm_rectangle_polytabloidInt_sq]

end BostConjecture.Specht
