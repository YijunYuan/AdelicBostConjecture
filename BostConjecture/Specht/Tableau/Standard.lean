/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Specht.Tableau.Basic

/-!
# Standard tableaux and triangular polytabloids

Standardness is imposed on the existing enumerating tableaux. Row words
distinguish row-standard tableaux; a column-standard tableau has the
lexicographically least row word among the terms of its polytabloid.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Specht

open OAI.Saxl

variable {n : ℕ} {μ : YoungDiagram}

/-- Labels increase from left to right in each row. -/
class RowStandard (t : Tableau n μ) : Prop where
  /-- Labels increase along each row. -/
  label_lt : ∀ i j, (t i).val.1 = (t j).val.1 → (t i).val.2 < (t j).val.2 → i < j

/-- Labels increase from top to bottom in each column. -/
class ColumnStandard (t : Tableau n μ) : Prop where
  /-- Labels increase down each column. -/
  label_lt : ∀ i j, (t i).val.2 = (t j).val.2 → (t i).val.1 < (t j).val.1 → i < j

/-- Standardness of an enumerating tableau. -/
class IsStandard (t : Tableau n μ) : Prop where
  /-- Standard tableaux are row-standard. -/
  rowStandard : RowStandard t
  /-- Standard tableaux are column-standard. -/
  columnStandard : ColumnStandard t

attribute [instance] IsStandard.rowStandard IsStandard.columnStandard

instance (t : {t : Tableau n μ // IsStandard t}) : IsStandard t.val := t.property

/-- Sorting every row removes the ambiguity in its row tabloid. -/
theorem RowStandard.eq_of_rowWord_eq {t u : Tableau n μ}
    [ht : RowStandard t] [hu : RowStandard u] (h : rowWord t = rowWord u) : t = u := by
  apply Equiv.ext
  intro i
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    have hr : (t i).val.1 = (u i).val.1 := congrArg Fin.val (congrFun h i)
    apply Subtype.ext
    apply Prod.ext hr
    apply le_antisymm
    · by_contra hc
      have hc' : (u i).val.2 < (t i).val.2 := lt_of_not_ge hc
      let j := t.symm (u i)
      have hj : j < i := ht.label_lt j i (by simp [j, hr]) (by simpa [j] using hc')
      have he : u i = u j := by simpa [j] using ih j hj
      exact (ne_of_lt hj) (u.injective he).symm
    · by_contra hc
      have hc' : (t i).val.2 < (u i).val.2 := lt_of_not_ge hc
      let j := u.symm (t i)
      have hj : j < i := hu.label_lt j i (by simp [j, hr]) (by simpa [j] using hc')
      have he : t j = t i := by simpa [j] using ih j hj
      exact (ne_of_lt hj) (t.injective he)

/-- In a column-standard tableau, a nonidentity column permutation increases
the row word lexicographically. -/
theorem ColumnStandard.rowWord_lt {t : Tableau n μ} [ht : ColumnStandard t]
    (g : columnGroup t) (hg : g ≠ 1) :
    toLex (rowWord t) < toLex (rowWord t ∘ (g : Equiv.Perm (Fin n))) := by
  classical
  let σ : Equiv.Perm (Fin n) := g.val
  have hex : ∃ i, σ i ≠ i := by
    by_contra h
    push Not at h
    exact hg (Subtype.ext (Equiv.ext h))
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image
    (Finset.univ.filter fun i : Fin n => σ i ≠ i) id (by
      obtain ⟨i, hi⟩ := hex
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩)
  have hgi : σ i ≠ i := (Finset.mem_filter.mp hi).2
  have hfix : ∀ j < i, σ j = j := by
    intro j hj
    by_contra hgj
    exact (not_le_of_gt hj) (hmin j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgj⟩))
  have hlt : i < σ i := by
    rcases lt_trichotomy i (σ i) with h | h | h
    · exact h
    · exact (hgi h.symm).elim
    · exact (hgi (σ.injective (hfix (σ i) h))).elim
  refine ⟨i, ?_, ?_⟩
  · intro j hj
    exact congrArg (rowWord t) (hfix j hj).symm
  · change (t i).val.1 < (t (σ i)).val.1
    rcases lt_trichotomy (t i).val.1 (t (σ i)).val.1 with h | h | h
    · exact h
    · have he : t i = t (σ i) := Subtype.ext (Prod.ext h (g.property i).symm)
      exact (hlt.ne (t.injective he)).elim
    · exact (not_lt_of_ge hlt.le (ht.label_lt (σ i) i (g.property i) h)).elim

/-- Every word with a nonzero coefficient lies above the leading row word. -/
theorem ColumnStandard.rowWord_le_of_polytabloid_ne_zero {t : Tableau n μ}
    [ht : ColumnStandard t] {w : Fin n → Fin (μ.colLen 0)}
    (hw : polytabloidInt t w ≠ 0) : toLex (rowWord t) ≤ toLex w := by
  classical
  let := Fintype.ofFinite (columnGroup t)
  unfold polytabloidInt at hw
  simp only [Finset.sum_apply, Pi.smul_apply, wordRepInt_single, Pi.single_apply] at hw
  obtain ⟨g, _, hg⟩ := Finset.exists_ne_zero_of_sum_ne_zero hw
  have he : rowWord t ∘ (g⁻¹ : columnGroup t).val = w := by
    by_cases h : w = rowWord t ∘ g.val.symm
    · exact h.symm
    · simp only [Equiv.Perm.inv_def, ite_eq_right h, smul_zero, ne_eq, not_true_eq_false] at hg
  rw [← he]
  by_cases h : g⁻¹ = 1
  · simp [h]
  · exact (ColumnStandard.rowWord_lt (t := t) g⁻¹ h).le

/-- The integral standard polytabloids are independent after coefficientwise
extension to any ring. In particular this applies to both rational and real coefficients. -/
theorem linearIndependent_standard_polytabloid (R : Type*) [Ring R] :
    LinearIndependent R (fun t : {t : Tableau n μ // IsStandard t} =>
      fun w => (polytabloidInt t.val w : R)) := by
  classical
  rw [linearIndependent_iff']
  intro s c hc i hi
  by_contra hci
  let s' := s.filter fun t => c t ≠ 0
  have hs' : s'.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hci⟩⟩
  obtain ⟨t, ht, hmin⟩ := Finset.exists_min_image s'
    (fun t => toLex (rowWord t.val)) hs'
  have ht' := Finset.mem_filter.mp ht
  have hz (u : {t : Tableau n μ // IsStandard t}) (hu : u ∈ s) (hut : u ≠ t) :
      c u * (polytabloidInt u.val (rowWord t.val) : R) = 0 := by
    by_cases hcu : c u = 0
    · simp [hcu]
    have hpol : polytabloidInt u.val (rowWord t.val) = 0 := by
      by_contra hpol
      have hle := ColumnStandard.rowWord_le_of_polytabloid_ne_zero (t := u.val) hpol
      have hrev := hmin u (Finset.mem_filter.mpr ⟨hu, hcu⟩)
      have hword : rowWord u.val = rowWord t.val :=
        congrArg ofLex (le_antisymm hle hrev)
      exact hut (Subtype.ext (RowStandard.eq_of_rowWord_eq (t := u.val) (u := t.val) hword))
    simp [hpol]
  have he := congrFun hc (rowWord t.val)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at he
  rw [Finset.sum_eq_single t (fun u hu hut => hz u hu hut)
    (fun ht => (ht ht'.1).elim), polytabloidInt_rowWord, Int.cast_one, mul_one] at he
  exact ht'.2 he

end BostConjecture.Specht
