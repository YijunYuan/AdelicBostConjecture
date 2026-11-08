/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Specht.Seminormal.RealAction

/-!
# Content coefficients of the concrete Murphy action

The coefficient at a tableau's own row word is computed directly from its
integral column antisymmetrizer. These are word coefficients; triangularity
in the standard-polytabloid basis is a separate assertion.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Specht

open OAI.Saxl

variable {n : ℕ} {μ : YoungDiagram}

/-- A nonzero word coefficient is produced by a column permutation. -/
theorem exists_column_of_polytabloidInt_ne_zero (t : Tableau n μ)
    {w : Fin n → Fin (μ.colLen 0)} (hw : polytabloidInt t w ≠ 0) :
    ∃ g : columnGroup t, rowWord t ∘ g.val = w := by
  classical
  let := Fintype.ofFinite (columnGroup t)
  unfold polytabloidInt at hw
  simp only [Finset.sum_apply, Pi.smul_apply, wordRepInt_single, Pi.single_apply] at hw
  obtain ⟨g, _, hg⟩ := Finset.exists_ne_zero_of_sum_ne_zero hw
  refine ⟨g⁻¹, ?_⟩
  by_contra he
  have h : w ≠ rowWord t ∘ g.val.symm := Ne.symm he
  simp only [Equiv.Perm.inv_def, ite_eq_right h, smul_zero, ne_eq, not_true_eq_false] at hg

/-- A swap between different rows and different columns has zero leading coefficient. -/
theorem polytabloidInt_rowWord_swap_eq_zero (t : Tableau n μ) (i j : Fin n)
    (hr : (t i).val.1 ≠ (t j).val.1) (hc : (t i).val.2 ≠ (t j).val.2) :
    polytabloidInt t (rowWord t ∘ Equiv.swap i j) = 0 := by
  classical
  by_contra hz
  obtain ⟨g, hg⟩ := exists_column_of_polytabloidInt_ne_zero t hz
  have hfix (k : Fin n) (hki : k ≠ i) (hkj : k ≠ j) : g.val k = k := by
    apply t.injective
    apply Subtype.ext
    apply Prod.ext _ (g.property k)
    have h := congrArg Fin.val (congrFun hg k)
    simpa only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hki hkj, rowWord] using h
  have hgi : g.val i ≠ i := by
    intro he
    have h := congrArg Fin.val (congrFun hg i)
    simp only [Function.comp_apply, Equiv.swap_apply_left, he] at h
    exact hr h
  have hgj : g.val i = j := by
    by_contra he
    exact hgi (g.val.injective (hfix (g.val i) hgi he))
  exact hc (by simpa only [hgj] using (g.property i).symm)

/-- The own-row-word coefficient after a transposition, for an arbitrary tableau. -/
theorem polytabloidInt_rowWord_swap (t : Tableau n μ) (i j : Fin n) (hij : i ≠ j) :
    polytabloidInt t (rowWord t ∘ Equiv.swap i j) =
      (if (t i).val.1 = (t j).val.1 then 1 else 0) -
        (if (t i).val.2 = (t j).val.2 then 1 else 0) := by
  classical
  by_cases hr : (t i).val.1 = (t j).val.1
  · have hc : (t i).val.2 ≠ (t j).val.2 := fun hc =>
      hij (t.injective (Subtype.ext (Prod.ext hr hc)))
    have hw : rowWord t ∘ Equiv.swap i j = rowWord t := by
      funext k
      exact Equiv.apply_swap_eq_self (Fin.ext hr) k
    simp [hr, hc, hw, polytabloidInt_rowWord]
  by_cases hc : (t i).val.2 = (t j).val.2
  · have hcol : Equiv.swap i j ∈ columnGroup t :=
      fun k => Equiv.apply_swap_eq_self (v := fun x => (t x).val.2) hc k
    have h := congrFun (polytabloidInt_relabel_of_mem_columnGroup t hcol) (rowWord t)
    rw [polytabloidInt_relabel] at h
    change polytabloidInt t (rowWord t ∘ Equiv.swap i j) = _ at h
    simpa [hr, hc, Equiv.Perm.sign_swap hij, polytabloidInt_rowWord] using h
  simp [hr, hc, polytabloidInt_rowWord_swap_eq_zero t i j hr hc]

/-- In a standard row, the order of labels is exactly the order of columns. -/
theorem RowStandard.lt_iff_col_lt {t : Tableau n μ} (ht : RowStandard t)
    {i j : Fin n} (hr : (t i).val.1 = (t j).val.1) :
    i < j ↔ (t i).val.2 < (t j).val.2 := by
  constructor
  · intro hij
    rcases lt_trichotomy (t i).val.2 (t j).val.2 with h | h | h
    · exact h
    · exact (hij.ne (t.injective (Subtype.ext (Prod.ext hr h)))).elim
    · exact (hij.not_gt (ht j i hr.symm h)).elim
  · exact ht i j hr

/-- In a standard column, the order of labels is exactly the order of rows. -/
theorem ColumnStandard.lt_iff_row_lt {t : Tableau n μ} (ht : ColumnStandard t)
    {i j : Fin n} (hc : (t i).val.2 = (t j).val.2) :
    i < j ↔ (t i).val.1 < (t j).val.1 := by
  constructor
  · intro hij
    rcases lt_trichotomy (t i).val.1 (t j).val.1 with h | h | h
    · exact h
    · exact (hij.ne (t.injective (Subtype.ext (Prod.ext h hc)))).elim
    · exact (hij.not_gt (ht j i hc.symm h)).elim
  · exact ht i j hc

open Classical in
/-- Earlier labels in a standard row are counted by the column coordinate. -/
theorem RowStandard.card_earlier_row {t : Tableau n μ} (ht : RowStandard t) (j : Fin n) :
    ((Finset.Iio j).filter fun i => (t i).val.1 = (t j).val.1).card = (t j).val.2 := by
  classical
  rw [← Finset.card_range (t j).val.2]
  apply Finset.card_bij (fun i _ => (t i).val.2)
  · intro i hi
    obtain ⟨hi, hr⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_range.mpr ((ht.lt_iff_col_lt hr).mp (Finset.mem_Iio.mp hi))
  · intro i hi k hk he
    apply t.injective
    apply Subtype.ext
    exact Prod.ext ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hk).2.symm) he
  · intro c hc
    have hc' : c < (t j).val.2 := Finset.mem_range.mp hc
    let b : μ := ⟨((t j).val.1, c), YoungDiagram.mem_iff_lt_rowLen.mpr
      (hc'.trans (YoungDiagram.mem_iff_lt_rowLen.mp (t j).property))⟩
    refine ⟨t.symm b, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_Iio.mpr
        apply (ht.lt_iff_col_lt (by simp [b])).mpr
        simpa [b] using hc'
      · simp [b]
    · simp [b]

open Classical in
/-- Earlier labels in a standard column are counted by the row coordinate. -/
theorem ColumnStandard.card_earlier_column {t : Tableau n μ}
    (ht : ColumnStandard t) (j : Fin n) :
    ((Finset.Iio j).filter fun i => (t i).val.2 = (t j).val.2).card = (t j).val.1 := by
  classical
  rw [← Finset.card_range (t j).val.1]
  apply Finset.card_bij (fun i _ => (t i).val.1)
  · intro i hi
    obtain ⟨hi, hc⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_range.mpr ((ht.lt_iff_row_lt hc).mp (Finset.mem_Iio.mp hi))
  · intro i hi k hk he
    apply t.injective
    apply Subtype.ext
    exact Prod.ext he ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hk).2.symm)
  · intro r hr
    have hr' : r < (t j).val.1 := Finset.mem_range.mp hr
    let b : μ := ⟨(r, (t j).val.2), YoungDiagram.mem_iff_lt_colLen.mpr
      (hr'.trans (YoungDiagram.mem_iff_lt_colLen.mp (t j).property))⟩
    refine ⟨t.symm b, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_Iio.mpr
        apply (ht.lt_iff_row_lt (by simp [b])).mpr
        simpa [b] using hr'
      · simp [b]
    · simp [b]

/-- The signed content of the box carrying a label. -/
def tableauContent (t : Tableau n μ) (j : Fin n) : ℤ :=
  (t j).val.2 - (t j).val.1

/-- The concrete integral Murphy sum has content as its own-row-word coefficient. -/
theorem sum_polytabloidInt_rowWord_swap {t : Tableau n μ} (ht : IsStandard t) (j : Fin n) :
    ∑ i ∈ Finset.Iio j, polytabloidInt t (rowWord t ∘ Equiv.swap i j) =
      tableauContent t j := by
  classical
  simp_rw [Finset.sum_congr rfl (fun i hi => polytabloidInt_rowWord_swap t i j
    (Finset.mem_Iio.mp hi).ne)]
  rw [Finset.sum_sub_distrib]
  simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one,
    ht.1.card_earlier_row, ht.2.card_earlier_column, tableauContent]

/-- The same content coefficient on the actual real standard basis.
This statement does not assert that the standard basis is a Murphy eigenbasis. -/
theorem murphyOperator_standardRealBasis_rowWord (t : Tableau n μ)
    (T : {u : Tableau n μ // IsStandard u}) (j : Fin n) :
    (murphyOperator t j (standardRealBasis t T)).val (rowWord T.val) =
      (tableauContent T.val j : ℝ) := by
  classical
  simp only [murphyOperator, LinearMap.sum_apply, Submodule.coe_sum, WithLp.ofLp_sum,
    Finset.sum_apply,
    realSpechtRep_coe, standardRealBasis_coe, wordRepReal_apply]
  change (∑ i ∈ Finset.Iio j, (polytabloidInt T.val
    (rowWord T.val ∘ Equiv.swap i j) : ℝ)) = _
  rw [← Int.cast_sum, sum_polytabloidInt_rowWord_swap T.property]

end BostConjecture.Specht
