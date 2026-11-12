/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Specht.Tableau.Prefix

/-!
# The explicit prefix insertion product

Prefix row counts are statistics of the existing enumerating tableau. The
positive rational insertion factors are this paper's monic
squared-norm product; identification with the actual norm is separate.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Specht

open OAI.Saxl

variable {n : ℕ} {μ : YoungDiagram}

/-- The number of labels before `m` in row `r`. -/
def prefixRowCount (t : Tableau n μ) (m : Fin n) (r : ℕ) : ℕ :=
  (Finset.univ.filter fun l => l < m ∧ (t l).val.1 = r).card

/-- The integer distance from an earlier row end to the newly inserted box. -/
def prefixAxialDistance (t : Tableau n μ) (m : Fin n) (r : ℕ) : ℤ :=
  (prefixRowCount t m r : ℤ) - (t m).val.2 + (t m).val.1 - r

/-- The contribution of the insertion of one box. -/
def prefixInsertionFactor (t : Tableau n μ) (m : Fin n) : ℝ :=
  ∏ r ∈ Finset.range (t m).val.1,
    (prefixAxialDistance t m r : ℝ) / ((prefixAxialDistance t m r : ℝ) - 1)

/-- The concrete product over all successive row insertions. -/
def prefixNormProduct (t : Tableau n μ) : ℝ := ∏ m, prefixInsertionFactor t m

/-- In the row of the current box, its column counts exactly the earlier labels. -/
theorem prefixRowCount_self {t : Tableau n μ} [ht : IsStandard t] (m : Fin n) :
    prefixRowCount t m (t m).val.1 = (t m).val.2 := by
  classical
  unfold prefixRowCount
  rw [← Finset.card_range (t m).val.2]
  apply Finset.card_bij (fun l _ => (t l).val.2)
  · intro l hl
    obtain ⟨_, hlm, hr⟩ := Finset.mem_filter.mp hl
    exact Finset.mem_range.mpr ((RowStandard.lt_iff_col_lt (t := t) hr).mp hlm)
  · intro l hl q hq he
    obtain ⟨_, _, hlr⟩ := Finset.mem_filter.mp hl
    obtain ⟨_, _, hqr⟩ := Finset.mem_filter.mp hq
    exact t.injective (Subtype.ext (Prod.ext (hlr.trans hqr.symm) he))
  · intro c hc
    have hc' : c < (t m).val.2 := Finset.mem_range.mp hc
    let b : μ := ⟨((t m).val.1, c), μ.up_left_mem le_rfl hc'.le (t m).property⟩
    refine ⟨t.symm b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩, ?_⟩
    · exact ht.rowStandard.label_lt _ m (by simp [b]) (by simpa [b] using hc')
    · simp [b]
    · simp [b]

/-- Every row above the current box already contains its column and all preceding columns. -/
theorem col_add_one_le_prefixRowCount {t : Tableau n μ} [ht : IsStandard t]
    (m : Fin n) (r : ℕ) (hr : r < (t m).val.1) :
    (t m).val.2 + 1 ≤ prefixRowCount t m r := by
  classical
  let s := Finset.univ.filter fun l : Fin n => l < m ∧ (t l).val.1 = r
  let f : Fin ((t m).val.2 + 1) → s := fun c =>
    let b : μ := ⟨(r, c.val), μ.up_left_mem hr.le (Nat.le_of_lt_succ c.isLt) (t m).property⟩
    ⟨t.symm b, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      lt_of_le_of_ne (by
        simpa using IsStandard.label_mono (t := t) (b := b) (c := t m)
          ⟨hr.le, show c.val ≤ (t m).val.2 from Nat.le_of_lt_succ c.isLt⟩)
        (by
          intro he
          have hh := congrArg (fun l => (t l).val.1) he
          simp only [Equiv.apply_symm_apply] at hh
          exact hr.ne hh), by simp [b]⟩⟩
  have hf : Function.Injective f := by
    intro c d he
    have hh := congrArg (fun z : s => (t z.val).val.2) he
    exact Fin.ext (by simpa [f] using hh)
  simpa only [Fintype.card_fin, Fintype.card_coe, s, prefixRowCount] using
    Fintype.card_le_of_injective f hf

/-- All factors that occur in the prefix product have distance at least two. -/
theorem two_le_prefixAxialDistance {t : Tableau n μ} [ht : IsStandard t]
    (m : Fin n) (r : ℕ) (hr : r < (t m).val.1) : 2 ≤ prefixAxialDistance t m r := by
  have hc := col_add_one_le_prefixRowCount (t := t) m r hr
  unfold prefixAxialDistance
  omega

theorem prefixInsertionFactor_pos {t : Tableau n μ} [ht : IsStandard t] (m : Fin n) :
    0 < prefixInsertionFactor t m := by
  apply Finset.prod_pos
  intro r hr
  have hd : (2 : ℝ) ≤ prefixAxialDistance t m r := by
    exact_mod_cast two_le_prefixAxialDistance (t := t) m r (Finset.mem_range.mp hr)
  exact div_pos (by linarith) (by linarith)

/-- Consecutive prefixes differ by the row of the intervening label. -/
theorem prefixRowCount_succ (t : Tableau n μ) (i j : Fin n)
    (hij : i.val + 1 = j.val) (r : ℕ) :
    prefixRowCount t j r = prefixRowCount t i r + if (t i).val.1 = r then 1 else 0 := by
  classical
  by_cases hr : (t i).val.1 = r
  · have he : (Finset.univ.filter fun l : Fin n => l < j ∧ (t l).val.1 = r) =
        insert i (Finset.univ.filter fun l => l < i ∧ (t l).val.1 = r) := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      by_cases hl : l = i
      · subst l
        simp only [hr, and_true, true_or, iff_true]
        change i.val < j.val
        omega
      · simp only [hl, false_or]
        have hlt : l < j ↔ l < i := by simp only [Fin.lt_def]; simp only [Fin.ext_iff] at hl; omega
        rw [hlt]
    simp only [prefixRowCount, he, ite_eq_left hr]
    rw [Finset.card_insert_of_notMem (by simp)]
  · have he : (Finset.univ.filter fun l : Fin n => l < j ∧ (t l).val.1 = r) =
        (Finset.univ.filter fun l => l < i ∧ (t l).val.1 = r) := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hl : l = i
      · subst l; simp [hr]
      · have hlt : l < j ↔ l < i := by simp only [Fin.lt_def]; simp only [Fin.ext_iff] at hl; omega
        rw [hlt]
    simp only [prefixRowCount, he, ite_eq_right hr, add_zero]

/-- Away from the single intervening prefix, an adjacent relabeling preserves all row counts. -/
theorem prefixRowCount_relabel_adjacent (t : Tableau n μ) (i j : Fin n)
    (hij : i.val + 1 = j.val) (m : Fin n) (hm : m ≠ j) (r : ℕ) :
    prefixRowCount (relabel (Equiv.swap i j) t) m r = prefixRowCount t m r := by
  classical
  have hprefix (l : Fin n) : Equiv.swap i j l < m ↔ l < m := by
    simp only [Equiv.swap_apply_def]
    split_ifs <;> simp_all [Fin.ext_iff] <;> omega
  have he (l : Fin n) : relabel (Equiv.swap i j) t l = t (Equiv.swap i j l) := by
    simp [relabel]
  unfold prefixRowCount
  apply Finset.card_bij (fun l _ => Equiv.swap i j l)
  · intro l hl
    obtain ⟨_, hlm, hr⟩ := Finset.mem_filter.mp hl
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (hprefix l).mpr hlm, by simpa only [he] using hr⟩
  · intro l hl q hq heq
    exact (Equiv.swap i j).injective heq
  · intro l hl
    obtain ⟨_, hlm, hr⟩ := Finset.mem_filter.mp hl
    refine ⟨Equiv.swap i j l, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (hprefix l).mpr hlm, ?_⟩, Equiv.swap_apply_self i j l⟩
    simpa only [he, Equiv.swap_apply_self] using hr

/-- The changed intervening prefix inserts the other row. -/
theorem prefixRowCount_relabel_adjacent_succ (t : Tableau n μ) (i j : Fin n)
    (hij : i.val + 1 = j.val) (r : ℕ) :
    prefixRowCount (relabel (Equiv.swap i j) t) j r =
      prefixRowCount t i r + if (t j).val.1 = r then 1 else 0 := by
  rw [prefixRowCount_succ _ i j hij,
    prefixRowCount_relabel_adjacent t i j hij i (by intro h; have := congrArg Fin.val h; omega)]
  simp [relabel]

/-- Every insertion except the two exchanged labels is unchanged. -/
theorem prefixInsertionFactor_relabel_adjacent_of_ne (t : Tableau n μ) (i j : Fin n)
    (hij : i.val + 1 = j.val) (m : Fin n) (hmi : m ≠ i) (hmj : m ≠ j) :
    prefixInsertionFactor (relabel (Equiv.swap i j) t) m = prefixInsertionFactor t m := by
  have hb : relabel (Equiv.swap i j) t m = t m := by
    simp [relabel, Equiv.swap_apply_of_ne_of_ne hmi hmj]
  simp only [prefixInsertionFactor, prefixAxialDistance, hb,
    prefixRowCount_relabel_adjacent t i j hij m hmj]

/-- In a lower-then-upper swap, the upper insertion sees no change in earlier upper rows. -/
theorem prefixInsertionFactor_relabel_adjacent_left (t : Tableau n μ) (i j : Fin n)
    (hij : i.val + 1 = j.val) (hr : (t j).val.1 < (t i).val.1) :
    prefixInsertionFactor (relabel (Equiv.swap i j) t) i = prefixInsertionFactor t j := by
  have hne : i ≠ j := by intro h; have := congrArg Fin.val h; omega
  have hb : relabel (Equiv.swap i j) t i = t j := by simp [relabel]
  simp only [prefixInsertionFactor, hb]
  apply Finset.prod_congr rfl
  intro r hmem
  have hri : (t i).val.1 ≠ r := by have := Finset.mem_range.mp hmem; omega
  simp only [prefixAxialDistance, hb, prefixRowCount_relabel_adjacent t i j hij i hne,
    prefixRowCount_succ t i j hij, ite_eq_right hri, add_zero]

/-- Only one factor changes in the lower insertion. -/
theorem prefixInsertionFactor_relabel_adjacent_right {t : Tableau n μ} [ht : IsStandard t]
    (i j : Fin n) (hij : i.val + 1 = j.val) (hr : (t j).val.1 < (t i).val.1) :
    prefixInsertionFactor (relabel (Equiv.swap i j) t) j =
      (1 - ((prefixAxialDistance t i (t j).val.1 : ℝ)⁻¹) ^ 2) * prefixInsertionFactor t i := by
  classical
  let q := (t j).val.1
  let A : ℝ := 1 - ((prefixAxialDistance t i q : ℝ)⁻¹) ^ 2
  have hb : relabel (Equiv.swap i j) t j = t i := by simp [relabel]
  have hd (r : ℕ) : prefixAxialDistance (relabel (Equiv.swap i j) t) j r =
      prefixAxialDistance t i r + if q = r then 1 else 0 := by
    simp only [prefixAxialDistance, hb, prefixRowCount_relabel_adjacent_succ t i j hij]
    dsimp [q]
    split_ifs <;> push_cast <;> ring
  have heach (r : ℕ) :
      (prefixAxialDistance (relabel (Equiv.swap i j) t) j r : ℝ) /
        ((prefixAxialDistance (relabel (Equiv.swap i j) t) j r : ℝ) - 1) =
      (if r = q then A else 1) *
        ((prefixAxialDistance t i r : ℝ) / ((prefixAxialDistance t i r : ℝ) - 1)) := by
    by_cases he : r = q
    · subst r
      rw [hd]
      norm_num only [Int.cast_add]
      simp only [ite_true, Int.cast_one, add_sub_cancel_right]
      have hp : (2 : ℝ) ≤ prefixAxialDistance t i q := by
        exact_mod_cast two_le_prefixAxialDistance (t := t) i q hr
      have h0 : (prefixAxialDistance t i q : ℝ) ≠ 0 := by linarith
      have h1 : (prefixAxialDistance t i q : ℝ) - 1 ≠ 0 := by linarith
      dsimp [A]
      field_simp [h0, h1]
      ring
    · rw [hd, ite_eq_right (Ne.symm he), add_zero, ite_eq_right he, one_mul]
  simp only [prefixInsertionFactor, hb]
  rw [Finset.prod_congr rfl (fun r _ => heach r), Finset.prod_mul_distrib]
  have hprod : ∏ r ∈ Finset.range (t i).val.1, (if r = q then A else 1) = A := by
    rw [Finset.prod_eq_single q]
    · simp
    · intro r hr hrq; simp [hrq]
    · intro hq; exact (hq (Finset.mem_range.mpr hr)).elim
  rw [hprod]

/-- The distance in the changed prefix factor is exactly the adjacent content difference. -/
theorem prefixAxialDistance_eq_content_sub {t : Tableau n μ} [ht : IsStandard t]
    (i j : Fin n) (hij : i.val + 1 = j.val) (hr : (t j).val.1 < (t i).val.1) :
    prefixAxialDistance t i (t j).val.1 = tableauContent t j - tableauContent t i := by
  have he := prefixRowCount_succ t i j hij (t j).val.1
  rw [prefixRowCount_self (t := t) j, ite_eq_right hr.ne', add_zero] at he
  simp only [prefixAxialDistance, tableauContent, ← he]
  ring

/-- The explicit prefix product satisfies the same legal adjacent ratio as the monic norm. -/
theorem prefixNormProduct_relabel_adjacent {t : Tableau n μ} [ht : IsStandard t]
    (i j : Fin n) (hij : i.val + 1 = j.val) (hr : (t j).val.1 < (t i).val.1) :
    prefixNormProduct (relabel (Equiv.swap i j) t) =
      (1 - (((tableauContent t j : ℝ) - tableauContent t i)⁻¹) ^ 2) * prefixNormProduct t := by
  classical
  let A : ℝ := 1 - ((prefixAxialDistance t i (t j).val.1 : ℝ)⁻¹) ^ 2
  have hne : i ≠ j := by intro h; have := congrArg Fin.val h; omega
  have heach (m : Fin n) : prefixInsertionFactor (relabel (Equiv.swap i j) t) m =
      (if m = j then A else 1) * prefixInsertionFactor t (Equiv.swap i j m) := by
    by_cases hmi : m = i
    · subst m
      rw [Equiv.swap_apply_left, ite_eq_right hne, one_mul]
      exact prefixInsertionFactor_relabel_adjacent_left t i j hij hr
    by_cases hmj : m = j
    · subst m
      rw [Equiv.swap_apply_right, ite_eq_left rfl]
      exact prefixInsertionFactor_relabel_adjacent_right (t := t) i j hij hr
    rw [Equiv.swap_apply_of_ne_of_ne hmi hmj, ite_eq_right hmj, one_mul]
    exact prefixInsertionFactor_relabel_adjacent_of_ne t i j hij m hmi hmj
  unfold prefixNormProduct
  rw [Finset.prod_congr rfl (fun m _ => heach m), Finset.prod_mul_distrib]
  have hprod : ∏ m : Fin n, (if m = j then A else 1) = A := by simp
  rw [hprod, Equiv.prod_comp]
  congr 1
  simp only [A, prefixAxialDistance_eq_content_sub (t := t) i j hij hr, Int.cast_sub]

end BostConjecture.Specht
