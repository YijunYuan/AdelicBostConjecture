module

public import BostConjecture.Specht.ColumnReading

/-!
# Legal adjacent paths between standard rectangular tableaux

Every noninitial standard tableau admits a legal colex-decreasing adjacent
swap. Finite induction connects all tableaux to the column-reading tableau.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Specht

open OAI.Saxl
open scoped StandardColex

variable {n : ℕ} {μ : YoungDiagram}

private theorem lt_of_adjacent_swap_lt {i j x y : Fin n} (hij : i.val + 1 = j.val)
    (hxy : Equiv.swap i j x < Equiv.swap i j y) (he : ¬(x = j ∧ y = i)) : x < y := by
  simp only [Equiv.swap_apply_def] at hxy
  split_ifs at hxy <;> simp_all [Fin.ext_iff] <;> omega

/-- Swapping consecutive labels in different rows and columns preserves standardness. -/
theorem IsStandard.relabel_adjacent {t : Tableau n μ} (ht : IsStandard t)
    (i j : Fin n) (hij : i.val + 1 = j.val)
    (hr : (t i).val.1 ≠ (t j).val.1) (hc : (t i).val.2 ≠ (t j).val.2) :
    IsStandard (relabel (Equiv.swap i j) t) := by
  have he (l : Fin n) : relabel (Equiv.swap i j) t l = t (Equiv.swap i j l) := by
    simp [relabel]
  constructor
  · intro x y hrow hcol
    simp only [he] at hrow hcol
    apply lt_of_adjacent_swap_lt hij (ht.1 _ _ hrow hcol)
    rintro ⟨rfl, rfl⟩
    exact hr (by simpa only [Equiv.swap_apply_left, Equiv.swap_apply_right] using hrow)
  · intro x y hcol hrow
    simp only [he] at hrow hcol
    apply lt_of_adjacent_swap_lt hij (ht.2 _ _ hcol hrow)
    rintro ⟨rfl, rfl⟩
    exact hc (by simpa only [Equiv.swap_apply_left, Equiv.swap_apply_right] using hcol)

/-- A nonidentity permutation of a finite chain has a consecutive descent. -/
private theorem exists_adjacent_descent (p : Equiv.Perm (Fin n)) (hp : p ≠ 1) :
    ∃ i j, i.val + 1 = j.val ∧ p j < p i := by
  by_contra! h
  have hm : StrictMono p := by
    cases n with
    | zero => exact fun i => Fin.elim0 i
    | succ n =>
      apply Fin.strictMono_iff_lt_succ.mpr
      intro i
      exact lt_of_le_of_ne (h i.castSucc i.succ rfl)
        (fun he => (Fin.castSucc_lt_succ (i := i)).ne (p.injective he))
  have he : p = 1 := by
    apply Equiv.ext
    intro i
    induction i using WellFoundedLT.induction with
    | ind i ih =>
      rcases lt_trichotomy (p i) i with hlt | he | hgt
      · have he' := ih (p i) hlt
        exact p.injective (by simpa using he')
      · exact he
      · have hpre : p.symm i < i := by
          by_contra hpre
          have hh := hm.monotone (le_of_not_gt hpre)
          simp only [Equiv.apply_symm_apply] at hh
          exact (not_le_of_gt hgt) hh
        have hh := ih (p.symm i) hpre
        have hh' : i = p.symm i := by simpa using hh
        exact (hpre.ne hh'.symm).elim
  exact hp he

/-- A noninitial standard rectangle admits an adjacent pair inverted in column-reading order. -/
theorem exists_rectangle_adjacent_descent {a k : ℕ}
    (t : Tableau (a * k) (rectangle a k)) (ht : IsStandard t)
    (hne : t ≠ rectangleColumnTableau a k) :
    ∃ i j : Fin (a * k), i.val + 1 = j.val ∧
      (t i).val.1 < (t j).val.1 ∧ (t j).val.2 < (t i).val.2 := by
  let v := rectangleColumnTableau a k
  let p : Equiv.Perm (Fin (a * k)) := t.trans v.symm
  have hp : p ≠ 1 := by
    intro he
    apply hne
    apply Equiv.ext
    intro i
    have hi := Equiv.congr_fun he i
    have hi' : v.symm (t i) = i := hi
    simpa using congrArg v hi'
  obtain ⟨i, j, hij, hdesc⟩ := exists_adjacent_descent p hp
  have hij' : i < j := by simp only [Fin.lt_def]; omega
  have hdesc' : (t j).val.1 + a * (t j).val.2 <
      (t i).val.1 + a * (t i).val.2 := hdesc
  have hcol : (t j).val.2 < (t i).val.2 := by
    rcases lt_trichotomy (t j).val.2 (t i).val.2 with hh | hh | hh
    · exact hh
    · have hr := (ht.2.lt_iff_row_lt hh.symm).mp hij'
      rw [hh] at hdesc'
      omega
    · have hm := Nat.mul_le_mul_left a (show (t i).val.2 + 1 ≤ (t j).val.2 by omega)
      have hrange : (t i).val.1 < a := (mem_rectangle.mp (t i).property).1
      nlinarith
  have hrow : (t i).val.1 < (t j).val.1 := by
    by_contra hrow
    have hh := ht.label_mono (b := t j) (c := t i) ⟨le_of_not_gt hrow, hcol.le⟩
    simp only [Equiv.symm_apply_apply] at hh
    exact (not_le_of_gt hij') hh
  exact ⟨i, j, hij, hrow, hcol⟩

/-- Swapping such a pair strictly decreases colex order. -/
theorem tableauColexLT_relabel_adjacent (t : Tableau n μ) (i j : Fin n)
    (hij : i.val + 1 = j.val) (hr : (t i).val.1 < (t j).val.1) :
    TableauColexLT (relabel (Equiv.swap i j) t) t := by
  refine ⟨j, ?_, ?_⟩
  · simpa [relabel] using hr
  · intro l hl
    have hli : l ≠ i := by intro he; subst l; simp only [Fin.lt_def] at hl; omega
    have hlj : l ≠ j := hl.ne'
    simp [relabel, Equiv.swap_apply_of_ne_of_ne hli hlj]

/-- The finite legal-swap graph is connected by paths increasing from column reading. -/
theorem rectangle_standard_adjacent_path (a k : ℕ)
    (T : {t : Tableau (a * k) (rectangle a k) // IsStandard t}) :
    Relation.ReflTransGen
      (fun U V : {t : Tableau (a * k) (rectangle a k) // IsStandard t} =>
        U < V ∧ ∃ i j : Fin (a * k), i.val + 1 = j.val ∧
          V.val = relabel (Equiv.swap i j) U.val)
      ⟨rectangleColumnTableau a k, rectangleColumnTableau_isStandard a k⟩ T := by
  induction T using WellFoundedLT.induction with
  | ind T ih =>
    by_cases he : T.val = rectangleColumnTableau a k
    · have he' : T = ⟨rectangleColumnTableau a k, rectangleColumnTableau_isStandard a k⟩ :=
        Subtype.ext he
      subst T
      exact Relation.ReflTransGen.refl
    · obtain ⟨i, j, hij, hr, hc⟩ := exists_rectangle_adjacent_descent T.val T.property he
      let U : {t : Tableau (a * k) (rectangle a k) // IsStandard t} :=
        ⟨relabel (Equiv.swap i j) T.val,
          T.property.relabel_adjacent i j hij hr.ne hc.ne'⟩
      have hUT : U < T := (standardColex_lt_iff U T).mpr
        (tableauColexLT_relabel_adjacent T.val i j hij hr)
      apply Relation.ReflTransGen.tail (ih U hUT)
      refine ⟨hUT, i, j, hij, ?_⟩
      apply Equiv.ext
      intro l
      simp [U, relabel]

end BostConjecture.Specht
