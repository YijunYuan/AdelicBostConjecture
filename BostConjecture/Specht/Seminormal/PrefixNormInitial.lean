/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Specht.Seminormal.PrefixNorm

/-!
# Initial value of the prefix insertion product

The upper-row counts of the literal column-reading tableau are explicit.
Each insertion product telescopes to its one-based row number.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Specht

open OAI.Saxl

/-- In column reading, an upper row already contains exactly the current column plus one boxes. -/
theorem prefixRowCount_rectangleColumnTableau {a k : ℕ} (m : Fin (a * k))
    (r : ℕ) (hr : r < (rectangleColumnTableau a k m).val.1) :
    prefixRowCount (rectangleColumnTableau a k) m r =
      (rectangleColumnTableau a k m).val.2 + 1 := by
  classical
  let t := rectangleColumnTableau a k
  have hlabel := rectangleColumnTableau_label a k
  unfold prefixRowCount
  rw [← Finset.card_range ((t m).val.2 + 1)]
  apply Finset.card_bij (fun l _ => (t l).val.2)
  · intro l hl
    obtain ⟨_, hlm, hlr⟩ := Finset.mem_filter.mp hl
    apply Finset.mem_range.mpr
    by_contra hc
    have hc' : (t m).val.2 + 1 ≤ (t l).val.2 := by omega
    have hm := Nat.mul_le_mul_left a hc'
    have hml : m.val = (t m).val.1 + a * (t m).val.2 := hlabel m
    have hll : l.val = (t l).val.1 + a * (t l).val.2 := hlabel l
    have hra : (t m).val.1 < a := (mem_rectangle.mp (t m).property).1
    change l.val < m.val at hlm
    nlinarith
  · intro l hl q hq he
    obtain ⟨_, _, hlr⟩ := Finset.mem_filter.mp hl
    obtain ⟨_, _, hqr⟩ := Finset.mem_filter.mp hq
    exact t.injective (Subtype.ext (Prod.ext (hlr.trans hqr.symm) he))
  · intro c hc
    have hc' : c ≤ (t m).val.2 := by have := Finset.mem_range.mp hc; omega
    let b : rectangle a k := ⟨(r, c),
      (rectangle a k).up_left_mem hr.le hc' (t m).property⟩
    refine ⟨t.symm b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩, ?_⟩
    · change (t.symm b).val < m.val
      have hl : (t.symm b).val = r + a * c := rectangleColumnTableau_symm_val a k b
      have hm : m.val = (t m).val.1 + a * (t m).val.2 := hlabel m
      have hmul := Nat.mul_le_mul_left a hc'
      rw [hl, hm]
      exact add_lt_add_of_lt_of_le hr hmul
    · change (t (t.symm b)).val.1 = r
      simp [b]
    · simp [b]

theorem prefixAxialDistance_rectangleColumnTableau {a k : ℕ} (m : Fin (a * k))
    (r : ℕ) (hr : r < (rectangleColumnTableau a k m).val.1) :
    prefixAxialDistance (rectangleColumnTableau a k) m r =
      ((rectangleColumnTableau a k m).val.1 : ℤ) - r + 1 := by
  rw [prefixAxialDistance, prefixRowCount_rectangleColumnTableau m r hr]
  push_cast
  ring

private theorem prod_successive_real_ratio (s : ℕ) :
    (∏ r ∈ Finset.range s, ((r : ℝ) + 2) / ((r : ℝ) + 1)) = (s : ℝ) + 1 := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.prod_range_succ, ih]
    push_cast
    have hs : (s : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring

/-- The insertion product down a column telescopes to the one-based row number. -/
theorem prefixInsertionFactor_rectangleColumnTableau {a k : ℕ} (m : Fin (a * k)) :
    prefixInsertionFactor (rectangleColumnTableau a k) m =
      ((rectangleColumnTableau a k m).val.1 : ℝ) + 1 := by
  let s := (rectangleColumnTableau a k m).val.1
  calc
    prefixInsertionFactor (rectangleColumnTableau a k) m =
        ∏ r ∈ Finset.range s,
          (((s - 1 - r : ℕ) : ℝ) + 2) / (((s - 1 - r : ℕ) : ℝ) + 1) := by
      apply Finset.prod_congr rfl
      intro r hr
      have hrl : r < s := Finset.mem_range.mp hr
      rw [prefixAxialDistance_rectangleColumnTableau m r hrl]
      push_cast
      have he : s - 1 - r + r + 1 = s := by omega
      have heR := congrArg (fun l : ℕ => (l : ℝ)) he
      push_cast at heR
      change ((s : ℝ) - r + 1) / ((s : ℝ) - r + 1 - 1) = _
      congr 1 <;> linarith
    _ = ∏ r ∈ Finset.range s, ((r : ℝ) + 2) / ((r : ℝ) + 1) :=
      Finset.prod_range_reflect (fun r => ((r : ℝ) + 2) / ((r : ℝ) + 1)) s
    _ = (s : ℝ) + 1 := prod_successive_real_ratio s

/-- The prefix product at column reading is the independently known initial squared norm. -/
theorem prefixNormProduct_rectangleColumnTableau (a k : ℕ) :
    prefixNormProduct (rectangleColumnTableau a k) = (Nat.factorial a : ℝ) ^ k := by
  classical
  unfold prefixNormProduct
  simp only [prefixInsertionFactor_rectangleColumnTableau]
  rw [(rectangleColumnTableau a k).prod_comp (fun b => ((b.val.1 : ℝ) + 1))]
  calc
    (∏ b : (rectangle a k).cells, ((b.val.1 : ℝ) + 1)) =
        ∏ rc : Fin a × Fin k, ((rc.1 : ℝ) + 1) :=
      ((rectangleCellsEquiv a k).symm.prod_comp (fun b => ((b.val.1 : ℝ) + 1))).symm
    _ = (∏ r : Fin a, ((r : ℝ) + 1)) ^ k := by
      rw [Fintype.prod_prod_type]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.prod_pow]
    _ = (Nat.factorial a : ℝ) ^ k := by
      congr 1
      rw [Fin.prod_univ_eq_prod_range (fun r : ℕ => (r : ℝ) + 1) a]
      exact_mod_cast (Nat.factorial_eq_prod_range_add_one a).symm

end BostConjecture.Specht
