/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Specht.Counting.HookCount

/-!
# Shifted row coordinates and the hook product

The hooks in a row and its shifted differences with later rows partition
an interval. Multiplying these row identities converts the checked hook
formula to the Vandermonde form needed by the rectangular prefix law.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Specht

open OAI.Saxl Finset
open RepresentationTheory.Combinatorics.CornerStatistics

/-- A row length shifted by its distance from the last of `a` rows. -/
def shiftedRowLength (μ : YoungDiagram) (a r : ℕ) : ℕ := μ.rowLen r + a - r - 1

/-- Shifted row lengths are strictly decreasing, including zero-padded rows. -/
theorem shiftedRowLength_strictAnti (μ : YoungDiagram) {a i j : ℕ}
    (hij : i < j) (hj : j < a) : shiftedRowLength μ a j < shiftedRowLength μ a i := by
  have h := μ.rowLen_anti i j hij.le
  unfold shiftedRowLength
  omega

private theorem hook_pos (μ : YoungDiagram) {r q : ℕ} (hq : q < μ.rowLen r) :
    0 < YoungDiagram.auxiliaryCellStatistic μ r q := by
  have hr := YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hq)
  unfold YoungDiagram.auxiliaryCellStatistic
  omega

private theorem hook_strictAnti (μ : YoungDiagram) {r q s : ℕ}
    (hqs : q < s) (hs : s < μ.rowLen r) :
    YoungDiagram.auxiliaryCellStatistic μ r s <
      YoungDiagram.auxiliaryCellStatistic μ r q := by
  have hc := μ.colLen_anti q s hqs.le
  have hp := hook_pos μ hs
  unfold YoungDiagram.auxiliaryCellStatistic at *
  omega

private theorem hook_le_shiftedRowLength (μ : YoungDiagram) {a r q : ℕ}
    (ha : μ.colLen 0 ≤ a) :
    YoungDiagram.auxiliaryCellStatistic μ r q ≤ shiftedRowLength μ a r := by
  have hc := μ.colLen_anti 0 q (Nat.zero_le q)
  unfold YoungDiagram.auxiliaryCellStatistic shiftedRowLength
  omega

private theorem hook_ne_shiftedDifference (μ : YoungDiagram) {a r j q : ℕ}
    (hrj : r < j) (hj : j < a) (hq : q < μ.rowLen r) :
    YoungDiagram.auxiliaryCellStatistic μ r q ≠
      shiftedRowLength μ a r - shiftedRowLength μ a j := by
  have hrow := μ.rowLen_anti r j hrj.le
  have hpos := hook_pos μ hq
  by_cases h : q < μ.rowLen j
  · have hc := YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr h)
    unfold YoungDiagram.auxiliaryCellStatistic shiftedRowLength at *
    omega
  · have hc : μ.colLen q ≤ j := by
      by_contra hc
      exact h (YoungDiagram.mem_iff_lt_rowLen.mp
        (YoungDiagram.mem_iff_lt_colLen.mpr (by omega)))
    unfold YoungDiagram.auxiliaryCellStatistic shiftedRowLength at *
    omega

private theorem row_hook_injOn (μ : YoungDiagram) (r : ℕ) :
    Set.InjOn (YoungDiagram.auxiliaryCellStatistic μ r) (range (μ.rowLen r)) := by
  intro q hq s hs he
  simp only [mem_coe, mem_range] at hq hs
  rcases lt_trichotomy q s with h | h | h
  · exact (ne_of_gt (hook_strictAnti μ h hs) he).elim
  · exact h
  · exact (ne_of_gt (hook_strictAnti μ h hq) he.symm).elim

private theorem shiftedDifference_injOn (μ : YoungDiagram) (a r : ℕ) :
    Set.InjOn (fun j => shiftedRowLength μ a r - shiftedRowLength μ a j) (Ioo r a) := by
  intro i hi j hj he
  simp only [mem_coe, mem_Ioo] at hi hj
  dsimp only at he
  have hi' := shiftedRowLength_strictAnti μ hi.1 hi.2
  have hj' := shiftedRowLength_strictAnti μ hj.1 hj.2
  rcases lt_trichotomy i j with h | h | h
  · have := shiftedRowLength_strictAnti μ h hj.2
    omega
  · exact h
  · have := shiftedRowLength_strictAnti μ h hi.2
    omega
private theorem row_hooks_disjoint_shiftedDifferences (μ : YoungDiagram) (a r : ℕ) : Disjoint
    ((range (μ.rowLen r)).image (YoungDiagram.auxiliaryCellStatistic μ r))
    ((Ioo r a).image (fun j => shiftedRowLength μ a r - shiftedRowLength μ a j)) := by
  apply disjoint_left.mpr
  intro x hx hy
  obtain ⟨q, hq, rfl⟩ := mem_image.mp hx
  obtain ⟨j, hj, he⟩ := mem_image.mp hy
  exact hook_ne_shiftedDifference μ (mem_Ioo.mp hj).1 (mem_Ioo.mp hj).2
    (mem_range.mp hq) he.symm

/-- This paper, proof of Proposition 3.15.

The hooks of one row and the differences with all subsequent shifted
rows partition the interval from one to its shifted length. -/
theorem row_hooks_union_shiftedDifferences (μ : YoungDiagram) {a r : ℕ}
    (ha : μ.colLen 0 ≤ a) (hr : r < a) :
    ((range (μ.rowLen r)).image (YoungDiagram.auxiliaryCellStatistic μ r)) ∪
      ((Ioo r a).image (fun j => shiftedRowLength μ a r - shiftedRowLength μ a j)) =
      Ico 1 (shiftedRowLength μ a r + 1) := by
  have hH := row_hook_injOn μ r
  have hG := shiftedDifference_injOn μ a r
  have hd := row_hooks_disjoint_shiftedDifferences μ a r
  apply eq_of_subset_of_card_le
  · intro x hx
    rcases mem_union.mp hx with hx | hx
    · obtain ⟨q, hq, rfl⟩ := mem_image.mp hx
      have hp := hook_pos μ (mem_range.mp hq)
      have hb := hook_le_shiftedRowLength (r := r) (q := q) μ ha
      exact mem_Ico.mpr ⟨hp, by omega⟩
    · obtain ⟨j, hj, rfl⟩ := mem_image.mp hx
      have hl := shiftedRowLength_strictAnti μ (mem_Ioo.mp hj).1 (mem_Ioo.mp hj).2
      exact mem_Ico.mpr ⟨by omega, by omega⟩
  · rw [card_union_of_disjoint hd, card_image_of_injOn hH, card_image_of_injOn hG]
    simp only [card_range, Nat.card_Ioo, Nat.card_Ico, shiftedRowLength]
    omega

/-- Multiplication of the row interval partition gives the factorial identity. -/
theorem row_hookProduct_mul_shiftedDifferences (μ : YoungDiagram) {a r : ℕ}
    (ha : μ.colLen 0 ≤ a) (hr : r < a) :
    (∏ q ∈ range (μ.rowLen r), YoungDiagram.auxiliaryCellStatistic μ r q) *
      (∏ j ∈ Ioo r a, (shiftedRowLength μ a r - shiftedRowLength μ a j)) =
      (shiftedRowLength μ a r).factorial := by
  have hH := row_hook_injOn μ r
  have hG := shiftedDifference_injOn μ a r
  have hd := row_hooks_disjoint_shiftedDifferences μ a r
  have hp := congrArg (fun s : Finset ℕ => ∏ x ∈ s, x)
    (row_hooks_union_shiftedDifferences μ ha hr)
  rwa [prod_union hd, prod_image hH, prod_image hG, prod_Ico_id_eq_factorial] at hp

/-- Row grouping of the hook product, allowing zero-padded rows. -/
theorem hookProduct_eq_prod_rows (μ : YoungDiagram) {a : ℕ} (ha : μ.colLen 0 ≤ a) :
    (∏ c ∈ μ.cells, YoungDiagram.auxiliaryCellStatistic μ c.1 c.2) =
      ∏ r ∈ range a, ∏ q ∈ range (μ.rowLen r), YoungDiagram.auxiliaryCellStatistic μ r q := by
  have hmem : ∀ c ∈ μ.cells, c.1 ∈ range a := by
    intro c hc
    have h0 := μ.up_left_mem (le_refl c.1) (Nat.zero_le c.2) hc
    exact mem_range.mpr ((YoungDiagram.mem_iff_lt_colLen.mp h0).trans_le ha)
  rw [← prod_fiberwise_of_maps_to hmem]
  apply prod_congr rfl
  intro r _
  change (∏ c ∈ μ.row r, YoungDiagram.auxiliaryCellStatistic μ c.1 c.2) = _
  rw [YoungDiagram.row_eq_prod]
  simp

/-- The total hook product times the shifted Vandermonde is the product of
shifted factorials. -/
theorem hookProduct_mul_shiftedVandermonde (μ : YoungDiagram) {a : ℕ}
    (ha : μ.colLen 0 ≤ a) :
    (∏ c ∈ μ.cells, YoungDiagram.auxiliaryCellStatistic μ c.1 c.2) *
      (∏ r ∈ range a, ∏ j ∈ Ioo r a,
        (shiftedRowLength μ a r - shiftedRowLength μ a j)) =
      ∏ r ∈ range a, (shiftedRowLength μ a r).factorial := by
  rw [hookProduct_eq_prod_rows μ ha, ← prod_mul_distrib]
  exact prod_congr rfl fun r hr => row_hookProduct_mul_shiftedDifferences μ ha (mem_range.mp hr)

/-- This paper, equation (3.14). This is the shifted form of [Frame–Robinson–Thrall][frt].

Shifted-coordinate enumeration without division, valid also for the empty diagram. -/
theorem card_standard_mul_shiftedFactorials (μ : YoungDiagram) {n a : ℕ}
    (hn : μ.card = n) (ha : μ.colLen 0 ≤ a) :
    Fintype.card {t : Tableau n μ // IsStandard t} *
      (∏ r ∈ range a, (shiftedRowLength μ a r).factorial) =
      n.factorial * (∏ r ∈ range a, ∏ j ∈ Ioo r a,
        (shiftedRowLength μ a r - shiftedRowLength μ a j)) := by
  rw [← hookProduct_mul_shiftedVandermonde μ ha, ← mul_assoc]
  simp only [YoungDiagram.auxiliaryCellStatistic]
  rw [card_standard_mul_hookProduct μ hn]

end BostConjecture.Specht

