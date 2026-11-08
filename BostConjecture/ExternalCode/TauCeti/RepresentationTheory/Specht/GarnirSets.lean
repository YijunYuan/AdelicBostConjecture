/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-
Adapted from TauCetiProject/TauCeti at b3b0334ab9203d9faee4b2f34cd75161463ecdd0.
Original paths: RepresentationTheory/Symmetric/Specht/Garnir.lean and
Combinatorics/Young/Diagram.lean (under TauCeti/).
See CONTRIBUTIONS.md for the local changes and consumers.
-/
module

public import BostConjecture.Specht.Tableau.Basic

/-!
# Garnir sets in the enumerating-tableau model

The two adjacent-column halves have one more label than the earlier column
has rows. A permutation supported in their union preserves columns exactly
when it preserves the left half.

## Source

Adapted from <https://github.com/TauCetiProject/TauCeti>, revision
`b3b0334ab9203d9faee4b2f34cd75161463ecdd0`.
Original sources:
* `TauCeti/RepresentationTheory/Symmetric/Specht/Garnir.lean`.
* `TauCeti/Combinatorics/Young/Diagram.lean`.

The original declaration namespaces and license notices are retained, except for
project-specific adaptations documented in `CONTRIBUTIONS.md`.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Specht

open OAI.Saxl

variable {n : ℕ} {μ : YoungDiagram}

/-- Row coordinate of a label. -/
abbrev rowIndex (t : Tableau n μ) (k : Fin n) : ℕ := (t k).val.1

/-- Column coordinate of a label. -/
abbrev colIndex (t : Tableau n μ) (k : Fin n) : ℕ := (t k).val.2

theorem rowIndex_colIndex_mem (t : Tableau n μ) (k : Fin n) :
    (rowIndex t k, colIndex t k) ∈ μ := (t k).property

theorem rowIndex_colIndex_injective (t : Tableau n μ) :
    Function.Injective (fun k => (rowIndex t k, colIndex t k)) :=
  fun _ _ h => t.injective (Subtype.ext h)

theorem exists_rowIndex_colIndex (t : Tableau n μ) {i j : ℕ} (h : (i, j) ∈ μ) :
    ∃ k, rowIndex t k = i ∧ colIndex t k = j :=
  ⟨t.symm ⟨(i, j), h⟩, by simp [rowIndex], by simp [colIndex]⟩

@[simp] theorem rowIndex_relabel (σ : Equiv.Perm (Fin n)) (t : Tableau n μ) (k : Fin n) :
    rowIndex (relabel σ t) k = rowIndex t (σ⁻¹ k) := rfl

@[simp] theorem colIndex_relabel (σ : Equiv.Perm (Fin n)) (t : Tableau n μ) (k : Fin n) :
    colIndex (relabel σ t) k = colIndex t (σ⁻¹ k) := rfl

private theorem card_filter_fst_lt_filter_snd_eq (lam : YoungDiagram) (k j : ℕ) :
    (((lam.cells.filter fun c => c.1 < k)).filter fun c => c.2 = j).card
      = min k (lam.colLen j) := by
  have himg : (((lam.cells.filter fun c => c.1 < k)).filter fun c => c.2 = j)
      = (Finset.range (min k (lam.colLen j))).image fun i => (i, j) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range, lt_min_iff,
      _root_.YoungDiagram.mem_cells]
    constructor
    · rintro ⟨⟨hc, hk⟩, hj⟩
      refine ⟨c.1, ⟨hk, ?_⟩, ?_⟩
      · exact _root_.YoungDiagram.mem_iff_lt_colLen.mp (hj ▸ hc)
      · rw [← hj]
    · rintro ⟨i, ⟨hik, hicol⟩, rfl⟩
      exact ⟨⟨_root_.YoungDiagram.mem_iff_lt_colLen.mpr hicol, hik⟩, rfl⟩
  rw [himg, Finset.card_image_of_injective _ fun _ _ h => congrArg Prod.fst h, Finset.card_range]

/-- The **Garnir set** of a tableau `t` at row `i` and column `j`: the labels of `t` lying in
column `j` from row `i` downwards, together with those lying in column `j + 1` from row `i`
upwards.

When `(i, j + 1)` is a cell of `μ` this set has one element more than column `j` has cells, while
its labels stay in column `j` or `j + 1` under a column permutation of `t`; that is what makes the
Garnir relation apply to it. -/
def garnirSet (t : Tableau n μ) (i j : ℕ) : Finset (Fin n) :=
  {k | (colIndex t k = j ∧ i ≤ rowIndex t k) ∨ (colIndex t k = j + 1 ∧ rowIndex t k ≤ i)}

@[simp]
theorem mem_garnirSet {t : Tableau n μ} {i j : ℕ} {k : Fin n} :
    k ∈ garnirSet t i j ↔
      (colIndex t k = j ∧ i ≤ rowIndex t k) ∨ (colIndex t k = j + 1 ∧ rowIndex t k ≤ i) := by
  simp [garnirSet]

/-- Every label of a Garnir set at column `j` lies in a column with at most as many cells as column
`j` has, since columns of a Young diagram shorten to the right. -/
theorem colLen_colIndex_le_colLen_of_mem_garnirSet {t : Tableau n μ} {i j : ℕ}
    {k : Fin n} (hk : k ∈ garnirSet t i j) : μ.colLen (colIndex t k) ≤ μ.colLen j := by
  rcases mem_garnirSet.mp hk with ⟨hcol, -⟩ | ⟨hcol, -⟩
  · rw [hcol]
  · rw [hcol]
    exact μ.colLen_anti j (j + 1) (Nat.le_succ j)

/-- The cells occupied by a Garnir set: those of column `j` from row `i` down, and those of column
`j + 1` from row `i` up. -/
private theorem image_rowIndex_colIndex_garnirSet (t : Tableau n μ) (i j : ℕ) :
    (garnirSet t i j).image (fun k => (rowIndex t k, colIndex t k)) =
      {c ∈ μ.cells | (c.2 = j ∧ i ≤ c.1) ∨ (c.2 = j + 1 ∧ c.1 ≤ i)} := by
  ext c
  simp only [Finset.mem_image, mem_garnirSet, Finset.mem_filter]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨rowIndex_colIndex_mem t k, hk⟩
  · rintro ⟨hmem, hc⟩
    refine ⟨t.symm ⟨c, hmem⟩, ?_, ?_⟩ <;> simp [rowIndex, colIndex, hc]

/-- The cells of column `j` from row `i` down are those of the whole column that the first `i`
rows leave over. -/
private theorem card_filter_cells_col (i j : ℕ) :
    {c ∈ μ.cells | c.2 = j ∧ i ≤ c.1}.card = μ.colLen j - i := by
  have htop : {c ∈ μ.col j | c.1 < i} = {c ∈ {c ∈ μ.cells | c.1 < i} | c.2 = j} := by
    simp [YoungDiagram.col, Finset.filter_filter, and_comm]
  have hbot : {c ∈ μ.col j | ¬ c.1 < i} = {c ∈ μ.cells | c.2 = j ∧ i ≤ c.1} := by
    simp [YoungDiagram.col, Finset.filter_filter]
  have hsplit := Finset.card_filter_add_card_filter_not (s := μ.col j)
    (p := fun c : ℕ × ℕ => c.1 < i)
  rw [htop, hbot, card_filter_fst_lt_filter_snd_eq, ← μ.colLen_eq_card] at hsplit
  omega

/-- The cells of column `j + 1` from row `i` up are those of that column in the first `i + 1`
rows, and `(i, j + 1) ∈ μ` says the column reaches that far. -/
private theorem card_filter_cells_col_succ {i j : ℕ} (h : (i, j + 1) ∈ μ) :
    {c ∈ μ.cells | c.2 = j + 1 ∧ c.1 ≤ i}.card = i + 1 := by
  have hlt : i < μ.colLen (j + 1) := YoungDiagram.mem_iff_lt_colLen.mp h
  -- the counting lemma filters the first `i + 1` rows before the column, so its nested filter
  -- has to be flattened into the single filter of the statement
  have hflat : {c ∈ {c ∈ μ.cells | c.1 < i + 1} | c.2 = j + 1} =
      {c ∈ μ.cells | c.2 = j + 1 ∧ c.1 ≤ i} := by
    simp [Finset.filter_filter, and_comm]
  have hcard := card_filter_fst_lt_filter_snd_eq μ (i + 1) (j + 1)
  rw [hflat] at hcard
  omega

/-- **A Garnir set is one bigger than the column it straddles.**  Column `j` contributes its cells
from row `i` down and column `j + 1` its cells from row `i` up, and `(i, j + 1) ∈ μ` makes both
counts available. -/
theorem card_garnirSet (t : Tableau n μ) {i j : ℕ} (h : (i, j + 1) ∈ μ) :
    (garnirSet t i j).card = μ.colLen j + 1 := by
  classical
  have hij : (i, j) ∈ μ := μ.up_left_mem (le_refl i) (Nat.le_succ j) h
  have hi : i < μ.colLen j := YoungDiagram.mem_iff_lt_colLen.mp hij
  have hinj : Function.Injective fun k : Fin n => (rowIndex t k, colIndex t k) :=
    rowIndex_colIndex_injective t
  have hcard := Finset.card_image_of_injective (garnirSet t i j) hinj
  rw [image_rowIndex_colIndex_garnirSet] at hcard
  have hdisj :
      Disjoint {c ∈ μ.cells | c.2 = j ∧ i ≤ c.1} {c ∈ μ.cells | c.2 = j + 1 ∧ c.1 ≤ i} := by
    rw [Finset.disjoint_left]
    rintro c h₁ h₂
    simp only [Finset.mem_filter] at h₁ h₂
    omega
  rw [← hcard, Finset.filter_or, Finset.card_union_of_disjoint hdisj, card_filter_cells_col,
    card_filter_cells_col_succ h]
  omega

/-!
## The left half of a Garnir set -/

/-- A permutation fixing everything outside `X` maps `X` to itself: were `σ k` outside `X` for
some `k` of `X`, it would be fixed, forcing `σ k = k`. -/
private theorem apply_mem_of_forall_notMem {α : Type*} {X : Finset α} {σ : Equiv.Perm α}
    (hσ : ∀ k ∉ X, σ k = k) {k : α} (hk : k ∈ X) : σ k ∈ X := by
  by_contra h
  have h' : σ k = k := σ.injective (hσ (σ k) h)
  rw [h'] at h
  exact h hk

/-- The **left half of a Garnir set**: the labels of `t` lying in column `j` from row `i`
downwards.  The Garnir set of `t` at `(i, j)` is this set together with the labels in column
`j + 1` from row `i` upwards, and the permutations of the Garnir set that preserve the columns of
`t` are exactly those preserving this half
(`BostConjecture.Specht.mem_columnGroup_iff_image_garnirSetLeft_eq`). -/
def garnirSetLeft (t : Tableau n μ) (i j : ℕ) : Finset (Fin n) :=
  {k | colIndex t k = j ∧ i ≤ rowIndex t k}

@[simp]
theorem mem_garnirSetLeft {t : Tableau n μ} {i j : ℕ} {k : Fin n} :
    k ∈ garnirSetLeft t i j ↔ colIndex t k = j ∧ i ≤ rowIndex t k := by
  simp [garnirSetLeft]

/-- The left half of a Garnir set is part of it, being the first of the two cases of its
definition. -/
theorem garnirSetLeft_subset_garnirSet (t : Tableau n μ) (i j : ℕ) :
    garnirSetLeft t i j ⊆ garnirSet t i j := fun _ hk =>
  mem_garnirSet.mpr (Or.inl (mem_garnirSetLeft.mp hk))

/-- A label of a Garnir set outside its left half lies in column `j + 1`, the two halves being the
two cases of the definition of the Garnir set. -/
theorem colIndex_eq_of_mem_garnirSet_of_notMem_garnirSetLeft {t : Tableau n μ} {i j : ℕ}
    {k : Fin n} (hk : k ∈ garnirSet t i j) (hk' : k ∉ garnirSetLeft t i j) :
    colIndex t k = j + 1 := by
  rcases mem_garnirSet.mp hk with h | h
  · exact absurd (mem_garnirSetLeft.mpr h) hk'
  · exact h.1

/-- **The internal permutations of a Garnir set are those preserving its left half.**  A
permutation supported in the Garnir set of `t` at `(i, j)` preserves the columns of `t` exactly
when it maps the column-`j` half of that set onto itself; it then automatically preserves the
column-`(j + 1)` half as well, so the internal permutations are the product of the two symmetric
groups on the halves. -/
theorem mem_columnGroup_iff_image_garnirSetLeft_eq {t : Tableau n μ} {i j : ℕ}
    {σ : Equiv.Perm (Fin n)} (hσ : ∀ k ∉ garnirSet t i j, σ k = k) :
    σ ∈ columnGroup t ↔ (garnirSetLeft t i j).image σ = garnirSetLeft t i j := by
  constructor
  · intro hcol
    refine Finset.eq_of_subset_of_card_le ?_
      (le_of_eq (Finset.card_image_of_injective _ σ.injective).symm)
    intro k hk
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hk
    have hmem : σ l ∈ garnirSet t i j :=
      apply_mem_of_forall_notMem hσ (garnirSetLeft_subset_garnirSet t i j hl)
    have hcolσ : colIndex t (σ l) = j := (hcol l).trans (mem_garnirSetLeft.mp hl).1
    rcases mem_garnirSet.mp hmem with ⟨-, hrow⟩ | ⟨hc, -⟩
    · exact mem_garnirSetLeft.mpr ⟨hcolσ, hrow⟩
    · exact absurd hc (by omega)
  · intro himg
    change (∀ k, colIndex t (σ k) = colIndex t k)
    intro k
    by_cases hk : k ∈ garnirSet t i j
    · by_cases hkl : k ∈ garnirSetLeft t i j
      · have hmem : σ k ∈ garnirSetLeft t i j := himg ▸ Finset.mem_image_of_mem σ hkl
        rw [(mem_garnirSetLeft.mp hmem).1, (mem_garnirSetLeft.mp hkl).1]
      · have hnot : σ k ∉ garnirSetLeft t i j := by
          intro h
          rw [← himg] at h
          obtain ⟨l, hl, hlk⟩ := Finset.mem_image.mp h
          exact hkl (σ.injective hlk ▸ hl)
        rw [colIndex_eq_of_mem_garnirSet_of_notMem_garnirSetLeft
            (apply_mem_of_forall_notMem hσ hk) hnot,
          colIndex_eq_of_mem_garnirSet_of_notMem_garnirSetLeft hk hkl]
    · rw [hσ k hk]

end BostConjecture.Specht
