/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Specht.Tableau.Prefix

/-!
# Restricting integral polytabloids to a prefix

Freezing the tail row word gives an integral coefficient map to the existing
smaller word representation. Column permutations contributing to this slice
fix the tail pointwise. No branching-filtration assertion is assumed here.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Specht

open OAI.Saxl

variable {n m : ℕ} {μ : YoungDiagram} {t : Tableau n μ}

/-- Identify prefix labels with the initial interval in the original labels. -/
def prefixFinEquiv (hm : m ≤ n) : Fin m ≃ {i : Fin n // i.val < m} where
  toFun i := ⟨Fin.castLE hm i, i.isLt⟩
  invFun i := ⟨i.val.val, i.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Extend a prefix permutation by the identity on all remaining labels. -/
def prefixPerm (hm : m ≤ n) (g : Equiv.Perm (Fin m)) : Equiv.Perm (Fin n) :=
  g.extendDomain (prefixFinEquiv hm)

@[simp] theorem prefixPerm_castLE (hm : m ≤ n) (g : Equiv.Perm (Fin m)) (i : Fin m) :
    prefixPerm hm g (Fin.castLE hm i) = Fin.castLE hm (g i) :=
  g.extendDomain_apply_image (prefixFinEquiv hm) i

@[simp] theorem prefixPerm_of_le (hm : m ≤ n) (g : Equiv.Perm (Fin m))
    (i : Fin n) (hi : m ≤ i.val) : prefixPerm hm g i = i :=
  g.extendDomain_apply_not_subtype (prefixFinEquiv hm) (not_lt.mpr hi)

@[simp] theorem sign_prefixPerm (hm : m ≤ n) (g : Equiv.Perm (Fin m)) :
    Equiv.Perm.sign (prefixPerm hm g) = Equiv.Perm.sign g :=
  Equiv.Perm.sign_extendDomain g (prefixFinEquiv hm)

@[simp] theorem prefixPerm_inv (hm : m ≤ n) (g : Equiv.Perm (Fin m)) :
    prefixPerm hm g⁻¹ = (prefixPerm hm g)⁻¹ := rfl

theorem prefix_invariant_of_fixes_tail (g : Equiv.Perm (Fin n))
    (hfix : ∀ i : Fin n, m ≤ i.val → g i = i) (i : Fin n) :
    (g i).val < m ↔ i.val < m := by
  constructor
  · intro hi
    by_contra h
    rw [hfix i (le_of_not_gt h)] at hi
    exact h hi
  · intro hi
    by_contra h
    have he : g i = i := g.injective (hfix (g i) (le_of_not_gt h))
    exact h (he.symm ▸ hi)

/-- Restrict a permutation fixing the tail to the initial labels. -/
def restrictPrefixPerm (hm : m ≤ n) (g : Equiv.Perm (Fin n))
    (hfix : ∀ i : Fin n, m ≤ i.val → g i = i) : Equiv.Perm (Fin m) :=
  (prefixFinEquiv hm).trans
    ((g.subtypePerm (prefix_invariant_of_fixes_tail g hfix)).trans (prefixFinEquiv hm).symm)

@[simp] theorem castLE_restrictPrefixPerm (hm : m ≤ n) (g : Equiv.Perm (Fin n))
    (hfix : ∀ i : Fin n, m ≤ i.val → g i = i) (i : Fin m) :
    Fin.castLE hm (restrictPrefixPerm hm g hfix i) = g (Fin.castLE hm i) := rfl

@[simp] theorem prefixPerm_restrictPrefixPerm (hm : m ≤ n) (g : Equiv.Perm (Fin n))
    (hfix : ∀ i : Fin n, m ≤ i.val → g i = i) :
    prefixPerm hm (restrictPrefixPerm hm g hfix) = g := by
  apply Equiv.ext
  intro i
  by_cases hi : i.val < m
  · change prefixPerm hm (restrictPrefixPerm hm g hfix) (Fin.castLE hm ⟨i.val, hi⟩) = _
    rw [prefixPerm_castLE, castLE_restrictPrefixPerm]
    rfl
  · rw [prefixPerm_of_le hm _ i (le_of_not_gt hi), hfix i (le_of_not_gt hi)]

/-- A prefix has no more rows than the original diagram. -/
theorem prefixShape_colLen_le (ht : IsStandard t) (hm : m ≤ n) :
    (prefixShape ht m hm).colLen 0 ≤ μ.colLen 0 := by
  by_contra! h
  have hb : (μ.colLen 0, 0) ∈ prefixShape ht m hm :=
    YoungDiagram.mem_iff_lt_colLen.mpr h
  have := YoungDiagram.mem_iff_lt_colLen.mp (prefixShape_le ht m hm hb)
  omega

/-- Extend a prefix word by the original tableau's row word on the tail. -/
def extendPrefixWord (ht : IsStandard t) (hm : m ≤ n)
    (w : Fin m → Fin ((prefixShape ht m hm).colLen 0)) : Fin n → Fin (μ.colLen 0) :=
  fun i => if h : i.val < m then
    Fin.castLE (prefixShape_colLen_le ht hm) (w ⟨i.val, h⟩) else rowWord t i

@[simp] theorem extendPrefixWord_castLE (ht : IsStandard t) (hm : m ≤ n)
    (w : Fin m → Fin ((prefixShape ht m hm).colLen 0)) (i : Fin m) :
    extendPrefixWord ht hm w (Fin.castLE hm i) =
      Fin.castLE (prefixShape_colLen_le ht hm) (w i) := by
  simp [extendPrefixWord, i.isLt]

@[simp] theorem extendPrefixWord_of_le (ht : IsStandard t) (hm : m ≤ n)
    (w : Fin m → Fin ((prefixShape ht m hm).colLen 0)) (i : Fin n) (hi : m ≤ i.val) :
    extendPrefixWord ht hm w i = rowWord t i := by
  simp [extendPrefixWord, not_lt.mpr hi]

/-- Frozen-tail coefficient restriction on the integral word space. -/
def prefixSlice (ht : IsStandard t) (hm : m ≤ n) :
    ((Fin n → Fin (μ.colLen 0)) → ℤ) →ₗ[ℤ]
      ((Fin m → Fin ((prefixShape ht m hm).colLen 0)) → ℤ) where
  toFun x w := x (extendPrefixWord ht hm w)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem extendPrefixWord_comp (ht : IsStandard t) (hm : m ≤ n)
    (w : Fin m → Fin ((prefixShape ht m hm).colLen 0)) (g : Equiv.Perm (Fin m)) :
    extendPrefixWord ht hm (w ∘ g) = extendPrefixWord ht hm w ∘ prefixPerm hm g := by
  funext i
  by_cases hi : i.val < m
  · let j : Fin m := ⟨i.val, hi⟩
    change extendPrefixWord ht hm (w ∘ g) (Fin.castLE hm j) =
      extendPrefixWord ht hm w (prefixPerm hm g (Fin.castLE hm j))
    simp
  · simp [Function.comp_apply, prefixPerm_of_le hm g i (le_of_not_gt hi),
      extendPrefixWord_of_le ht hm _ i (le_of_not_gt hi)]

/-- The coefficient restriction intertwines the actual integral position actions. -/
theorem prefixSlice_wordRepInt (ht : IsStandard t) (hm : m ≤ n)
    (g : Equiv.Perm (Fin m)) (x : (Fin n → Fin (μ.colLen 0)) → ℤ) :
    prefixSlice ht hm (wordRepInt n (μ.colLen 0) (prefixPerm hm g) x) =
      wordRepInt m ((prefixShape ht m hm).colLen 0) g (prefixSlice ht hm x) := by
  ext w
  exact congrArg x (extendPrefixWord_comp ht hm w g).symm

/-- Column permutations of the smaller tableau extend to column permutations of the original. -/
def prefixColumnGroup (ht : IsStandard t) (hm : m ≤ n)
    (g : columnGroup (prefixTableau ht m hm)) : columnGroup t :=
  ⟨prefixPerm hm g.val, by
    intro i
    by_cases hi : i.val < m
    · let j : Fin m := ⟨i.val, hi⟩
      change (t (prefixPerm hm g.val (Fin.castLE hm j))).val.2 = _
      rw [prefixPerm_castLE]
      exact g.property j
    · rw [prefixPerm_of_le hm g.val i (le_of_not_gt hi)]⟩

/-- Restriction of a tail-fixing column permutation to the prefix column group. -/
def restrictPrefixColumnGroup (ht : IsStandard t) (hm : m ≤ n)
    (g : columnGroup t) (hfix : ∀ i : Fin n, m ≤ i.val → g.val i = i) :
    columnGroup (prefixTableau ht m hm) :=
  ⟨restrictPrefixPerm hm g.val hfix, by
    intro i
    change (t (Fin.castLE hm (restrictPrefixPerm hm g.val hfix i))).val.2 = _
    rw [castLE_restrictPrefixPerm]
    exact g.property (Fin.castLE hm i)⟩

/-- The coefficient of a column-permuted row word is exactly its sign. -/
theorem polytabloidInt_rowWord_column (t : Tableau n μ) (g : columnGroup t) :
    polytabloidInt t (rowWord t ∘ g.val) = (Equiv.Perm.sign g.val : ℤ) := by
  have h := congrFun (polytabloidInt_relabel_of_mem_columnGroup t g.property) (rowWord t)
  rw [polytabloidInt_relabel] at h
  simpa [wordRepInt, polytabloidInt_rowWord] using h

theorem extendPrefixWord_rowWord_comp (ht : IsStandard t) (hm : m ≤ n)
    (g : columnGroup (prefixTableau ht m hm)) :
    extendPrefixWord ht hm (rowWord (prefixTableau ht m hm) ∘ g.val) =
      rowWord t ∘ (prefixColumnGroup ht hm g).val := by
  funext i
  by_cases hi : i.val < m
  · change extendPrefixWord ht hm _ (Fin.castLE hm ⟨i.val, hi⟩) = _
    rw [extendPrefixWord_castLE]
    change _ = rowWord t (prefixPerm hm g.val (Fin.castLE hm ⟨i.val, hi⟩))
    rw [prefixPerm_castLE]
    rfl
  · change _ = rowWord t (prefixPerm hm g.val i)
    rw [prefixPerm_of_le hm g.val i (le_of_not_gt hi),
      extendPrefixWord_of_le ht hm _ i (le_of_not_gt hi)]

/-- A column permutation matching the frozen tail fixes every tail label. -/
theorem columnGroup_fixes_tail_of_rowWord (ht : IsStandard t) (hm : m ≤ n)
    (g : columnGroup t) (w : Fin m → Fin ((prefixShape ht m hm).colLen 0))
    (hg : rowWord t ∘ g.val = extendPrefixWord ht hm w)
    (i : Fin n) (hi : m ≤ i.val) : g.val i = i := by
  apply t.injective
  apply Subtype.ext
  apply Prod.ext _ (g.property i)
  have h := congrArg Fin.val (congrFun hg i)
  simpa [Function.comp_apply, extendPrefixWord_of_le ht hm w i hi, rowWord] using h

/-- Freezing the tail sends the original polytabloid to the actual prefix polytabloid. -/
theorem prefixSlice_polytabloidInt (ht : IsStandard t) (hm : m ≤ n) :
    prefixSlice ht hm (polytabloidInt t) = polytabloidInt (prefixTableau ht m hm) := by
  ext w
  change polytabloidInt t (extendPrefixWord ht hm w) = _
  by_cases hw : polytabloidInt (prefixTableau ht m hm) w ≠ 0
  · obtain ⟨g, rfl⟩ := exists_column_of_polytabloidInt_ne_zero (prefixTableau ht m hm) hw
    rw [extendPrefixWord_rowWord_comp, polytabloidInt_rowWord_column,
      polytabloidInt_rowWord_column]
    exact congrArg (fun x : ℤˣ => (x : ℤ)) (sign_prefixPerm hm g.val)
  · have hz : polytabloidInt (prefixTableau ht m hm) w = 0 := not_ne_iff.mp hw
    rw [hz]
    by_contra hx
    obtain ⟨g, hg⟩ := exists_column_of_polytabloidInt_ne_zero t hx
    let hfix := columnGroup_fixes_tail_of_rowWord ht hm g w hg
    let q := restrictPrefixColumnGroup ht hm g hfix
    have hq : rowWord (prefixTableau ht m hm) ∘ q.val = w := by
      funext i
      apply Fin.ext
      have hi := congrArg Fin.val (congrFun hg (Fin.castLE hm i))
      rw [extendPrefixWord_castLE] at hi
      change (t (g.val (Fin.castLE hm i))).val.1 = (w i).val at hi
      change (t (Fin.castLE hm (restrictPrefixPerm hm g.val hfix i))).val.1 = _
      rw [castLE_restrictPrefixPerm]
      exact hi
    have he := polytabloidInt_rowWord_column (prefixTableau ht m hm) q
    rw [hq, hz] at he
    exact (Units.ne_zero (Equiv.Perm.sign q.val)) he.symm

/-- Every vector of the smaller integral orbit lattice has an integral lift. -/
theorem orbitLattice_le_map_prefixSlice (ht : IsStandard t) (hm : m ≤ n) :
    orbitLattice (prefixTableau ht m hm) ≤ (orbitLattice t).map (prefixSlice ht hm) := by
  rw [orbitLattice, Submodule.span_le]
  rintro _ ⟨g, rfl⟩
  exact ⟨wordRepInt n (μ.colLen 0) (prefixPerm hm g) (polytabloidInt t),
    orbit_mem_orbitLattice t _, by rw [prefixSlice_wordRepInt, prefixSlice_polytabloidInt]⟩

/-- The prefix central action has the expected scalar after coefficient restriction.
This is an identity of slices, not an eigenvector assertion in the full Specht module. -/
theorem prefixSlice_central_polytabloidInt (ht : IsStandard t) (hm : m ≤ n) :
    prefixSlice ht hm
      (∑ j : Fin m, ∑ i ∈ Finset.Iio j,
        wordRepInt n (μ.colLen 0) (prefixPerm hm (Equiv.swap i j)) (polytabloidInt t)) =
      diagramContent (prefixShape ht m hm) • polytabloidInt (prefixTableau ht m hm) := by
  simp only [map_sum, prefixSlice_wordRepInt, prefixSlice_polytabloidInt]
  exact sum_wordRepInt_polytabloid_eq_content (prefixTableau_isStandard ht m hm)

/-- Column standardness bounds the row assigned to the largest label in every nonzero term. -/
theorem ColumnStandard.last_row_le_of_polytabloidInt_ne_zero
    {t : Tableau (n + 1) μ} (ht : ColumnStandard t)
    {w : Fin (n + 1) → Fin (μ.colLen 0)} (hw : polytabloidInt t w ≠ 0) :
    w (Fin.last n) ≤ rowWord t (Fin.last n) := by
  obtain ⟨g, rfl⟩ := exists_column_of_polytabloidInt_ne_zero t hw
  change (t (g.val (Fin.last n))).val.1 ≤ (t (Fin.last n)).val.1
  by_contra! h
  have := ht (Fin.last n) (g.val (Fin.last n)) (g.property _).symm h
  exact (not_lt_of_ge (Fin.le_last _)) this

end BostConjecture.Specht
