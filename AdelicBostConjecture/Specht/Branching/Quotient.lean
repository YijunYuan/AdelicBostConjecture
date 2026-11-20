/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import AdelicBostConjecture.Specht.Branching.Filtration

/-!
# Branching by restriction at a removable corner

The frozen-tail coefficient map on the largest-label filtration takes values in
the smaller Specht space and vanishes on the preceding filtration step. All spaces use
the existing orthonormal word realization.
-/

@[expose] public section

noncomputable section

namespace AdelicBostConjecture.Specht

open OAI.Saxl

variable {n m : ℕ} {μ : YoungDiagram}

/-- In a row-standard tableau, the largest label is at the right end of its row. -/
theorem RowStandard.last_col_eq_of_row_eq {t u : Tableau (n + 1) μ}
    [ht : RowStandard t] [hu : RowStandard u]
    (hr : (t (Fin.last n)).val.1 = (u (Fin.last n)).val.1) :
    t (Fin.last n) = u (Fin.last n) := by
  apply Subtype.ext
  apply Prod.ext hr
  apply le_antisymm
  · by_contra! h
    have hi := hu.label_lt (Fin.last n) (u.symm (t (Fin.last n)))
      (by simpa using hr.symm) (by simpa using h)
    exact (not_lt_of_ge (Fin.le_last _)) hi
  · by_contra! h
    have hi := ht.label_lt (Fin.last n) (t.symm (u (Fin.last n)))
      (by simpa using hr) (by simpa using h)
    exact (not_lt_of_ge (Fin.le_last _)) hi

/-- Two tableaux placing the largest label in the same box differ by a prefix permutation. -/
theorem exists_prefixPerm_relabel {t u : Tableau (n + 1) μ}
    (h : t (Fin.last n) = u (Fin.last n)) :
    ∃ g : Equiv.Perm (Fin n), relabel (prefixPerm (Nat.le_succ n) g) t = u := by
  let p := t.trans u.symm
  have hfix : ∀ i : Fin (n + 1), n ≤ i.val → p i = i := by
    intro i hi
    have he : i = Fin.last n := Fin.ext (by simp only [Fin.val_last]; omega)
    subst i
    change u.symm (t (Fin.last n)) = Fin.last n
    rw [h, u.symm_apply_apply]
  refine ⟨restrictPrefixPerm (Nat.le_succ n) p hfix, ?_⟩
  rw [prefixPerm_restrictPrefixPerm]
  apply Equiv.ext
  intro i
  simp [relabel, p]

/-- Frozen-tail restriction between real Hilbert word spaces. -/
def prefixSliceReal (t : Tableau n μ) [ht : IsStandard t] (hm : m ≤ n) :
    EuclideanSpace ℝ (Fin n → Fin (μ.colLen 0)) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin m → Fin ((prefixShape t m hm).colLen 0)) where
  toFun x := WithLp.toLp 2 (fun w => x (extendPrefixWord t hm w))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem prefixSliceReal_realCast {t : Tableau n μ} [ht : IsStandard t]
    (hm : m ≤ n) (x : (Fin n → Fin (μ.colLen 0)) → ℤ) :
    prefixSliceReal t hm (realCast n (μ.colLen 0) x) =
      realCast m ((prefixShape t m hm).colLen 0) (prefixSlice t hm x) := rfl

@[simp] theorem prefixSliceReal_polytabloid {t : Tableau n μ} [ht : IsStandard t]
    (hm : m ≤ n) :
    prefixSliceReal t hm (realCast n (μ.colLen 0) (polytabloidInt t)) =
      realCast m ((prefixShape t m hm).colLen 0)
        (polytabloidInt (prefixTableau t m hm)) := by
  rw [prefixSliceReal_realCast, prefixSlice_polytabloidInt]

/-- Restriction commutes with the real prefix position action. -/
theorem prefixSliceReal_wordRepReal {t : Tableau n μ} [ht : IsStandard t]
    (hm : m ≤ n) (g : Equiv.Perm (Fin m))
    (x : EuclideanSpace ℝ (Fin n → Fin (μ.colLen 0))) :
    prefixSliceReal t hm (wordRepReal n (μ.colLen 0) (prefixPerm hm g) x) =
      wordRepReal m ((prefixShape t m hm).colLen 0) g (prefixSliceReal t hm x) := by
  ext w
  exact congrArg x (extendPrefixWord_comp (t := t) hm w g).symm

/-- The row word of the original tableau is the extension of its prefix row word. -/
@[simp] theorem extendPrefixWord_rowWord {t : Tableau n μ} [ht : IsStandard t]
    (hm : m ≤ n) :
    extendPrefixWord t hm (rowWord (prefixTableau t m hm)) = rowWord t := by
  funext i
  by_cases hi : i.val < m
  · change extendPrefixWord t hm _ (Fin.castLE hm ⟨i.val, hi⟩) = _
    rw [extendPrefixWord_castLE]
    rfl
  · exact extendPrefixWord_of_le (t := t) hm _ i (le_of_not_gt hi)

/-- Leading row words in the chosen corner stratum occur among the slice coordinates. -/
theorem exists_extendPrefixWord_eq_rowWord {t u : Tableau (n + 1) μ}
    [ht : IsStandard t] [hu : RowStandard u]
    (hr : (rowWord u (Fin.last n)).val = (rowWord t (Fin.last n)).val) :
    ∃ w, extendPrefixWord t (Nat.le_succ n) w = rowWord u := by
  obtain ⟨g, rfl⟩ := exists_prefixPerm_relabel
    (RowStandard.last_col_eq_of_row_eq (t := t) (u := u) hr.symm)
  refine ⟨rowWord (prefixTableau t n (Nat.le_succ n)) ∘ (g⁻¹ : Equiv.Perm (Fin n)), ?_⟩
  rw [extendPrefixWord_comp, extendPrefixWord_rowWord, rowWord_relabel, prefixPerm_inv]

/-- A standard generator in a strictly earlier row is killed by the corner slice. -/
theorem prefixSliceReal_standardRealBasis_eq_zero {t : Tableau (n + 1) μ}
    [ht : IsStandard t] (T : {u : Tableau (n + 1) μ // IsStandard u})
    (hT : (rowWord T.val (Fin.last n)).val < (rowWord t (Fin.last n)).val) :
    prefixSliceReal t (Nat.le_succ n) (standardRealBasis t T) = 0 := by
  ext w
  change (standardRealBasis t T).val (extendPrefixWord t (Nat.le_succ n) w) = 0
  rw [standardRealBasis_coe]
  change (polytabloidInt T.val (extendPrefixWord t (Nat.le_succ n) w) : ℝ) = 0
  suffices hz : polytabloidInt T.val (extendPrefixWord t (Nat.le_succ n) w) = 0 by
    rw [hz, Int.cast_zero]
  by_contra hz
  have hle := ColumnStandard.last_row_le_of_polytabloidInt_ne_zero (t := T.val) hz
  rw [extendPrefixWord_of_le (t := t) (Nat.le_succ n) _ _ le_rfl] at hle
  exact (not_le_of_gt hT) hle

/-- A standard generator in the corner row maps into the smaller Specht space. -/
theorem prefixSliceReal_standardRealBasis_mem {t : Tableau (n + 1) μ}
    [ht : IsStandard t] (T : {u : Tableau (n + 1) μ // IsStandard u})
    (hT : (rowWord T.val (Fin.last n)).val = (rowWord t (Fin.last n)).val) :
    prefixSliceReal t (Nat.le_succ n) (standardRealBasis t T) ∈
      realSpan (prefixTableau t n (Nat.le_succ n)) := by
  obtain ⟨g, hg⟩ := exists_prefixPerm_relabel
    (RowStandard.last_col_eq_of_row_eq (t := t) (u := T.val) hT.symm)
  rw [standardRealBasis_coe, ← hg, polytabloidInt_relabel, ← wordRepReal_realCast,
    prefixSliceReal_wordRepReal, prefixSliceReal_polytabloid]
  apply wordRepReal_mem_realSpan
  exact Submodule.subset_span ⟨_, polytabloidInt_mem_orbitLattice _, rfl⟩

/-- Restriction of the entire filtration step lands in the smaller Specht space. -/
theorem prefixSliceReal_mem_realSpan {t : Tableau (n + 1) μ} [ht : IsStandard t]
    {x : realSpan t} (hx : x ∈ lastRowSubspace t (rowWord t (Fin.last n)).val) :
    prefixSliceReal t (Nat.le_succ n) x.val ∈
      realSpan (prefixTableau t n (Nat.le_succ n)) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨T, hT, rfl⟩ := hx
    rcases hT.eq_or_lt with hT | hT
    · exact prefixSliceReal_standardRealBasis_mem (t := t) T hT
    · rw [prefixSliceReal_standardRealBasis_eq_zero (t := t) T hT]
      exact Submodule.zero_mem _
  | zero => simp
  | add x y hx hy ihx ihy =>
    simpa only [Submodule.coe_add, map_add] using Submodule.add_mem _ ihx ihy
  | smul a x hx ih =>
    simpa only [Submodule.coe_smul, map_smul] using Submodule.smul_mem _ a ih

/-- The actual branching restriction map, with its image condition proved. -/
def branchingMap (t : Tableau (n + 1) μ) [ht : IsStandard t] :
    lastRowSubspace t (rowWord t (Fin.last n)).val →ₗ[ℝ]
      realSpan (prefixTableau t n (Nat.le_succ n)) where
  toFun x := ⟨prefixSliceReal t (Nat.le_succ n) x.val.val,
    prefixSliceReal_mem_realSpan (t := t) x.property⟩
  map_add' _ _ := by ext w; rfl
  map_smul' _ _ := by ext w; rfl

/-- The strict preceding step, including the zero step when the row is zero. -/
def lastRowSubspaceLT (t : Tableau (n + 1) μ) (r : ℕ) : Submodule ℝ (realSpan t) :=
  Submodule.span ℝ {x | ∃ T : {u : Tableau (n + 1) μ // IsStandard u},
    (rowWord T.val (Fin.last n)).val < r ∧ standardRealBasis t T = x}

/-- Restriction annihilates the preceding filtration step. -/
theorem prefixSliceReal_eq_zero_of_mem_lastRowSubspaceLT {t : Tableau (n + 1) μ}
    [ht : IsStandard t] {x : realSpan t}
    (hx : x ∈ lastRowSubspaceLT t (rowWord t (Fin.last n)).val) :
    prefixSliceReal t (Nat.le_succ n) x.val = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨T, hT, rfl⟩ := hx
    exact prefixSliceReal_standardRealBasis_eq_zero (t := t) T hT
  | zero => simp
  | add x y hx hy ihx ihy => simp only [Submodule.coe_add, map_add, ihx, ihy, add_zero]
  | smul a x hx ih => simp only [Submodule.coe_smul, map_smul, ih, smul_zero]

/-- The kernel is exactly the preceding standard-basis filtration step. -/
theorem branchingMap_eq_zero_iff {t : Tableau (n + 1) μ} [ht : IsStandard t]
    (x : lastRowSubspace t (rowWord t (Fin.last n)).val) :
    branchingMap t x = 0 ↔ x.val ∈ lastRowSubspaceLT t (rowWord t (Fin.last n)).val := by
  constructor
  · intro hx
    have hlead (U : {u : Tableau (n + 1) μ // IsStandard u})
        (hU : (rowWord t (Fin.last n)).val ≤ (rowWord U.val (Fin.last n)).val) :
        x.val.val (rowWord U.val) = 0 := by
      rcases hU.eq_or_lt with hU | hU
      · obtain ⟨w, hw⟩ := exists_extendPrefixWord_eq_rowWord (t := t) (u := U.val) hU.symm
        have he := congrArg (fun y => y.val w) hx
        change x.val.val (extendPrefixWord t (Nat.le_succ n) w) = 0 at he
        rwa [hw] at he
      · exact (mem_lastRowSubspace_iff t _ x.val).mp x.property _ hU
    rw [← (standardRealBasis t).sum_repr x.val]
    apply Submodule.sum_mem
    intro T _
    by_cases hT : (rowWord T.val (Fin.last n)).val < (rowWord t (Fin.last n)).val
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨T, hT, rfl⟩)
    · rw [standardRealBasis_repr_eq_zero_of_leading_zero t x.val _ hlead T (le_of_not_gt hT),
        zero_smul]
      exact Submodule.zero_mem _
  · intro hx
    apply Subtype.ext
    exact prefixSliceReal_eq_zero_of_mem_lastRowSubspaceLT (t := t) hx

end AdelicBostConjecture.Specht
