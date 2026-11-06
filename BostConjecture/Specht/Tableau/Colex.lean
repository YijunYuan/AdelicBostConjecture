/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Specht.Tableau.Extension

/-!
# Colexicographic order for standard tableaux

The largest label with a different row determines the comparison. This is
the order compatible with the largest-label branching filtration.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Specht

open OAI.Saxl

variable {n : ℕ} {μ : YoungDiagram}

/-- Compare rows at the largest label where they differ. -/
def TableauColexLT (u t : Tableau n μ) : Prop :=
  ∃ j, (u j).val.1 < (t j).val.1 ∧ ∀ k, j < k → (u k).val.1 = (t k).val.1

/-- Colexicographic comparison is lexicographic comparison after reversal. -/
theorem tableauColexLT_iff (u t : Tableau n μ) :
    TableauColexLT u t ↔
      toLex (rowWord u ∘ Fin.rev) < toLex (rowWord t ∘ Fin.rev) := by
  change TableauColexLT u t ↔ ∃ j : Fin n,
    (∀ k : Fin n, k < j → rowWord u k.rev = rowWord t k.rev) ∧
    rowWord u j.rev < rowWord t j.rev
  constructor
  · rintro ⟨j, hj, htail⟩
    refine ⟨j.rev, ?_, ?_⟩
    · intro k hk
      apply Fin.ext
      exact htail k.rev ((Fin.rev_lt_rev (i := k.rev) (j := j)).mp
        (by simpa only [Fin.rev_rev] using hk))
    · simpa only [Fin.rev_rev, Fin.lt_def, rowWord] using hj
  · rintro ⟨j, htail, hj⟩
    refine ⟨j.rev, ?_, ?_⟩
    · simpa only [Fin.lt_def, rowWord] using hj
    · intro k hk
      have h := congrArg Fin.val (htail k.rev (by simpa only [Fin.rev_rev] using
        (Fin.rev_lt_rev.mpr hk)))
      simpa only [Fin.rev_rev, rowWord] using h

namespace StandardColex

/-- The canonical total order used for monic orthogonalization. -/
scoped instance : LinearOrder {t : Tableau n μ // IsStandard t} :=
  LinearOrder.lift' (fun T => toLex (rowWord T.val ∘ Fin.rev)) (by
    intro T U h
    apply Subtype.ext
    apply T.property.1.eq_of_rowWord_eq U.property.1
    funext i
    have he := congrFun (congrArg ofLex h) i.rev
    simpa using he)

end StandardColex

open scoped StandardColex

theorem standardColex_lt_iff (U T : {t : Tableau n μ // IsStandard t}) :
    U < T ↔ TableauColexLT U.val T.val := (tableauColexLT_iff _ _).symm

/-- A strictly earlier final row precedes every filling of a later final row. -/
theorem tableauColexLT_of_last_row_lt {u t : Tableau (n + 1) μ}
    (h : (u (Fin.last n)).val.1 < (t (Fin.last n)).val.1) : TableauColexLT u t :=
  ⟨Fin.last n, h, fun k hk => (not_lt_of_ge (Fin.le_last k) hk).elim⟩

/-- Deleting a common last box preserves and reflects colex comparison. -/
theorem tableauColexLT_extendTableau_iff {t : Tableau (n + 1) μ} (ht : IsStandard t)
    (u v : Tableau n (prefixShape ht n (Nat.le_succ n))) :
    TableauColexLT (extendTableau ht u) (extendTableau ht v) ↔ TableauColexLT u v := by
  constructor
  · rintro ⟨j, hj, htail⟩
    induction j using Fin.lastCases with
    | last => exact (lt_irrefl _ (by simpa only [extendTableau_last] using hj)).elim
    | cast j =>
      refine ⟨j, ?_, ?_⟩
      · simpa only [extendTableau_castSucc] using hj
      · intro k hk
        simpa only [extendTableau_castSucc] using htail k.castSucc hk
  · rintro ⟨j, hj, htail⟩
    refine ⟨j.castSucc, ?_, ?_⟩
    · simpa only [extendTableau_castSucc] using hj
    · intro k hk
      induction k using Fin.lastCases with
      | last => simp only [extendTableau_last]
      | cast k => simpa only [extendTableau_castSucc] using htail k hk

@[simp] theorem extendTableau_prefixTableau {t : Tableau (n + 1) μ} (ht : IsStandard t) :
    extendTableau ht (prefixTableau ht n (Nat.le_succ n)) = t := by
  apply Equiv.ext
  intro i
  induction i using Fin.lastCases with
  | last => exact extendTableau_last ht _
  | cast i => exact Subtype.ext (extendTableau_castSucc ht _ i)

/-- Lifting a smaller earlier tableau gives an earlier tableau in the same corner stratum. -/
theorem tableauColexLT_extendTableau {t : Tableau (n + 1) μ} (ht : IsStandard t)
    {u : Tableau n (prefixShape ht n (Nat.le_succ n))}
    (hu : TableauColexLT u (prefixTableau ht n (Nat.le_succ n))) :
    TableauColexLT (extendTableau ht u) t := by
  simpa only [extendTableau_prefixTableau] using
    (tableauColexLT_extendTableau_iff ht _ _).mpr hu

/-- The span of standard polytabloids strictly earlier than the specified tableau. -/
def colexSubspace (t u : Tableau n μ) : Submodule ℝ (realSpan t) :=
  Submodule.span ℝ {x | ∃ U : {v : Tableau n μ // IsStandard v},
    TableauColexLT U.val u ∧ standardRealBasis t U = x}

theorem lastRowSubspaceLT_le_colexSubspace (t : Tableau (n + 1) μ) :
    lastRowSubspaceLT t (rowWord t (Fin.last n)).val ≤ colexSubspace t t := by
  apply Submodule.span_le.mpr
  rintro _ ⟨U, hU, rfl⟩
  exact Submodule.subset_span ⟨U, tableauColexLT_of_last_row_lt hU, rfl⟩

/-- The linear lift obtained by extending each standard tableau at the fixed corner. -/
def cornerLift {t : Tableau (n + 1) μ} (ht : IsStandard t) :
    realSpan (prefixTableau ht n (Nat.le_succ n)) →ₗ[ℝ] realSpan t :=
  (standardRealBasis (prefixTableau ht n (Nat.le_succ n))).constr ℝ
    (fun U => standardRealBasis t (extendStandardTableau ht U))

@[simp] theorem cornerLift_standardRealBasis {t : Tableau (n + 1) μ} (ht : IsStandard t)
    (U : {u : Tableau n (prefixShape ht n (Nat.le_succ n)) // IsStandard u}) :
    cornerLift ht (standardRealBasis (prefixTableau ht n (Nat.le_succ n)) U) =
      standardRealBasis t (extendStandardTableau ht U) :=
  Module.Basis.constr_basis _ _ _ _

/-- All lifted vectors lie in the correct largest-label filtration step. -/
theorem cornerLift_mem_lastRowSubspace {t : Tableau (n + 1) μ} (ht : IsStandard t)
    (x : realSpan (prefixTableau ht n (Nat.le_succ n))) :
    cornerLift ht x ∈ lastRowSubspace t (rowWord t (Fin.last n)).val := by
  rw [← (standardRealBasis (prefixTableau ht n (Nat.le_succ n))).sum_repr x, map_sum]
  apply Submodule.sum_mem
  intro U _
  rw [map_smul, cornerLift_standardRealBasis]
  apply Submodule.smul_mem
  apply Submodule.subset_span
  refine ⟨extendStandardTableau ht U, ?_, rfl⟩
  change (extendTableau ht U.val (Fin.last n)).val.1 ≤ (t (Fin.last n)).val.1
  rw [extendTableau_last]

/-- The concrete coefficient restriction is a left inverse of the standard lift. -/
theorem prefixSliceReal_cornerLift {t : Tableau (n + 1) μ} (ht : IsStandard t)
    (x : realSpan (prefixTableau ht n (Nat.le_succ n))) :
    prefixSliceReal ht (Nat.le_succ n) (cornerLift ht x).val = x.val := by
  have h : (prefixSliceReal ht (Nat.le_succ n)).comp
      ((realSpan t).subtype.comp (cornerLift ht)) =
        (realSpan (prefixTableau ht n (Nat.le_succ n))).subtype := by
    apply (standardRealBasis (prefixTableau ht n (Nat.le_succ n))).ext
    intro U
    simp only [LinearMap.comp_apply, Submodule.subtype_apply,
      cornerLift_standardRealBasis, standardRealBasis_coe]
    exact prefixSliceReal_extendTableau ht U.val
  exact LinearMap.congr_fun h x

/-- Earlier prefix polytabloids lift to earlier polytabloids in the original space. -/
theorem cornerLift_mem_colexSubspace {t : Tableau (n + 1) μ} (ht : IsStandard t)
    {x : realSpan (prefixTableau ht n (Nat.le_succ n))}
    (hx : x ∈ colexSubspace (prefixTableau ht n (Nat.le_succ n))
      (prefixTableau ht n (Nat.le_succ n))) : cornerLift ht x ∈ colexSubspace t t := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨U, hU, rfl⟩ := hy
    rw [cornerLift_standardRealBasis]
    exact Submodule.subset_span
      ⟨extendStandardTableau ht U, tableauColexLT_extendTableau ht hU, rfl⟩
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul a x hx ih => simpa only [map_smul] using Submodule.smul_mem _ a ih

end BostConjecture.Specht
