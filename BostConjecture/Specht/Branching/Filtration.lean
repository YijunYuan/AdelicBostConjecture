/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Specht.Branching.Basic

/-!
# The largest-label support filtration

The standard-basis filtration by the row of the largest label equals the
ambient word-support filtration. Consequently it is invariant under all
permutations of the other labels. No branching quotient is assumed.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Specht

open OAI.Saxl

variable {n : ℕ} {μ : YoungDiagram}

/-- Vanishing at leading words above a row cutoff forces the corresponding basis coefficients
to vanish. -/
theorem standardRealBasis_repr_eq_zero_of_leading_zero (t : Tableau (n + 1) μ)
    (x : realSpan t) (r : ℕ)
    (hx : ∀ U : {u : Tableau (n + 1) μ // IsStandard u},
      r ≤ (rowWord U.val (Fin.last n)).val → x.val (rowWord U.val) = 0)
    (T : {u : Tableau (n + 1) μ // IsStandard u})
    (hT : r ≤ (rowWord T.val (Fin.last n)).val) :
    (standardRealBasis t).repr x T = 0 := by
  classical
  let c := (standardRealBasis t).repr x
  by_contra hcT
  let s := Finset.univ.filter fun U : {u : Tableau (n + 1) μ // IsStandard u} =>
    r ≤ (rowWord U.val (Fin.last n)).val ∧ c U ≠ 0
  have hs : s.Nonempty := ⟨T, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT, hcT⟩⟩
  obtain ⟨U, hU, hmin⟩ := Finset.exists_min_image s (fun U => toLex (rowWord U.val)) hs
  have hU' := (Finset.mem_filter.mp hU).2
  have hzero (V : {u : Tableau (n + 1) μ // IsStandard u}) (hVU : V ≠ U) :
      c V * (polytabloidInt V.val (rowWord U.val) : ℝ) = 0 := by
    by_cases hcV : c V = 0
    · simp [hcV]
    have hpol : polytabloidInt V.val (rowWord U.val) = 0 := by
      by_contra hpol
      have hrow := ColumnStandard.last_row_le_of_polytabloidInt_ne_zero (t := V.val) hpol
      have hrV : r ≤ (rowWord V.val (Fin.last n)).val := hU'.1.trans hrow
      have hle := ColumnStandard.rowWord_le_of_polytabloid_ne_zero (t := V.val) hpol
      have hrev := hmin V (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrV, hcV⟩)
      have hw : rowWord V.val = rowWord U.val := congrArg ofLex (le_antisymm hle hrev)
      exact hVU (Subtype.ext (RowStandard.eq_of_rowWord_eq (t := V.val) (u := U.val) hw))
    simp [hpol]
  have he := congrArg (fun y : realSpan t => y.val (rowWord U.val))
    ((standardRealBasis t).sum_repr x)
  simp only [Submodule.coe_sum, WithLp.ofLp_sum, Finset.sum_apply, Submodule.coe_smul,
    WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, standardRealBasis_coe] at he
  change (∑ V, c V * (polytabloidInt V.val (rowWord U.val) : ℝ)) = x.val (rowWord U.val) at he
  rw [Finset.sum_eq_single U (fun V _ hVU => hzero V hVU) (by simp),
    polytabloidInt_rowWord, Int.cast_one, mul_one, hx _ hU'.1] at he
  exact hU'.2 he

/-- A standard coefficient outside a last-letter support cutoff must vanish. -/
theorem standardRealBasis_repr_eq_zero_of_last_support (t : Tableau (n + 1) μ)
    (x : realSpan t) (r : ℕ)
    (hx : ∀ w : Fin (n + 1) → Fin (μ.colLen 0), r < (w (Fin.last n)).val → x.val w = 0)
    (T : {u : Tableau (n + 1) μ // IsStandard u})
    (hT : r < (rowWord T.val (Fin.last n)).val) :
    (standardRealBasis t).repr x T = 0 :=
  standardRealBasis_repr_eq_zero_of_leading_zero t x (r + 1)
    (fun U hU => hx (rowWord U.val) hU) T hT

/-- The standard subspace cut out by the row of the largest label. -/
def lastRowSubspace (t : Tableau (n + 1) μ) (r : ℕ) : Submodule ℝ (realSpan t) :=
  Submodule.span ℝ {x | ∃ T : {u : Tableau (n + 1) μ // IsStandard u},
    (rowWord T.val (Fin.last n)).val ≤ r ∧ standardRealBasis t T = x}

/-- The standard-basis filtration is exactly the ambient word-support filtration. -/
theorem mem_lastRowSubspace_iff (t : Tableau (n + 1) μ) (r : ℕ) (x : realSpan t) :
    x ∈ lastRowSubspace t r ↔
      ∀ w : Fin (n + 1) → Fin (μ.colLen 0), r < (w (Fin.last n)).val → x.val w = 0 := by
  classical
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨T, hT, rfl⟩ := hy
      intro w hw
      have hz : polytabloidInt T.val w = 0 := by
        by_contra hz
        have hle : (w (Fin.last n)).val ≤ (rowWord T.val (Fin.last n)).val :=
          ColumnStandard.last_row_le_of_polytabloidInt_ne_zero (t := T.val) hz
        exact (not_le_of_gt hw) (hle.trans hT)
      simp [standardRealBasis_coe, realCast, hz]
    | zero => intro w _; rfl
    | add y z hy hz ihy ihz =>
      intro w hw
      change y.val w + z.val w = 0
      rw [ihy w hw, ihz w hw, zero_add]
    | smul a y hy ih =>
      intro w hw
      change a * y.val w = 0
      rw [ih w hw, mul_zero]
  · intro hx
    rw [← (standardRealBasis t).sum_repr x]
    apply Submodule.sum_mem
    intro T _
    by_cases hT : (rowWord T.val (Fin.last n)).val ≤ r
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨T, hT, rfl⟩)
    · rw [standardRealBasis_repr_eq_zero_of_last_support t x r hx T (lt_of_not_ge hT), zero_smul]
      exact Submodule.zero_mem _

/-- Permutations fixing the largest label preserve the actual standard-basis filtration. -/
theorem realSpechtRep_mem_lastRowSubspace (t : Tableau (n + 1) μ) (r : ℕ)
    (g : Equiv.Perm (Fin (n + 1))) (hg : g (Fin.last n) = Fin.last n)
    {x : realSpan t} (hx : x ∈ lastRowSubspace t r) :
    realSpechtRep t g x ∈ lastRowSubspace t r := by
  rw [mem_lastRowSubspace_iff] at hx ⊢
  intro w hw
  change x.val (w ∘ g) = 0
  apply hx
  simpa only [Function.comp_apply, hg] using hw

/-- In particular, all permutations of the prefix preserve the filtration. -/
theorem prefixPerm_mem_lastRowSubspace (t : Tableau (n + 1) μ) (r : ℕ)
    (g : Equiv.Perm (Fin n)) {x : realSpan t} (hx : x ∈ lastRowSubspace t r) :
    realSpechtRep t (prefixPerm (Nat.le_succ n) g) x ∈ lastRowSubspace t r :=
  realSpechtRep_mem_lastRowSubspace t r _ (prefixPerm_of_le _ _ _ le_rfl) hx

end BostConjecture.Specht
