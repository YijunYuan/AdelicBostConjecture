/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Specht.Branching.Quotient

/-!
# Extending a standard tableau at a fixed corner

Deletion and extension use the existing enumerating tableaux. Extension fixes
the last box and intertwines the actual branching map on polytabloids.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Specht

open OAI.Saxl

variable {n : ℕ} {μ : YoungDiagram} {t : Tableau (n + 1) μ}

/-- Replace the prefix filling and keep the original last box. -/
def extendTableau (ht : IsStandard t)
    (u : Tableau n (prefixShape ht n (Nat.le_succ n))) : Tableau (n + 1) μ :=
  relabel (prefixPerm (Nat.le_succ n)
    ((prefixTableau ht n (Nat.le_succ n)).trans u.symm)) t

@[simp] theorem extendTableau_castSucc (ht : IsStandard t)
    (u : Tableau n (prefixShape ht n (Nat.le_succ n))) (i : Fin n) :
    (extendTableau ht u i.castSucc).val = (u i).val := by
  change (t (prefixPerm (Nat.le_succ n)
    ((prefixTableau ht n (Nat.le_succ n)).trans u.symm)⁻¹
      (Fin.castLE (Nat.le_succ n) i))).val = _
  rw [prefixPerm_castLE]
  change (prefixTableau ht n (Nat.le_succ n)
    ((prefixTableau ht n (Nat.le_succ n)).symm (u i))).val = _
  rw [Equiv.apply_symm_apply]

@[simp] theorem extendTableau_last (ht : IsStandard t)
    (u : Tableau n (prefixShape ht n (Nat.le_succ n))) :
    extendTableau ht u (Fin.last n) = t (Fin.last n) := by
  apply t.injective.eq_iff.mpr
  change (prefixPerm (Nat.le_succ n)
    ((prefixTableau ht n (Nat.le_succ n)).trans u.symm)).symm (Fin.last n) = _
  apply (Equiv.symm_apply_eq _).mpr
  exact (prefixPerm_of_le _ _ _ le_rfl).symm

/-- Adding the largest label at the removed corner preserves standardness. -/
theorem extendTableau_isStandard (ht : IsStandard t)
    {u : Tableau n (prefixShape ht n (Nat.le_succ n))} (hu : IsStandard u) :
    IsStandard (extendTableau ht u) := by
  constructor
  · intro i j hr hc
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => exact (lt_irrefl _ hc).elim
      | cast j =>
        have h := ht.1 (Fin.last n) (t.symm (extendTableau ht u j.castSucc))
          (by simpa only [Equiv.apply_symm_apply, extendTableau_last] using hr)
          (by simpa only [Equiv.apply_symm_apply, extendTableau_last] using hc)
        exact (not_lt_of_ge (Fin.le_last _) h).elim
    | cast i =>
      induction j using Fin.lastCases with
      | last => exact Fin.castSucc_lt_last i
      | cast j =>
        exact hu.1 i j (by simpa only [extendTableau_castSucc] using hr)
          (by simpa only [extendTableau_castSucc] using hc)
  · intro i j hc hr
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => exact (lt_irrefl _ hr).elim
      | cast j =>
        have h := ht.2 (Fin.last n) (t.symm (extendTableau ht u j.castSucc))
          (by simpa only [Equiv.apply_symm_apply, extendTableau_last] using hc)
          (by simpa only [Equiv.apply_symm_apply, extendTableau_last] using hr)
        exact (not_lt_of_ge (Fin.le_last _) h).elim
    | cast i =>
      induction j using Fin.lastCases with
      | last => exact Fin.castSucc_lt_last i
      | cast j =>
        exact hu.2 i j (by simpa only [extendTableau_castSucc] using hc)
          (by simpa only [extendTableau_castSucc] using hr)

/-- Extension induces the standard-basis lift in the chosen corner stratum. -/
def extendStandardTableau (ht : IsStandard t)
    (U : {u : Tableau n (prefixShape ht n (Nat.le_succ n)) // IsStandard u}) :
    {u : Tableau (n + 1) μ // IsStandard u} :=
  ⟨extendTableau ht U.val, extendTableau_isStandard ht U.property⟩

/-- Frozen-tail restriction of an extended polytabloid is the original polytabloid. -/
theorem prefixSliceReal_extendTableau (ht : IsStandard t)
    (u : Tableau n (prefixShape ht n (Nat.le_succ n))) :
    prefixSliceReal ht (Nat.le_succ n)
      (realCast (n + 1) (μ.colLen 0) (polytabloidInt (extendTableau ht u))) =
      realCast n ((prefixShape ht n (Nat.le_succ n)).colLen 0) (polytabloidInt u) := by
  unfold extendTableau
  rw [polytabloidInt_relabel, ← wordRepReal_realCast,
    prefixSliceReal_wordRepReal, prefixSliceReal_polytabloid,
    wordRepReal_realCast, ← polytabloidInt_relabel]
  congr 2
  apply Equiv.ext
  intro i
  simp [relabel]

end BostConjecture.Specht
