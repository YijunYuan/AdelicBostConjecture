/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import AdelicBostConjecture.Specht.Branching.Quotient

/-!
# Content action modulo the preceding branching step

The central content identity on the smaller Specht module, transported through
the proved branching map, identifies the last Murphy operator on each quotient.
-/

@[expose] public section

noncomputable section

namespace AdelicBostConjecture.Specht

open OAI.Saxl

variable {n m : ℕ} {μ : YoungDiagram}

/-- Extending a transposition by fixed tail labels gives the same transposition. -/
theorem prefixPerm_swap (hm : m ≤ n) (i j : Fin m) :
    prefixPerm hm (Equiv.swap i j) = Equiv.swap (Fin.castLE hm i) (Fin.castLE hm j) := by
  classical
  apply Equiv.ext
  intro k
  by_cases hk : k.val < m
  · change prefixPerm hm (Equiv.swap i j) (Fin.castLE hm ⟨k.val, hk⟩) = _
    rw [prefixPerm_castLE]
    exact (Fin.castLE_injective hm).map_swap i j ⟨k.val, hk⟩
  · rw [prefixPerm_of_le hm _ k (le_of_not_gt hk)]
    symm
    apply Equiv.swap_apply_of_ne_of_ne
    · intro h
      have := congrArg Fin.val h
      simp only [Fin.val_castLE] at this
      omega
    · intro h
      have := congrArg Fin.val h
      simp only [Fin.val_castLE] at this
      omega

/-- The central prefix sum on the original Specht module. -/
def prefixCentralOperator (t : Tableau n μ) (m : ℕ) (hm : m ≤ n) :
    Module.End ℝ (realSpan t) :=
  ∑ j : Fin m, ∑ i ∈ Finset.Iio j,
    realSpechtRep t (prefixPerm hm (Equiv.swap i j))

/-- Prefix central sums preserve each largest-label filtration step. -/
theorem prefixCentralOperator_mem_lastRowSubspace (t : Tableau (n + 1) μ)
    (r : ℕ) {x : realSpan t} (hx : x ∈ lastRowSubspace t r) :
    prefixCentralOperator t n (Nat.le_succ n) x ∈ lastRowSubspace t r := by
  classical
  simp only [prefixCentralOperator, LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro j _
  apply Submodule.sum_mem
  exact fun i _ => prefixPerm_mem_lastRowSubspace t r (Equiv.swap i j) hx

/-- Through the actual restriction map, the prefix central sum acts by prefix content. -/
theorem prefixSliceReal_prefixCentralOperator {t : Tableau (n + 1) μ}
    [ht : IsStandard t] {x : realSpan t}
    (hx : x ∈ lastRowSubspace t (rowWord t (Fin.last n)).val) :
    prefixSliceReal t (Nat.le_succ n)
        (prefixCentralOperator t n (Nat.le_succ n) x).val =
      (diagramContent (prefixShape t n (Nat.le_succ n)) : ℝ) •
        prefixSliceReal t (Nat.le_succ n) x.val := by
  let y := branchingMap t ⟨x, hx⟩
  have h := congrArg (fun f : Module.End ℝ (realSpan (prefixTableau t n (Nat.le_succ n))) =>
    (f y).val) (sum_murphyOperator_eq (prefixTableau t n (Nat.le_succ n)))
  simp only [murphyOperator, LinearMap.sum_apply, Submodule.coe_sum, LinearMap.smul_apply,
    Module.End.one_apply, Submodule.coe_smul, realSpechtRep_coe] at h
  have hy : y.val = prefixSliceReal t (Nat.le_succ n) x.val := rfl
  rw [hy] at h
  simpa only [prefixCentralOperator, LinearMap.sum_apply, Submodule.coe_sum, map_sum,
    realSpechtRep_coe, prefixSliceReal_wordRepReal] using h

/-- Prefix central action differs from its content scalar only in earlier rows. -/
theorem prefixCentralOperator_sub_content_mem {t : Tableau (n + 1) μ}
    [ht : IsStandard t] {x : realSpan t}
    (hx : x ∈ lastRowSubspace t (rowWord t (Fin.last n)).val) :
    prefixCentralOperator t n (Nat.le_succ n) x -
      (diagramContent (prefixShape t n (Nat.le_succ n)) : ℝ) • x ∈
        lastRowSubspaceLT t (rowWord t (Fin.last n)).val := by
  have hy : prefixCentralOperator t n (Nat.le_succ n) x -
      (diagramContent (prefixShape t n (Nat.le_succ n)) : ℝ) • x ∈
        lastRowSubspace t (rowWord t (Fin.last n)).val :=
    (lastRowSubspace t _).sub_mem (prefixCentralOperator_mem_lastRowSubspace t _ hx)
      ((lastRowSubspace t _).smul_mem _ hx)
  apply (branchingMap_eq_zero_iff (t := t) ⟨_, hy⟩).mp
  apply Subtype.ext
  change prefixSliceReal t (Nat.le_succ n)
    ((prefixCentralOperator t n (Nat.le_succ n) x).val -
      (diagramContent (prefixShape t n (Nat.le_succ n)) : ℝ) • x.val) = 0
  rw [map_sub, map_smul, prefixSliceReal_prefixCentralOperator (t := t) hx, sub_self]

/-- The central prefix sum is the sum of the Murphy operators at prefix labels. -/
theorem prefixCentralOperator_eq_sum (t : Tableau n μ) (m : ℕ) (hm : m ≤ n) :
    prefixCentralOperator t m hm = ∑ j : Fin m, murphyOperator t (Fin.castLE hm j) := by
  classical
  unfold prefixCentralOperator murphyOperator
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_bij (fun i _ => Fin.castLE hm i)
  · intro i hi
    apply Finset.mem_Iio.mpr
    change i < j
    exact Finset.mem_Iio.mp hi
  · intro i hi k hk h
    exact Fin.castLE_injective hm h
  · intro i hi
    have hij : i.val < j.val := (show i < Fin.castLE hm j from Finset.mem_Iio.mp hi)
    exact ⟨⟨i.val, hij.trans j.isLt⟩, Finset.mem_Iio.mpr hij, rfl⟩
  · intro i hi
    rw [prefixPerm_swap]

/-- Splitting off the last Murphy operator from the full central sum. -/
theorem prefixCentralOperator_add_last (t : Tableau (n + 1) μ) :
    prefixCentralOperator t n (Nat.le_succ n) + murphyOperator t (Fin.last n) =
      (diagramContent μ : ℝ) • (1 : Module.End ℝ (realSpan t)) := by
  rw [prefixCentralOperator_eq_sum, ← sum_murphyOperator_eq, Fin.sum_univ_castSucc]
  rfl

/-- The total content differs from the prefix content by the content of the last box. -/
theorem diagramContent_sub_prefixShape {t : Tableau (n + 1) μ} [ht : IsStandard t] :
    diagramContent μ - diagramContent (prefixShape t n (Nat.le_succ n)) =
      tableauContent t (Fin.last n) := by
  rw [← sum_tableauContent t, diagramContent_prefixShape, Fin.sum_univ_castSucc]
  have he : (∑ j : Fin n, tableauContent t (Fin.castLE (Nat.le_succ n) j)) =
      ∑ j : Fin n, tableauContent t j.castSucc := rfl
  rw [he]
  abel

/-- On a branching quotient the last Murphy operator is the content scalar. -/
theorem murphyOperator_last_sub_content_mem {t : Tableau (n + 1) μ}
    [ht : IsStandard t] {x : realSpan t}
    (hx : x ∈ lastRowSubspace t (rowWord t (Fin.last n)).val) :
    murphyOperator t (Fin.last n) x - (tableauContent t (Fin.last n) : ℝ) • x ∈
      lastRowSubspaceLT t (rowWord t (Fin.last n)).val := by
  have h := congrArg (fun f : Module.End ℝ (realSpan t) => f x)
    (prefixCentralOperator_add_last t)
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply] at h
  have hc : (tableauContent t (Fin.last n) : ℝ) =
      (diagramContent μ : ℝ) - (diagramContent (prefixShape t n (Nat.le_succ n)) : ℝ) := by
    exact_mod_cast (diagramContent_sub_prefixShape (t := t)).symm
  have he : murphyOperator t (Fin.last n) x - (tableauContent t (Fin.last n) : ℝ) • x =
      -(prefixCentralOperator t n (Nat.le_succ n) x -
        (diagramContent (prefixShape t n (Nat.le_succ n)) : ℝ) • x) := by
    rw [eq_sub_of_add_eq' h, hc, sub_smul]
    abel
  simpa only [he] using Submodule.neg_mem _ (prefixCentralOperator_sub_content_mem (t := t) hx)

end AdelicBostConjecture.Specht
