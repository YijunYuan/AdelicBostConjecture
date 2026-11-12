/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Specht.Tableau.Colex
public import BostConjecture.Specht.Branching.LastMurphy

/-!
# Triangular Murphy action

Induction through the concrete branching quotient identifies every diagonal
coefficient with its box content in colexicographic order.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Specht

open OAI.Saxl

variable {n : ℕ} {μ : YoungDiagram}

/-- Prefix Murphy operators are sums of extended prefix transpositions. -/
theorem murphyOperator_castSucc (t : Tableau (n + 1) μ) (j : Fin n) :
    murphyOperator t j.castSucc = ∑ i ∈ Finset.Iio j,
      realSpechtRep t (prefixPerm (Nat.le_succ n) (Equiv.swap i j)) := by
  classical
  symm
  unfold murphyOperator
  apply Finset.sum_bij (fun i _ => i.castSucc)
  · intro i hi
    apply Finset.mem_Iio.mpr
    change i < j
    exact Finset.mem_Iio.mp hi
  · intro i hi k hk h
    exact Fin.castSucc_injective _ h
  · intro i hi
    have hij : i.val < j.val := (show i < j.castSucc from Finset.mem_Iio.mp hi)
    exact ⟨⟨i.val, hij.trans j.isLt⟩, Finset.mem_Iio.mpr hij, rfl⟩
  · intro i hi
    rw [prefixPerm_swap]
    rfl

theorem murphyOperator_castSucc_mem_lastRowSubspace (t : Tableau (n + 1) μ)
    (j : Fin n) (r : ℕ) {x : realSpan t} (hx : x ∈ lastRowSubspace t r) :
    murphyOperator t j.castSucc x ∈ lastRowSubspace t r := by
  classical
  rw [murphyOperator_castSucc]
  simp only [LinearMap.sum_apply]
  apply Submodule.sum_mem
  exact fun i _ => prefixPerm_mem_lastRowSubspace t r (Equiv.swap i j) hx

/-- The restriction map intertwines each prefix Murphy operator. -/
theorem prefixSliceReal_murphyOperator {t : Tableau (n + 1) μ} [ht : IsStandard t]
    (j : Fin n) {x : realSpan t}
    (hx : x ∈ lastRowSubspace t (rowWord t (Fin.last n)).val) :
    prefixSliceReal t (Nat.le_succ n) (murphyOperator t j.castSucc x).val =
      (murphyOperator (prefixTableau t n (Nat.le_succ n)) j
        (branchingMap t ⟨x, hx⟩)).val := by
  classical
  rw [murphyOperator_castSucc]
  simp only [murphyOperator, LinearMap.sum_apply,
    Submodule.coe_sum, map_sum, realSpechtRep_coe, prefixSliceReal_wordRepReal]
  rfl

/-- Every Murphy content residual of the generating standard tableau is earlier in colex order. -/
theorem murphyOperator_self_sub_content_mem_colex (t : Tableau n μ) [ht : IsStandard t]
    (j : Fin n) :
    murphyOperator t j (standardRealBasis t ⟨t, ht⟩) -
      (tableauContent t j : ℝ) • standardRealBasis t ⟨t, ht⟩ ∈ colexSubspace t t := by
  induction n generalizing μ with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    have hv : standardRealBasis t ⟨t, ht⟩ ∈
        lastRowSubspace t (rowWord t (Fin.last n)).val :=
      Submodule.subset_span ⟨⟨t, ht⟩, le_rfl, rfl⟩
    induction j using Fin.lastCases with
    | last =>
      exact lastRowSubspaceLT_le_colexSubspace t (murphyOperator_last_sub_content_mem (t := t) hv)
    | cast j =>
      let u := prefixTableau t n (Nat.le_succ n)
      have hu : IsStandard u := prefixTableau_isStandard (t := t) n (Nat.le_succ n)
      let x := murphyOperator t j.castSucc (standardRealBasis t ⟨t, ht⟩) -
        (tableauContent t j.castSucc : ℝ) • standardRealBasis t ⟨t, ht⟩
      let y := murphyOperator u j (standardRealBasis u ⟨u, hu⟩) -
        (tableauContent u j : ℝ) • standardRealBasis u ⟨u, hu⟩
      have hx : x ∈ lastRowSubspace t (rowWord t (Fin.last n)).val :=
        Submodule.sub_mem _ (murphyOperator_castSucc_mem_lastRowSubspace t j _ hv)
          (Submodule.smul_mem _ _ hv)
      have hbase : branchingMap t ⟨standardRealBasis t ⟨t, ht⟩, hv⟩ =
          standardRealBasis u ⟨u, hu⟩ := by
        apply Subtype.ext
        change prefixSliceReal t (Nat.le_succ n) (standardRealBasis t ⟨t, ht⟩).val = _
        rw [standardRealBasis_coe, prefixSliceReal_polytabloid, standardRealBasis_coe]
      have hxy : prefixSliceReal t (Nat.le_succ n) x.val = y.val := by
        simp only [x, y, Submodule.coe_sub, Submodule.coe_smul, map_sub, map_smul]
        rw [prefixSliceReal_murphyOperator (t := t) j hv, hbase,
          standardRealBasis_coe, prefixSliceReal_polytabloid, standardRealBasis_coe]
        rfl
      have hz : x - cornerLift t y ∈ lastRowSubspace t (rowWord t (Fin.last n)).val :=
        Submodule.sub_mem _ hx (cornerLift_mem_lastRowSubspace (t := t) y)
      have hker : x - cornerLift t y ∈
          lastRowSubspaceLT t (rowWord t (Fin.last n)).val := by
        apply (branchingMap_eq_zero_iff (t := t) ⟨_, hz⟩).mp
        apply Subtype.ext
        change prefixSliceReal t (Nat.le_succ n) (x.val - (cornerLift t y).val) = 0
        rw [map_sub, hxy, prefixSliceReal_cornerLift, sub_self]
      have hy : cornerLift t y ∈ colexSubspace t t :=
        cornerLift_mem_colexSubspace (t := t) (ih u j)
      exact (Submodule.sub_mem_iff_left _ hy).mp (lastRowSubspaceLT_le_colexSubspace t hker)

/-- Triangularity holds for every standard basis vector in the fixed real Specht space. -/
theorem murphyOperator_sub_content_mem_colex (t : Tableau n μ)
    (T : {u : Tableau n μ // IsStandard u}) (j : Fin n) :
    murphyOperator t j (standardRealBasis t T) -
      (tableauContent T.val j : ℝ) • standardRealBasis t T ∈ colexSubspace t T.val := by
  have hspan (v : Tableau n μ) :
      (colexSubspace v T.val).map (realSpan v).subtype =
        Submodule.span ℝ {x | ∃ U : {u : Tableau n μ // IsStandard u},
          TableauColexLT U.val T.val ∧ realCast n (μ.colLen 0) (polytabloidInt U.val) = x} := by
    rw [colexSubspace, Submodule.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨y, ⟨U, hU, rfl⟩, rfl⟩
      exact ⟨U, hU, (standardRealBasis_coe v U).symm⟩
    · rintro ⟨U, hU, rfl⟩
      exact ⟨standardRealBasis v U, ⟨U, hU, rfl⟩, standardRealBasis_coe v U⟩
  let x := murphyOperator t j (standardRealBasis t T) -
    (tableauContent T.val j : ℝ) • standardRealBasis t T
  let y := murphyOperator T.val j (standardRealBasis T.val T) -
    (tableauContent T.val j : ℝ) • standardRealBasis T.val T
  have hxy : y.val = x.val := by
    simp only [x, y, Submodule.coe_sub, Submodule.coe_smul, murphyOperator,
      LinearMap.sum_apply, Submodule.coe_sum, realSpechtRep_coe, standardRealBasis_coe]
  have h : x.val ∈ (colexSubspace T.val T.val).map (realSpan T.val).subtype :=
    ⟨y, murphyOperator_self_sub_content_mem_colex T.val  j, hxy⟩
  rw [hspan T.val, ← hspan t] at h
  obtain ⟨z, hz, hzx⟩ := h
  have he : z = x := Subtype.ext hzx
  rwa [he] at hz

end BostConjecture.Specht
