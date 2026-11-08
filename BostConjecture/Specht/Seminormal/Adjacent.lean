/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Specht.Seminormal.Spectral
public import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Adjacent transpositions on the monic orthogonal Specht basis

Content separation and the concrete Murphy relations determine the spectral
support. Literal relabeling of standard polytabloids fixes its normalization.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Specht

open OAI.Saxl InnerProductSpace
open scoped StandardColex

variable {n : ℕ} {μ : YoungDiagram}

/-- A standard tableau is determined by its sequence of box contents. -/
theorem IsStandard.eq_of_tableauContent_eq {t u : Tableau n μ}
    (ht : IsStandard t) (hu : IsStandard u)
    (h : ∀ i, tableauContent t i = tableauContent u i) : t = u := by
  apply Equiv.ext
  intro i
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    have hc := h i
    simp only [tableauContent] at hc
    have hcase (v w : Tableau n μ) (hv : IsStandard v)
        (hearlier : ∀ j < i, v j = w j)
        (hr : (w i).val.1 ≤ (v i).val.1)
        (hc : (w i).val.2 ≤ (v i).val.2) : v i = w i := by
      let j := v.symm (w i)
      have hj : j ≤ i := by simpa [j] using hv.label_mono ⟨hr, hc⟩
      rcases hj.eq_or_lt with hj | hj
      · simpa [j] using (congrArg v hj).symm
      · have he : w i = w j := by simpa [j] using hearlier j hj
        exact (hj.ne (w.injective he).symm).elim
    rcases le_total (u i).val.1 (t i).val.1 with hr | hr
    · exact hcase t u ht ih hr (by omega)
    · exact (hcase u t hu (fun j hj => (ih j hj).symm) hr (by omega)).symm

/-- The joint Murphy eigenspace for a standard content sequence is its actual monic line. -/
theorem eq_smul_orthogonalStandardBasis_of_eigenvalues (t : Tableau n μ)
    (T : {u : Tableau n μ // IsStandard u}) (x : realSpan t)
    (hx : ∀ j, murphyOperator t j x = (tableauContent T.val j : ℝ) • x) :
    x = (inner ℝ (orthogonalStandardBasis t T) x /
      ‖orthogonalStandardBasis t T‖ ^ 2) • orthogonalStandardBasis t T := by
  apply ext_inner_left_basis (orthogonalStandardBasis t)
  intro U
  by_cases hUT : U = T
  · subst U
    rw [real_inner_smul_right (F := realSpan t), real_inner_self_eq_norm_sq,
      div_mul_cancel₀ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr
        (orthogonalStandardBasis_ne_zero t T)))]
  · have hdiff : ∃ j, tableauContent U.val j ≠ tableauContent T.val j := by
      by_contra! h
      exact hUT (Subtype.ext (U.property.eq_of_tableauContent_eq T.property h))
    obtain ⟨j, hj⟩ := hdiff
    have hs := murphyOperator_symmetric t j (orthogonalStandardBasis t U) x
    rw [murphyOperator_orthogonalStandardBasis, hx,
      real_inner_smul_left (F := realSpan t), real_inner_smul_right (F := realSpan t)] at hs
    have hj' : (tableauContent U.val j : ℝ) ≠ (tableauContent T.val j : ℝ) :=
      fun h => hj (Int.cast_injective h)
    have hz : inner ℝ (orthogonalStandardBasis t U) x = 0 := (mul_eq_zero.mp (by nlinarith [hs] :
        ((tableauContent U.val j : ℝ) - tableauContent T.val j) *
          inner ℝ (orthogonalStandardBasis t U) x = 0)).resolve_left (sub_ne_zero.mpr hj')
    rw [hz, real_inner_smul_right (F := realSpan t), orthogonalStandardBasis_orthogonal t hUT,
      mul_zero]

/-- An adjacent swap commutes with every Murphy operator outside its two labels. -/
theorem realSpechtRep_adjacent_commute_murphyOperator (t : Tableau n μ)
    (i j k : Fin n) (hij : i.val + 1 = j.val) (hki : k ≠ i) (hkj : k ≠ j) :
    Commute (realSpechtRep t (Equiv.swap i j)) (murphyOperator t k) := by
  by_cases hjk : j < k
  · exact realSpechtRep_swap_commute_murphyOperator t i j k
      (by simp only [Fin.lt_def] at *; omega) hjk
  · have hki' : k < i := by simp only [Fin.lt_def] at *; omega
    apply realSpechtRep_commute_murphyOperator
    · exact Equiv.swap_apply_of_ne_of_ne hki hkj
    · intro x
      by_cases hxi : x = i
      · subst x
        simpa only [Equiv.swap_apply_left] using iff_of_false (not_lt_of_ge hki'.le)
          (by simp only [Fin.lt_def] at *; omega)
      by_cases hxj : x = j
      · subst x
        rw [Equiv.swap_apply_right]
        exact iff_of_false (by simp only [Fin.lt_def] at *; omega)
          (not_lt_of_ge hki'.le)
      rw [Equiv.swap_apply_of_ne_of_ne hxi hxj]

/-- The second affine-Hecke identity, with the smaller Murphy label on the left. -/
theorem murphyOperator_pred_mul_swap (t : Tableau n μ) (i j : Fin n)
    (hij : i.val + 1 = j.val) :
    murphyOperator t i * realSpechtRep t (Equiv.swap i j) =
      realSpechtRep t (Equiv.swap i j) * murphyOperator t j - 1 := by
  have hs : realSpechtRep t (Equiv.swap i j) * realSpechtRep t (Equiv.swap i j) = 1 := by
    rw [← map_mul, Equiv.swap_mul_self, map_one]
  rw [murphyOperator_succ t i j hij, mul_add, ← mul_assoc, ← mul_assoc, hs,
    one_mul, add_sub_cancel_right]

@[simp] theorem tableauContent_relabel_swap (t : Tableau n μ) (i j k : Fin n) :
    tableauContent (relabel (Equiv.swap i j) t) k =
      tableauContent t (Equiv.swap i j k) := by
  simp [tableauContent, relabel]

/-- A legal transposition has distinct contents; this is a consequence of content separation. -/
theorem tableauContent_ne_of_swap_standard {T U : Tableau n μ}
    (hT : IsStandard T) (hU : IsStandard U) (i j : Fin n) (hij : i ≠ j)
    (hUeq : U = relabel (Equiv.swap i j) T) : tableauContent T i ≠ tableauContent T j := by
  intro hc
  have he : U = T := hU.eq_of_tableauContent_eq hT (by
    intro k
    simpa only [hUeq, tableauContent_relabel_swap] using Equiv.apply_swap_eq_self hc k)
  have hi := congrArg (fun v : Tableau n μ => v i) (he.symm.trans hUeq)
  have : i = j := T.injective (by simpa [relabel] using hi)
  exact hij this

/-- The residual of the actual monic vector has the content spectrum of the swapped tableau. -/
theorem murphyOperator_swap_residual (t : Tableau n μ)
    (T : {u : Tableau n μ // IsStandard u}) (i j : Fin n)
    (hij : i.val + 1 = j.val)
    (hab : (tableauContent T.val j : ℝ) - tableauContent T.val i ≠ 0) (k : Fin n) :
    murphyOperator t k
      (realSpechtRep t (Equiv.swap i j) (orthogonalStandardBasis t T) -
        ((tableauContent T.val j : ℝ) - tableauContent T.val i)⁻¹ •
          orthogonalStandardBasis t T) =
      (tableauContent (relabel (Equiv.swap i j) T.val) k : ℝ) •
        (realSpechtRep t (Equiv.swap i j) (orthogonalStandardBasis t T) -
          ((tableauContent T.val j : ℝ) - tableauContent T.val i)⁻¹ •
            orthogonalStandardBasis t T) := by
  let x := orthogonalStandardBasis t T
  let s := realSpechtRep t (Equiv.swap i j)
  let a : ℝ := tableauContent T.val i
  let b : ℝ := tableauContent T.val j
  let r : ℝ := (b - a)⁻¹
  have hr : (b - a) * r = 1 := mul_inv_cancel₀ hab
  have hi : murphyOperator t i x = a • x := murphyOperator_orthogonalStandardBasis t T i
  have hj : murphyOperator t j x = b • x := murphyOperator_orthogonalStandardBasis t T j
  rw [tableauContent_relabel_swap]
  by_cases hki : k = i
  · subst k
    rw [Equiv.swap_apply_left]
    change murphyOperator t i (s x - r • x) = b • (s x - r • x)
    have he := LinearMap.congr_fun (murphyOperator_pred_mul_swap t i j hij) x
    change murphyOperator t i (s x) = s (murphyOperator t j x) - x at he
    rw [map_sub, map_smul, he, hi, hj, map_smul, smul_smul]
    calc
      b • s x - x - (r * a) • x = b • s x - (1 + r * a) • x := by module
      _ = b • s x - (b * r) • x := by rw [show 1 + r * a = b * r by nlinarith [hr]]
      _ = b • (s x - r • x) := by module
  by_cases hkj : k = j
  · subst k
    rw [Equiv.swap_apply_right]
    change murphyOperator t j (s x - r • x) = a • (s x - r • x)
    have he := LinearMap.congr_fun (murphyOperator_mul_swap t i j hij) x
    change murphyOperator t j (s x) = s (murphyOperator t i x) + x at he
    rw [map_sub, map_smul, he, hi, hj, map_smul, smul_smul]
    calc
      a • s x + x - (r * b) • x = a • s x + (1 - r * b) • x := by module
      _ = a • s x + (-(a * r)) • x := by rw [show 1 - r * b = -(a * r) by nlinarith [hr]]
      _ = a • (s x - r • x) := by module
  rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
  have he := LinearMap.congr_fun
    (realSpechtRep_adjacent_commute_murphyOperator t i j k hij hki hkj).eq x
  change s (murphyOperator t k x) = murphyOperator t k (s x) at he
  change murphyOperator t k (s x - r • x) =
    (tableauContent T.val k : ℝ) • (s x - r • x)
  rw [map_sub, map_smul, ← he, murphyOperator_orthogonalStandardBasis, map_smul]
  module

/-- A legal adjacent swap has support on exactly the two possible monic spectral lines. -/
theorem exists_swap_orthogonalStandardBasis_eq (t : Tableau n μ)
    (T U : {u : Tableau n μ // IsStandard u}) (i j : Fin n)
    (hij : i.val + 1 = j.val) (hU : U.val = relabel (Equiv.swap i j) T.val) :
    ∃ c : ℝ, realSpechtRep t (Equiv.swap i j) (orthogonalStandardBasis t T) =
      ((tableauContent T.val j : ℝ) - tableauContent T.val i)⁻¹ •
        orthogonalStandardBasis t T + c • orthogonalStandardBasis t U := by
  have hne := tableauContent_ne_of_swap_standard T.property U.property i j
    (by intro he; have := congrArg Fin.val he; omega) hU
  have hab : (tableauContent T.val j : ℝ) - tableauContent T.val i ≠ 0 :=
    sub_ne_zero.mpr (fun h => hne (Int.cast_injective h.symm))
  let x := realSpechtRep t (Equiv.swap i j) (orthogonalStandardBasis t T) -
    ((tableauContent T.val j : ℝ) - tableauContent T.val i)⁻¹ • orthogonalStandardBasis t T
  have hx : x = (inner ℝ (orthogonalStandardBasis t U) x /
      ‖orthogonalStandardBasis t U‖ ^ 2) • orthogonalStandardBasis t U :=
    eq_smul_orthogonalStandardBasis_of_eigenvalues t U x (fun k => by
      simpa only [hU] using murphyOperator_swap_residual t T i j hij hab k)
  refine ⟨inner ℝ (orthogonalStandardBasis t U) x /
    ‖orthogonalStandardBasis t U‖ ^ 2, ?_⟩
  exact (sub_eq_iff_eq_add.mp hx).trans (add_comm _ _)

/-- Literal relabeling fixes the off-diagonal coefficient to one for an increasing legal swap. -/
theorem realSpechtRep_swap_orthogonalStandardBasis (t : Tableau n μ)
    (T U : {u : Tableau n μ // IsStandard u}) (i j : Fin n)
    (hij : i.val + 1 = j.val) (hU : U.val = relabel (Equiv.swap i j) T.val)
    (hTU : T < U) :
    realSpechtRep t (Equiv.swap i j) (orthogonalStandardBasis t T) =
      ((tableauContent T.val j : ℝ) - tableauContent T.val i)⁻¹ •
        orthogonalStandardBasis t T + orthogonalStandardBasis t U := by
  obtain ⟨c, hc⟩ := exists_swap_orthogonalStandardBasis_eq t T U i j hij hU
  have hT : T.val = relabel (Equiv.swap i j) U.val := by
    rw [hU]
    apply Equiv.ext
    intro k
    simp [relabel]
  obtain ⟨d, hd⟩ := exists_swap_orthogonalStandardBasis_eq t U T i j hij hT
  have he : realSpechtRep t (Equiv.swap i j) (standardRealBasis t T) =
      standardRealBasis t U := by
    apply Subtype.ext
    rw [realSpechtRep_standardRealBasis_coe, standardRealBasis_coe, hU]
  let z := orthogonalStandardBasis t T - standardRealBasis t T
  have hz : z ∈ colexSubspace t T.val := orthogonalStandardBasis_sub_mem_colexSubspace t T
  have hzU : z ∈ colexSubspace t U.val := colexSubspace_mono t hTU.le hz
  have hzero : inner ℝ (orthogonalStandardBasis t U)
      (realSpechtRep t (Equiv.swap i j) z) = 0 := by
    rw [← realSpechtRep_swap_symmetric t i j, hd, inner_add_left,
      real_inner_smul_left (F := realSpan t), real_inner_smul_left (F := realSpan t),
      inner_orthogonalStandardBasis_eq_zero_of_mem_colexSubspace t U hzU,
      inner_orthogonalStandardBasis_eq_zero_of_mem_colexSubspace t T hz,
      mul_zero, mul_zero, add_zero]
  change inner ℝ (orthogonalStandardBasis t U)
    (realSpechtRep t (Equiv.swap i j)
      (orthogonalStandardBasis t T - standardRealBasis t T)) = 0 at hzero
  rw [map_sub, inner_sub_right, he, inner_orthogonalStandardBasis_standard, hc,
    inner_add_right, real_inner_smul_right (F := realSpan t),
    real_inner_smul_right (F := realSpan t),
    orthogonalStandardBasis_orthogonal t hTU.ne', real_inner_self_eq_norm_sq,
    mul_zero, zero_add] at hzero
  have hn : 0 < ‖orthogonalStandardBasis t U‖ ^ 2 :=
    sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (orthogonalStandardBasis_ne_zero t U))
  have hc1 : c = 1 := by nlinarith [hzero]
  simpa only [hc1, one_smul] using hc

/-- The normalized adjacent action gives the actual neighboring squared-norm ratio. -/
theorem norm_orthogonalStandardBasis_swap_sq (t : Tableau n μ)
    (T U : {u : Tableau n μ // IsStandard u}) (i j : Fin n)
    (hij : i.val + 1 = j.val) (hU : U.val = relabel (Equiv.swap i j) T.val)
    (hTU : T < U) :
    ‖orthogonalStandardBasis t U‖ ^ 2 =
      (1 - (((tableauContent T.val j : ℝ) - tableauContent T.val i)⁻¹) ^ 2) *
        ‖orthogonalStandardBasis t T‖ ^ 2 := by
  have hne := tableauContent_ne_of_swap_standard T.property U.property i j
    (by intro he; have := congrArg Fin.val he; omega) hU
  have h := norm_swap_residual_of_murphy_eigenvector t i j hij
    (orthogonalStandardBasis t T) (tableauContent T.val i) (tableauContent T.val j)
    (murphyOperator_orthogonalStandardBasis t T i)
    (murphyOperator_orthogonalStandardBasis t T j)
    (sub_ne_zero.mpr (fun h => hne (Int.cast_injective h.symm)))
  rwa [realSpechtRep_swap_orthogonalStandardBasis t T U i j hij hU hTU,
    add_sub_cancel_left] at h

end BostConjecture.Specht
