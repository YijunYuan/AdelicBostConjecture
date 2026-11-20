/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import AdelicBostConjecture.Specht.Branching.Triangular
public import AdelicBostConjecture.Specht.Seminormal.Orthogonal

/-!
# Content eigenvalues of the actual monic orthogonal basis

Symmetry and the proved colex triangular action identify each Murphy
eigenvalue. No spectrum or eigenvector hypothesis is imposed on the basis.
-/

@[expose] public section

noncomputable section

namespace AdelicBostConjecture.Specht

open OAI.Saxl InnerProductSpace
open scoped StandardColex

variable {n : ℕ} {μ : YoungDiagram}

namespace StandardColex

scoped instance : LocallyFiniteOrderBot {t : Tableau n μ // IsStandard t} :=
  LocallyFiniteOrderBot.ofIic' _ (fun T => Finset.univ.filter (· ≤ T))
    (fun _ _ => by simp only [Finset.mem_filter, Finset.mem_univ, true_and])

end StandardColex

theorem colexSubspace_eq_span (t : Tableau n μ)
    (T : {u : Tableau n μ // IsStandard u}) :
    colexSubspace t T.val = Submodule.span ℝ (standardRealBasis t '' Set.Iio T) := by
  unfold colexSubspace
  apply congrArg (Submodule.span ℝ)
  ext x
  constructor
  · rintro ⟨U, hU, rfl⟩
    exact ⟨U, (standardColex_lt_iff U T).mpr hU, rfl⟩
  · rintro ⟨U, hU, rfl⟩
    exact ⟨U, (standardColex_lt_iff U T).mp hU, rfl⟩

theorem colexSubspace_mono (t : Tableau n μ)
    {U T : {u : Tableau n μ // IsStandard u}} (h : U ≤ T) :
    colexSubspace t U.val ≤ colexSubspace t T.val := by
  rw [colexSubspace_eq_span t U, colexSubspace_eq_span t T]
  exact Submodule.span_mono (Set.image_mono (fun _ hU => lt_of_lt_of_le hU h))

/-- Triangularity implies invariance of each earlier-tableau span. -/
theorem murphyOperator_mem_colexSubspace (t : Tableau n μ)
    (T : {u : Tableau n μ // IsStandard u}) (j : Fin n)
    {x : realSpan t} (hx : x ∈ colexSubspace t T.val) :
    murphyOperator t j x ∈ colexSubspace t T.val := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨U, hU, rfl⟩ := hx
    have hb : standardRealBasis t U ∈ colexSubspace t T.val :=
      Submodule.subset_span ⟨U, hU, rfl⟩
    have hr := colexSubspace_mono t ((standardColex_lt_iff U T).mpr hU).le
      (murphyOperator_sub_content_mem_colex t U j)
    exact (Submodule.sub_mem_iff_left _ (Submodule.smul_mem _ _ hb)).mp hr
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul a x hx ih => simpa only [map_smul] using Submodule.smul_mem _ a ih

/-- Earlier orthogonal vectors belong to the same earlier standard span. -/
theorem orthogonalStandardBasis_mem_colexSubspace (t : Tableau n μ)
    {U T : {u : Tableau n μ // IsStandard u}} (h : U < T) :
    orthogonalStandardBasis t U ∈ colexSubspace t T.val := by
  rw [colexSubspace_eq_span t T, ← span_gramSchmidt_Iio ℝ (standardRealBasis t) T,
    orthogonalStandardBasis_apply]
  exact Submodule.subset_span ⟨U, h, rfl⟩

/-- Monic orthogonalization changes a standard vector only by earlier vectors. -/
theorem orthogonalStandardBasis_sub_mem_colexSubspace (t : Tableau n μ)
    (T : {u : Tableau n μ // IsStandard u}) :
    orthogonalStandardBasis t T - standardRealBasis t T ∈ colexSubspace t T.val := by
  rw [orthogonalStandardBasis_eq_sub_sum, sub_sub_cancel_left]
  apply Submodule.neg_mem
  apply Submodule.sum_mem
  exact fun U hU => Submodule.smul_mem _ _
    (orthogonalStandardBasis_mem_colexSubspace t (Finset.mem_Iio.mp hU))

/-- Each monic orthogonal vector is perpendicular to the earlier standard span. -/
theorem inner_orthogonalStandardBasis_eq_zero_of_mem_colexSubspace (t : Tableau n μ)
    (T : {u : Tableau n μ // IsStandard u}) {x : realSpan t}
    (hx : x ∈ colexSubspace t T.val) : inner ℝ (orthogonalStandardBasis t T) x = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨U, hU, rfl⟩ := hx
    rw [orthogonalStandardBasis_apply]
    exact gramSchmidt_inv_triangular ℝ (standardRealBasis t)
      ((standardColex_lt_iff U T).mpr hU)
  | zero => exact inner_zero_right _
  | add x y hx hy ihx ihy => rw [inner_add_right, ihx, ihy, add_zero]
  | smul a x hx ih => rw [inner_smul_right, ih, mul_zero]

/-- The concrete Murphy eigenvalue of every monic orthogonal standard vector is its box content. -/
theorem murphyOperator_orthogonalStandardBasis (t : Tableau n μ)
    (T : {u : Tableau n μ // IsStandard u}) (j : Fin n) :
    murphyOperator t j (orthogonalStandardBasis t T) =
      (tableauContent T.val j : ℝ) • orthogonalStandardBasis t T := by
  let f := orthogonalStandardBasis t T
  let c : ℝ := tableauContent T.val j
  let z := murphyOperator t j f - c • f
  have hd := orthogonalStandardBasis_sub_mem_colexSubspace t T
  have hz : z ∈ colexSubspace t T.val := by
    have h₁ := murphyOperator_mem_colexSubspace t T j hd
    have h₂ := (colexSubspace t T.val).smul_mem c hd
    have h₃ := murphyOperator_sub_content_mem_colex t T j
    have he : z = (murphyOperator t j (f - standardRealBasis t T) -
        c • (f - standardRealBasis t T)) +
        (murphyOperator t j (standardRealBasis t T) - c • standardRealBasis t T) := by
      simp only [z, map_sub, smul_sub]
      abel
    simpa only [he] using Submodule.add_mem _ (Submodule.sub_mem _ h₁ h₂) h₃
  have hzero : inner ℝ z z = 0 := by
    change inner ℝ (murphyOperator t j f - c • f) z = 0
    rw [inner_sub_left, murphyOperator_symmetric t j f z,
      inner_orthogonalStandardBasis_eq_zero_of_mem_colexSubspace t T
        (murphyOperator_mem_colexSubspace t T j hz), real_inner_smul_left (F := realSpan t),
      inner_orthogonalStandardBasis_eq_zero_of_mem_colexSubspace t T hz,
      mul_zero, sub_zero]
  exact sub_eq_zero.mp ((inner_self_eq_zero).mp hzero)

end AdelicBostConjecture.Specht
