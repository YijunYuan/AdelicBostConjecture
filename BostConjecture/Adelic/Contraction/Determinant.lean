/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.Analysis.Determinant.Basic
public import ArakelovGeometry.Analysis.Determinant.Pairing

/-!
# Non-Archimedean determinant estimates

The determinant estimate used in Lemma 6.1 of this paper, with no
nontriviality hypothesis on the absolute value.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Adelic.Contraction

open ArakelovGeometry Module

variable {L E ι : Type*} [NormedField L] [IsUltrametricDist L]
  [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace L E]

/-- Coordinate bounds in a nearly orthogonal basis give the determinant bound
without a factorial loss. The field may carry the trivial norm. -/
theorem norm_basis_det_le (b : Basis ι L E) (c : ι → ℝ)
    (hc : ∀ i x, ‖b.coord i x‖ ≤ c i * ‖x‖) (x : ι → E) :
    ‖b.det x‖ ≤ (∏ i, c i) * ∏ i, ‖x i‖ := by
  rw [Basis.det_apply]
  apply norm_det_le_prod_of_entry_le _ c (fun i ↦ ‖x i‖)
  intro i j
  exact hc i (x j)

/-- The dual coordinate operator norms give an intrinsic version of the
non-Archimedean determinant bound. -/
theorem norm_basis_det_le_dual_prod [CompleteSpace L] [FiniteDimensional L E]
    (b : Basis ι L E) (x : ι → E) :
    ‖b.det x‖ ≤ (∏ i, linearMapOperatorSeminorm (b.coord i)) * ∏ i, ‖x i‖ :=
  norm_basis_det_le b _ (fun i x ↦ norm_linearMap_apply_le (b.coord i) x) x

/-- A weighted coordinate lower bound passes to the determinant. This is the
local algebraic estimate behind the alpha-orthogonal-basis argument. -/
theorem prod_mul_norm_basis_det_le (b : Basis ι L E) (w : ι → ℝ)
    (hw : ∀ i, 0 < w i) (hb : ∀ i x, w i * ‖b.coord i x‖ ≤ ‖x‖)
    (x : ι → E) :
    (∏ i, w i) * ‖b.det x‖ ≤ ∏ i, ‖x i‖ := by
  have hcoord (i : ι) (y : E) : ‖b.coord i y‖ ≤ (w i)⁻¹ * ‖y‖ := by
    rw [← div_eq_inv_mul]
    exact (le_div_iff₀ (hw i)).2 (by simpa only [mul_comm] using hb i y)
  have hprod : (∏ i, w i) ≠ 0 :=
    ne_of_gt (Finset.prod_pos fun i _ ↦ hw i)
  calc
    (∏ i, w i) * ‖b.det x‖ ≤
        (∏ i, w i) * ((∏ i, (w i)⁻¹) * ∏ i, ‖x i‖) :=
      mul_le_mul_of_nonneg_left (norm_basis_det_le b _ hcoord x)
        (Finset.prod_nonneg fun i _ ↦ (hw i).le)
    _ = ∏ i, ‖x i‖ := by
      rw [Finset.prod_inv_distrib, ← mul_assoc, mul_inv_cancel₀ hprod, one_mul]

omit [IsUltrametricDist L] [Fintype ι] [DecidableEq ι] in
/-- Nearly optimal bases supply the coordinate half of alpha-orthogonality.
This includes trivially valued complete fields. -/
theorem exists_basis_coord_bound [CompleteSpace L] [FiniteDimensional L E] [Finite ι]
    (b : Basis ι L E) {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ e : Basis ι L E, ∀ i x, α * ‖e i‖ * ‖e.coord i x‖ ≤ ‖x‖ := by
  obtain ⟨e, he⟩ := exists_basis_mul_dual_norm_le b hα hα1
  refine ⟨e, fun i x ↦ ?_⟩
  have hi : α * (‖e i‖ * linearMapOperatorSeminorm (e.coord i)) ≤ 1 := by
    simpa only [mul_inv_cancel₀ hα.ne'] using
      mul_le_mul_of_nonneg_left (he i).2 hα.le
  calc
    α * ‖e i‖ * ‖e.coord i x‖ ≤
        α * ‖e i‖ * (linearMapOperatorSeminorm (e.coord i) * ‖x‖) :=
      mul_le_mul_of_nonneg_left (norm_linearMap_apply_le (e.coord i) x)
        (mul_nonneg hα.le (norm_nonneg _))
    _ = (α * (‖e i‖ * linearMapOperatorSeminorm (e.coord i))) * ‖x‖ := by ring
    _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hi (norm_nonneg _)
    _ = ‖x‖ := one_mul _

end BostConjecture.Adelic.Contraction
