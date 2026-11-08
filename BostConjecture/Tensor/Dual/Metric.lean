/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# The canonical Hilbert form on the algebraic dual

Finite-dimensional Riesz representation identifies the existing algebraic
dual with the conjugate of the original space. The resulting Core has exactly
the continuous operator norm and supplies the evaluation estimate.

## Implementation notes

The dual core is a scoped instance in `BostConjecture.Tensor`. As for the
tensor core, its induced norm is installed only where that metric is needed.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Tensor

open Module

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

local instance : CompleteSpace E := FiniteDimensional.complete ℂ E

/-- Riesz representation on the actual algebraic dual, conjugate linear as usual. -/
def dualRieszEquiv : Dual ℂ E ≃ₗ⋆[ℂ] E :=
  (LinearMap.toContinuousLinearMap : Dual ℂ E ≃ₗ[ℂ] StrongDual ℂ E).trans
    (InnerProductSpace.toDual ℂ E).symm.toLinearEquiv

@[simp]
theorem dualRieszEquiv_inner (f : Dual ℂ E) (x : E) :
    inner ℂ (dualRieszEquiv E f) x = f x := by
  simp [dualRieszEquiv]

/-- The dual Hilbert form, with the reversed Riesz arguments ensuring the
usual conjugate-linearity convention. No new dual-module representation is used. -/
@[instance_reducible]
scoped instance dualCore : InnerProductSpace.Core ℂ (Dual ℂ E) where
  inner f g := inner ℂ (dualRieszEquiv E g) (dualRieszEquiv E f)
  conj_inner_symm f g := inner_conj_symm _ _
  re_inner_nonneg f := inner_self_nonneg
  add_left f g h := by simp only [map_add, inner_add_right]
  smul_left f g z := by
    rw [map_smulₛₗ, inner_smul_right]
  definite f hf := by
    apply (dualRieszEquiv E).injective
    simpa only [map_zero] using (inner_self_eq_zero.mp hf)

theorem dualCore_inner (f g : Dual ℂ E) :
    (dualCore E).inner f g = inner ℂ (dualRieszEquiv E g) (dualRieszEquiv E f) := rfl

/-- The norm prescribed by the dual Core equals the existing continuous operator norm. -/
theorem dualCore_norm (f : Dual ℂ E) :
    Real.sqrt (((dualCore E).inner f f).re) = ‖f.toContinuousLinearMap‖ := by
  rw [dualCore_inner]
  change Real.sqrt (RCLike.re (inner ℂ (dualRieszEquiv E f) (dualRieszEquiv E f))) = _
  rw [← norm_eq_sqrt_re_inner (𝕜 := ℂ)]
  exact (InnerProductSpace.toDual ℂ E).symm.norm_map _

/-- Evaluation has its actual operator-norm bound for the canonical dual form. -/
theorem dualCore_evaluation_le (f : Dual ℂ E) (x : E) :
    ‖f x‖ ≤ Real.sqrt (((dualCore E).inner f f).re) * ‖x‖ := by
  rw [dualCore_norm]
  exact f.toContinuousLinearMap.le_opNorm x

/-- A bound on every evaluation bounds the canonical dual norm. -/
theorem dualCore_norm_le (f : Dual ℂ E) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x : E, ‖f x‖ ≤ C * ‖x‖) :
    Real.sqrt (((dualCore E).inner f f).re) ≤ C := by
  simpa only [dualCore_norm] using f.toContinuousLinearMap.opNorm_le_bound hC h

/-- In any orthonormal frame the dual metric is the coefficient Gram form. -/
theorem dualCore_inner_basis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ E) (f g : Dual ℂ E) :
    (dualCore E).inner f g = ∑ i, star (f (b i)) * g (b i) := by
  rw [dualCore_inner, ← b.sum_inner_mul_inner]
  apply Finset.sum_congr rfl
  intro i hi
  rw [dualRieszEquiv_inner, ← inner_conj_symm, dualRieszEquiv_inner]
  simp only [RCLike.star_def, mul_comm]

end BostConjecture.Tensor
