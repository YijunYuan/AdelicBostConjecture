/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Balanced.PolarLog
public import BostConjecture.Balanced.ExponentialDeterminant
public import Mathlib.LinearAlgebra.SpecialLinearGroup

/-!
# Determinant-one polar reduction

A determinant-one complex automorphism decomposes into a unitary map and
the exponential of a traceless Hermitian map. This reduces the orbit norm
inequality to the exponential estimate used in Section 7 of this paper.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Balanced

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

local instance : CompleteSpace E := FiniteDimensional.complete ℂ E

theorem det_adjoint (A : Module.End ℂ E) : LinearMap.det A.adjoint = star (LinearMap.det A) := by
  let b := stdOrthonormalBasis ℂ E
  rw [← LinearMap.det_toMatrix b.toBasis, LinearMap.toMatrix_adjoint b b,
    Matrix.det_conjTranspose, LinearMap.det_toMatrix]

theorem det_abs_eq_one (T : E →L[ℂ] E) (hT : Function.Injective T)
    (hdet : LinearMap.det T.toLinearMap = 1) : LinearMap.det T.abs.toLinearMap = 1 := by
  let H := (CFC.log T.abs).toLinearMap
  have hp : LinearMap.det T.abs.toLinearMap = (Real.exp (LinearMap.trace ℂ E H).re : ℂ) := by
    rw [← exp_log_abs T hT]
    exact det_exp_of_isSymmetric H (log_abs_isSymmetric T)
  have hsq : LinearMap.det T.abs.toLinearMap * LinearMap.det T.abs.toLinearMap = 1 := by
    rw [← LinearMap.det_comp]
    have h := congrArg ContinuousLinearMap.toLinearMap T.abs_comp_abs
    change T.abs.toLinearMap.comp T.abs.toLinearMap = T.adjoint.toLinearMap.comp T.toLinearMap at h
    rw [h, LinearMap.det_comp, ← ContinuousLinearMap.adjoint_toLinearMap, det_adjoint, hdet]
    simp
  rw [hp] at hsq
  have hr : Real.exp (LinearMap.trace ℂ E H).re * Real.exp (LinearMap.trace ℂ E H).re = 1 := by
    exact_mod_cast hsq
  have he : Real.exp (LinearMap.trace ℂ E H).re = 1 := by
    have := Real.exp_pos (LinearMap.trace ℂ E H).re
    nlinarith
  simpa [he] using hp

theorem trace_log_abs_eq_zero (T : E →L[ℂ] E) (hT : Function.Injective T)
    (hdet : LinearMap.det T.toLinearMap = 1) :
    LinearMap.trace ℂ E (CFC.log T.abs).toLinearMap = 0 := by
  apply trace_eq_zero_of_det_exp_eq_one _ (log_abs_isSymmetric T)
  change LinearMap.det (NormedSpace.exp (CFC.log T.abs)).toLinearMap = 1
  rw [exp_log_abs T hT]
  exact det_abs_eq_one T hT hdet

/-- Every special-linear map factors as a determinant-one unitary and the exponential
of a constructed traceless Hermitian operator. -/
theorem specialLinear_polar (g : SpecialLinearGroup ℂ E) :
    ∃ (u : E ≃ₗᵢ[ℂ] E) (H : Module.End ℂ E),
      LinearMap.det u.toLinearEquiv.toLinearMap = 1 ∧ H.IsSymmetric ∧
      LinearMap.trace ℂ E H = 0 ∧
      (g : E →ₗ[ℂ] E) = u.toLinearEquiv.toLinearMap.comp
        (NormedSpace.exp (LinearMap.toContinuousLinearMap H)).toLinearMap := by
  let T := LinearMap.toContinuousLinearMap (g : E →ₗ[ℂ] E)
  have hT : Function.Injective T := g.val.injective
  have hdet : LinearMap.det T.toLinearMap = 1 := g.det_eq_one
  let u := LinearIsometryEquiv.ofSurjective (polarIsometry T hT)
    ((LinearMap.injective_iff_surjective).mp (polarIsometry T hT).injective)
  refine ⟨u, (CFC.log T.abs).toLinearMap, ?_, log_abs_isSymmetric T,
    trace_log_abs_eq_zero T hT hdet, ?_⟩
  · have h := congrArg LinearMap.det (polarIsometry_comp_exp_log_abs T hT)
    rw [LinearMap.det_comp, exp_log_abs T hT, det_abs_eq_one T hT hdet, mul_one, hdet] at h
    exact h
  · exact (polarIsometry_comp_exp_log_abs T hT).symm

end BostConjecture.Balanced
