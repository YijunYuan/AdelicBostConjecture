module

public import BostConjecture.Analysis.InnerProductSpace.Polar
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
public import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Invertible polar factors and their Hermitian logarithms

This consumes the selectively ported polar decomposition. In finite dimension,
injectivity makes its positive modulus invertible and its polar factor a full
linear isometry. The canonical CFC logarithm exponentiates to the modulus.
Determinant-one and trace-zero conclusions are separate lemmas.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Balanced

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

local instance : CompleteSpace E := FiniteDimensional.complete ℂ E

theorem abs_injective (T : E →L[ℂ] E) (hT : Function.Injective T) :
    Function.Injective T.abs :=
  LinearMap.ker_eq_bot.mp (T.ker_abs_eq.trans (LinearMap.ker_eq_bot.mpr hT))

theorem abs_bijective (T : E →L[ℂ] E) (hT : Function.Injective T) :
    Function.Bijective T.abs :=
  ⟨abs_injective T hT, (LinearMap.injective_iff_surjective).mp (abs_injective T hT)⟩

theorem abs_isStrictlyPositive (T : E →L[ℂ] E) (hT : Function.Injective T) :
    IsStrictlyPositive T.abs :=
  (ContinuousLinearMap.isUnit_iff_bijective.mpr (abs_bijective T hT)).isStrictlyPositive T.abs_nonneg

theorem norm_polar_apply (T : E →L[ℂ] E) (hT : Function.Injective T) (x : E) :
    ‖T.polar x‖ = ‖x‖ := by
  obtain ⟨y, rfl⟩ := (abs_bijective T hT).surjective x
  rw [← ContinuousLinearMap.comp_apply, T.polar_comp_abs, T.norm_abs_apply]

/-- The actual polar factor of an injective endomorphism is a full linear isometry. -/
def polarIsometry (T : E →L[ℂ] E) (hT : Function.Injective T) : E →ₗᵢ[ℂ] E where
  toLinearMap := T.polar.toLinearMap
  norm_map' := norm_polar_apply T hT

@[simp]
theorem polarIsometry_apply (T : E →L[ℂ] E) (hT : Function.Injective T) (x : E) :
    polarIsometry T hT x = T.polar x := rfl

theorem log_abs_isSymmetric (T : E →L[ℂ] E) :
    (CFC.log T.abs).toLinearMap.IsSymmetric :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp IsSelfAdjoint.log

theorem exp_log_abs (T : E →L[ℂ] E) (hT : Function.Injective T) :
    NormedSpace.exp (CFC.log T.abs) = T.abs :=
  CFC.exp_log _ (abs_isStrictlyPositive T hT)

/-- Polar decomposition with a constructed Hermitian logarithm of the positive factor. -/
theorem polarIsometry_comp_exp_log_abs (T : E →L[ℂ] E) (hT : Function.Injective T) :
    (polarIsometry T hT).toLinearMap.comp (NormedSpace.exp (CFC.log T.abs)).toLinearMap =
      T.toLinearMap := by
  rw [exp_log_abs T hT]
  exact congrArg ContinuousLinearMap.toLinearMap T.polar_comp_abs

end BostConjecture.Balanced
