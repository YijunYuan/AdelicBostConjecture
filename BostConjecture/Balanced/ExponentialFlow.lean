/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Balanced.GramDerivative
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# First variation of the actual tensor exponential flow

Differentiating the tensor exponential at zero identifies its generator.
For a balanced subspace, the associated Gram determinant has zero first variation.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Balanced

open scoped TensorProduct

variable {U W : Type*} [NormedAddCommGroup U] [InnerProductSpace ℂ U]
  [FiniteDimensional ℂ U] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [FiniteDimensional ℂ W]

local instance : Module ℝ (U ⊗[ℂ] W) := (NormedSpace.restrictScalars ℝ ℂ _).toModule
local instance : NormedSpace ℝ (U ⊗[ℂ] W) := NormedSpace.restrictScalars ℝ ℂ _

/-- The operator exponential, evaluated at a vector, has its defining generator as
derivative at zero. -/
theorem hasDerivAt_exp_apply_zero (H : U →L[ℂ] U) (u : U) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • H) u) (H u) 0 := by
  let _ := FiniteDimensional.complete ℂ U
  have h := ((ContinuousLinearMap.apply ℂ U u).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    0 (hasDerivAt_exp_smul_const H (0 : ℝ))
  convert! h using 1
  simp

/-- Differentiate the actual tensor product of two operator exponentials. -/
theorem hasDerivAt_tensor_exp_zero (H : U →L[ℂ] U) (J : W →L[ℂ] W)
    (z : U ⊗[ℂ] W) :
    HasDerivAt (fun t : ℝ =>
      TensorProduct.mapL (NormedSpace.exp (t • H)) (NormedSpace.exp (t • J)) z)
      ((TensorProduct.map H.toLinearMap LinearMap.id +
        TensorProduct.map LinearMap.id J.toLinearMap : Module.End ℂ (U ⊗[ℂ] W)) z) 0 := by
  induction z using TensorProduct.inductionOn with
  | tmul u w =>
    have h := ((TensorProduct.mkL ℂ U W).bilinearRestrictScalars ℝ).hasDerivAt_of_bilinear
      (fun _ => hasDerivAt_exp_apply_zero H u) (fun _ => hasDerivAt_exp_apply_zero J w)
    simpa [TensorProduct.mapL_tmul, add_comm] using h
  | add x y hx hy =>
    convert! HasDerivAt.add hx hy using 1 <;> simp [map_add]
    rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Balance forces zero first variation along the actual tensor exponential flow. -/
theorem IsBalanced.hasDerivAt_re_gramDet_tensor_exp_zero
    {S : Submodule ℂ (U ⊗[ℂ] W)} (hS : IsBalanced S) (v : OrthonormalBasis ι ℂ S)
    (H : Module.End ℂ U) (J : Module.End ℂ W)
    (hH : LinearMap.trace ℂ U H = 0) (hJ : LinearMap.trace ℂ W J = 0) :
    HasDerivAt (fun t : ℝ => (Matrix.of fun i j => inner ℂ
      (TensorProduct.mapL (NormedSpace.exp (t • LinearMap.toContinuousLinearMap H))
        (NormedSpace.exp (t • LinearMap.toContinuousLinearMap J)) (v i : U ⊗[ℂ] W))
      (TensorProduct.mapL (NormedSpace.exp (t • LinearMap.toContinuousLinearMap H))
        (NormedSpace.exp (t • LinearMap.toContinuousLinearMap J))
        (v j : U ⊗[ℂ] W))).det.re) 0 0 := by
  apply hS.hasDerivAt_re_gramDet_zero v H J hH hJ
  · intro i
    simp
  · intro i
    exact hasDerivAt_tensor_exp_zero (LinearMap.toContinuousLinearMap H)
      (LinearMap.toContinuousLinearMap J) (v i)

end BostConjecture.Balanced
