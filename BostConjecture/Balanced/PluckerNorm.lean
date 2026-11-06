/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Balanced.ExponentialFlow
public import BostConjecture.Balanced.ExteriorMetric

/-!
# Plücker norms and balanced first variation

The full exterior Gram metric identifies the norm of the actual Plücker
vector with the Gram determinant. Unitary maps preserve this norm, and the
balanced projection equations force zero variation along tensor exponentials.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Balanced

open exteriorPower
open scoped TensorProduct

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F] {s : ℕ}

/-- An isometry induces an isometry of the complex exterior Gram form. -/
theorem exterior_map_inner (f : E →ₗᵢ[ℂ] F) (x y : ⋀[ℂ]^s E) :
    inner ℂ (exteriorPower.map s f.toLinearMap x) (exteriorPower.map s f.toLinearMap y) =
      inner ℂ x y := by
  apply Tensor.inner_ext_of_span (ιMulti ℂ s) (ιMulti_span ℂ s E)
    (InnerProductSpace.toCore (𝕜 := ℂ) (E := ⋀[ℂ]^s F))
    (InnerProductSpace.toCore (𝕜 := ℂ) (E := ⋀[ℂ]^s E))
    (exteriorPower.map s f.toLinearMap) LinearMap.id _ x y
  intro v w
  simp only [LinearMap.id_apply, map_apply_ιMulti, exterior_inner_ιMulti,
    Function.comp_apply, LinearIsometry.coe_toLinearMap, f.inner_map_map]

/-- The Plücker vector of an orthonormal frame has squared norm one. -/
theorem plucker_norm_sq (S : Submodule ℂ E) (v : OrthonormalBasis (Fin s) ℂ S) :
    ‖ιMulti ℂ s (fun i => (v i : E))‖ ^ 2 = 1 := by
  rw [exterior_norm_sq_ιMulti]
  have hgram : (Matrix.of fun i j => inner ℂ (v i : E) (v j : E)) = 1 := by
    ext i j
    exact (orthonormal_iff_ite.mp v.orthonormal i j)
  rw [hgram, Matrix.det_one]
  rfl

variable {U W : Type*} [NormedAddCommGroup U] [InnerProductSpace ℂ U]
  [FiniteDimensional ℂ U] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [FiniteDimensional ℂ W]

/-- Balance gives zero first variation of the actual exterior Plücker norm. -/
theorem IsBalanced.hasDerivAt_plucker_norm_sq_tensor_exp_zero
    {S : Submodule ℂ (U ⊗[ℂ] W)} (hS : IsBalanced S)
    (v : OrthonormalBasis (Fin s) ℂ S) (H : Module.End ℂ U) (J : Module.End ℂ W)
    (hH : LinearMap.trace ℂ U H = 0) (hJ : LinearMap.trace ℂ W J = 0) :
    HasDerivAt (fun t : ℝ => ‖exteriorPower.map s
      (TensorProduct.map (NormedSpace.exp (t • LinearMap.toContinuousLinearMap H)).toLinearMap
        (NormedSpace.exp (t • LinearMap.toContinuousLinearMap J)).toLinearMap)
      (ιMulti ℂ s (fun i => (v i : U ⊗[ℂ] W)))‖ ^ 2) 0 0 := by
  simpa only [map_apply_ιMulti, exterior_norm_sq_ιMulti, Function.comp_apply,
    TensorProduct.mapL_apply] using
    hS.hasDerivAt_re_gramDet_tensor_exp_zero v H J hH hJ

end BostConjecture.Balanced
