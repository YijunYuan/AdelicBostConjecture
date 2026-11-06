/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Balanced.SpectralExpansion
public import BostConjecture.Balanced.PluckerNorm

/-!
# Balanced tensor exponential minimum

The tensor product of Hermitian exponentials is the exponential of their
Hermitian tensor-sum generator. This connects actual Plücker stationarity
to the exterior spectral convexity theorem.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Balanced

open scoped TensorProduct
open exteriorPower

variable {U W : Type*} [NormedAddCommGroup U] [InnerProductSpace ℂ U]
  [FiniteDimensional ℂ U] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [FiniteDimensional ℂ W]

local instance : NormedAddCommGroup (U ⊗[ℂ] W) := inferInstance
local instance : NormedSpace ℂ (U ⊗[ℂ] W) := inferInstance

local instance : Module ℝ (U ⊗[ℂ] W) := (NormedSpace.restrictScalars ℝ ℂ _).toModule
local instance : NormedSpace ℝ (U ⊗[ℂ] W) := NormedSpace.restrictScalars ℝ ℂ _

theorem isSymmetric_tensorSum (H : Module.End ℂ U) (J : Module.End ℂ W)
    (hH : H.IsSymmetric) (hJ : J.IsSymmetric) :
    (TensorProduct.map H LinearMap.id + TensorProduct.map LinearMap.id J :
      Module.End ℂ (U ⊗[ℂ] W)).IsSymmetric := by
  rw [LinearMap.isSymmetric_iff_isSelfAdjoint, LinearMap.isSelfAdjoint_iff']
  simp [hH.adjoint_eq, hJ.adjoint_eq]

/-- The equality of the actual tensor flow with the tensor-sum exponential. -/
theorem exp_tensorSum (H : Module.End ℂ U) (J : Module.End ℂ W)
    (hH : H.IsSymmetric) (hJ : J.IsSymmetric) (t : ℝ) :
    (NormedSpace.exp (t • LinearMap.toContinuousLinearMap
      (TensorProduct.map H LinearMap.id + TensorProduct.map LinearMap.id J :
        Module.End ℂ (U ⊗[ℂ] W)))).toLinearMap =
      TensorProduct.map (NormedSpace.exp (t • LinearMap.toContinuousLinearMap H)).toLinearMap
        (NormedSpace.exp (t • LinearMap.toContinuousLinearMap J)).toLinearMap := by
  apply ((hH.eigenvectorBasis rfl).tensorProduct (hJ.eigenvectorBasis rfl)).toBasis.ext
  rintro ⟨i, j⟩
  let u := hH.eigenvectorBasis rfl i
  let w := hJ.eigenvectorBasis rfl j
  let a := hH.eigenvalues rfl i
  let b := hJ.eigenvalues rfl j
  have hu : H u = (a : ℂ) • u := hH.apply_eigenvectorBasis rfl i
  have hw : J w = (b : ℂ) • w := hJ.apply_eigenvectorBasis rfl j
  have huv : (TensorProduct.map H LinearMap.id + TensorProduct.map LinearMap.id J :
      Module.End ℂ (U ⊗[ℂ] W))
      (u ⊗ₜ[ℂ] w) = ((a + b : ℝ) : ℂ) • (u ⊗ₜ[ℂ] w) := by
    simp [hu, hw, TensorProduct.smul_tmul', TensorProduct.tmul_smul, add_smul]
  simp only [OrthonormalBasis.coe_toBasis, OrthonormalBasis.tensorProduct_apply]
  change NormedSpace.exp (t • LinearMap.toContinuousLinearMap
    (TensorProduct.map H LinearMap.id + TensorProduct.map LinearMap.id J :
      Module.End ℂ (U ⊗[ℂ] W)))
    (u ⊗ₜ[ℂ] w) = _
  rw [exp_real_smul_apply_of_apply_eq_smul _ _ _ _ huv]
  simp only [TensorProduct.map_tmul, ContinuousLinearMap.coe_coe]
  change _ = NormedSpace.exp (t • LinearMap.toContinuousLinearMap H) u ⊗ₜ[ℂ]
    NormedSpace.exp (t • LinearMap.toContinuousLinearMap J) w
  rw [exp_real_smul_apply_of_apply_eq_smul _ _ _ _ hu,
    exp_real_smul_apply_of_apply_eq_smul _ _ _ _ hw]
  simp [mul_add, Real.exp_add, TensorProduct.smul_tmul', TensorProduct.tmul_smul,
    smul_smul, mul_comm]

theorem convexOn_exterior_tensor_exp_norm_sq
    (H : Module.End ℂ U) (J : Module.End ℂ W) (hH : H.IsSymmetric) (hJ : J.IsSymmetric)
    (s : ℕ) (z : ⋀[ℂ]^s (U ⊗[ℂ] W)) :
    ConvexOn ℝ Set.univ (fun t : ℝ => ‖exteriorPower.map s
      (TensorProduct.map (NormedSpace.exp (t • LinearMap.toContinuousLinearMap H)).toLinearMap
        (NormedSpace.exp (t • LinearMap.toContinuousLinearMap J)).toLinearMap) z‖ ^ 2) := by
  simpa only [exp_tensorSum H J hH hJ] using
    convexOn_exterior_exp_norm_sq _ (isSymmetric_tensorSum H J hH hJ) s z

/-- Balanced Plücker vectors have norm at least one along every traceless Hermitian tensor flow. -/
theorem IsBalanced.one_le_plucker_norm_sq_tensor_exp {s : ℕ}
    {S : Submodule ℂ (U ⊗[ℂ] W)} (hS : IsBalanced S)
    (v : OrthonormalBasis (Fin s) ℂ S) (H : Module.End ℂ U) (J : Module.End ℂ W)
    (hH : H.IsSymmetric) (hJ : J.IsSymmetric)
    (htrH : LinearMap.trace ℂ U H = 0) (htrJ : LinearMap.trace ℂ W J = 0) (t : ℝ) :
    1 ≤ ‖exteriorPower.map s
      (TensorProduct.map (NormedSpace.exp (t • LinearMap.toContinuousLinearMap H)).toLinearMap
        (NormedSpace.exp (t • LinearMap.toContinuousLinearMap J)).toLinearMap)
      (ιMulti ℂ s (fun i => (v i : U ⊗[ℂ] W)))‖ ^ 2 := by
  have hd := hS.hasDerivAt_plucker_norm_sq_tensor_exp_zero v H J htrH htrJ
  have hm := exterior_norm_sq_le_exp_of_hasDerivAt_zero _ (isSymmetric_tensorSum H J hH hJ)
    s (ιMulti ℂ s (fun i => (v i : U ⊗[ℂ] W)))
    (by simpa only [exp_tensorSum H J hH hJ] using hd) t
  simpa only [exp_tensorSum H J hH hJ, plucker_norm_sq] using hm

end BostConjecture.Balanced
