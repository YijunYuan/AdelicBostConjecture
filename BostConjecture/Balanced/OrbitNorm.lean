/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Balanced.SpecialLinearPolar
public import BostConjecture.Balanced.TensorExponential
public import BostConjecture.InvariantTheory.Plucker.Action

/-!
# The full special-linear orbit norm bound

Polar decomposition extends the balanced exponential minimum to every actual
special-linear orbit point. This excludes zero from its Euclidean closure;
the algebraic orbit-closure comparison is a separate theorem.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Balanced

open exteriorPower InvariantTheory
open scoped TensorProduct

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

theorem exterior_map_norm (f : E →ₗᵢ[ℂ] F) {s : ℕ} (z : ⋀[ℂ]^s E) :
    ‖exteriorPower.map s f.toLinearMap z‖ = ‖z‖ :=
  (LinearMap.isometryOfInner (exteriorPower.map s f.toLinearMap)
    (exterior_map_inner f)).norm_map z

variable {U W : Type*} [NormedAddCommGroup U] [InnerProductSpace ℂ U]
  [FiniteDimensional ℂ U] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [FiniteDimensional ℂ W]

theorem IsBalanced.one_le_plucker_norm_sq {s : ℕ}
    {S : Submodule ℂ (U ⊗[ℂ] W)} (hS : IsBalanced S)
    (v : OrthonormalBasis (Fin s) ℂ S)
    (g : SpecialLinearGroup ℂ U × SpecialLinearGroup ℂ W) :
    1 ≤ ‖pluckerRepresentation ℂ U W s g
      (ιMulti ℂ s (fun i => (v i : U ⊗[ℂ] W)))‖ ^ 2 := by
  obtain ⟨u, H, _, hH, htrH, hg⟩ := specialLinear_polar g.1
  obtain ⟨w, J, _, hJ, htrJ, hk⟩ := specialLinear_polar g.2
  rw [pluckerRepresentation_apply, hg, hk, TensorProduct.map_comp, map_comp,
    LinearMap.comp_apply]
  have huw : TensorProduct.map u.toLinearEquiv.toLinearMap w.toLinearEquiv.toLinearMap =
      (TensorProduct.mapIsometry u.toLinearIsometry w.toLinearIsometry).toLinearMap := rfl
  rw [huw, exterior_map_norm]
  simpa only [one_smul] using
    hS.one_le_plucker_norm_sq_tensor_exp v H J hH hJ htrH htrJ 1

/-- The analytic conclusion, with the actual orbit and the exterior Gram topology. -/
theorem IsBalanced.zero_not_mem_closure_plucker_orbit {s : ℕ}
    {S : Submodule ℂ (U ⊗[ℂ] W)} (hS : IsBalanced S)
    (v : OrthonormalBasis (Fin s) ℂ S) :
    (0 : ⋀[ℂ]^s (U ⊗[ℂ] W)) ∉ closure (Set.range (fun g =>
      pluckerRepresentation ℂ U W s g (ιMulti ℂ s (fun i => (v i : U ⊗[ℂ] W))))) := by
  have hc : closure (Set.range (fun g => pluckerRepresentation ℂ U W s g
      (ιMulti ℂ s (fun i => (v i : U ⊗[ℂ] W))))) ⊆
      {z : ⋀[ℂ]^s (U ⊗[ℂ] W) | 1 ≤ ‖z‖ ^ 2} := by
    apply closure_minimal
    · rintro _ ⟨g, rfl⟩
      exact hS.one_le_plucker_norm_sq v g
    · exact isClosed_le continuous_const (continuous_norm.pow 2)
  intro h
  have hz := hc h
  change 1 ≤ ‖(0 : ⋀[ℂ]^s (U ⊗[ℂ] W))‖ ^ 2 at hz
  have hnorm : ‖(0 : ⋀[ℂ]^s (U ⊗[ℂ] W))‖ = 0 :=
    @norm_zero (⋀[ℂ]^s (U ⊗[ℂ] W)) _
  rw [hnorm] at hz
  norm_num at hz

end BostConjecture.Balanced
