/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Dual.Fiber

/-!
# Finiteness of bounded intrinsic integral sections

Finite projectivity embeds the integral module into a finite free module.
The coordinate functionals are bounded on each Hermitian fiber; finiteness
of algebraic integers with bounded conjugates then gives the actual finite
set of sections. No freeness assumption on the original module is used.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace BostConjecture.Arithmetic.HermitianMetric

variable {K : Type*} [Field K] [NumberField K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]
variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]

omit [NumberField K] in
/-- Every integral coordinate is bounded on each actual archimedean fiber. -/
lemma exists_coordinate_bound (h : HermitianMetric K M)
    (f : M →ₗ[𝓞 K] 𝓞 K) (σ : K →+* ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : M, ‖σ (f x)‖ ≤ C * h.sectionNorm σ x := by
  let : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
  let := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
  let F := (dualFiberEquiv (M := M) σ (fiberSection _ σ f)).toContinuousLinearMap
  refine ⟨‖F‖, F.opNorm_nonneg, fun x => ?_⟩
  have hF := F.le_opNorm (fiberSection M σ x)
  change ‖dualFiberEquiv M σ (fiberSection _ σ f) (fiberSection M σ x)‖ ≤
    ‖F‖ * h.sectionNorm σ x at hF
  rwa [dualFiberEquiv_section] at hF

/-- Integral sections bounded at every embedding form a finite set. -/
theorem finite_bounded_sections (h : HermitianMetric K M)
    (b : (K →+* ℂ) → ℝ) : {x : M | ∀ σ, h.sectionNorm σ x ≤ b σ}.Finite := by
  classical
  obtain ⟨n, p, i, hp, hi, hpi⟩ := Module.Finite.exists_comp_eq_id_of_projective (𝓞 K) M
  let f (j : Fin n) : M →ₗ[𝓞 K] 𝓞 K := (LinearMap.proj j).comp i
  choose C hC hbound using fun (j : Fin n) (σ : K →+* ℂ) =>
    h.exists_coordinate_bound (f j) σ
  let B (j : Fin n) : ℝ := ∑ σ : K →+* ℂ, max (C j σ * b σ) 0
  let S (j : Fin n) : Set (𝓞 K) := {a | ∀ σ : K →+* ℂ, ‖σ a‖ ≤ B j}
  have hS (j : Fin n) : (S j).Finite := by
    have hf := (NumberField.Embeddings.finite_of_norm_le K ℂ (B j)).preimage
      (f := fun a : 𝓞 K => (a : K)) (RingOfIntegers.coe_injective.injOn)
    apply hf.subset
    exact fun a ha => ⟨a.property, ha⟩
  apply ((Set.Finite.pi hS).preimage hi.injOn).subset
  intro x hx
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left]
  intro j σ
  calc
    ‖σ (i x j)‖ ≤ C j σ * h.sectionNorm σ x := hbound j σ x
    _ ≤ C j σ * b σ := mul_le_mul_of_nonneg_left (hx σ) (hC j σ)
    _ ≤ max (C j σ * b σ) 0 := le_max_left _ _
    _ ≤ B j := Finset.single_le_sum
      (f := fun τ => max (C j τ * b τ) 0) (fun τ _ => le_max_right _ _) (Finset.mem_univ σ)

end BostConjecture.Arithmetic.HermitianMetric
