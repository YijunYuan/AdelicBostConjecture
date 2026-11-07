/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Main.MaxSlope.LowerBound

/-!
# Maximal slope under integral isometries

The attained first HN submodule maps to an actual submodule of the target.
This supplies the invariant needed for canonical finite tensor regroupings.
-/

@[expose] public section
noncomputable section
open NumberField TensorProduct

namespace BostConjecture.Arithmetic.HermitianMetric

universe u
variable {K : Type*} [Field K] [NumberField K]
variable {M N : Type u} [AddCommGroup M] [Module (𝓞 K) M]
    [AddCommGroup N] [Module (𝓞 K) N]
    [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
    [Module.Finite (𝓞 K) N] [Module.Projective (𝓞 K) N]
    [Nontrivial (K ⊗[𝓞 K] M)] [Nontrivial (K ⊗[𝓞 K] N)]

/-- An actual integral fiberwise isometric injection cannot decrease maximal slope. -/
lemma maxSlope_le_of_isometric_injection (h : HermitianMetric (K := K) M)
    (g : HermitianMetric (K := K) N) (f : M →ₗ[𝓞 K] N)
    (hf : Function.Injective f)
    (he : ∀ (σ : K →+* ℂ) (x y : ComplexFiber M σ),
      (g.fiber σ).inner (fiberMap f σ x) (fiberMap f σ y) = (h.fiber σ).inner x y) :
    h.maxSlope ≤ g.maxSlope := by
  let P := h.hnSubmodule 1
  let j := f.comp P.subtype
  have hj : Function.Injective j := hf.comp P.injective_subtype
  have hm : g.pullback j hj = h.submodule P := by
    apply ext_inner
    intro σ x y
    change (g.fiber σ).inner (fiberMap j σ x) (fiberMap j σ y) = _
    rw [show j = f.comp P.subtype from rfl, fiberMap_comp]
    exact he σ _ _
  have hs := g.slope_pullback_le_maxSlope j hj h.hnSubmodule_one_rank_pos
  rw [hm] at hs
  simpa only [P, h.slope_hnSubmodule_one] using hs

/-- Canonical integral isometries preserve the attained maximal slope. -/
theorem maxSlope_eq_of_equiv (h : HermitianMetric (K := K) M)
    (g : HermitianMetric (K := K) N) (e : M ≃ₗ[𝓞 K] N)
    (he : ∀ (σ : K →+* ℂ) (x y : ComplexFiber M σ),
      (g.fiber σ).inner (fiberMap e.toLinearMap σ x) (fiberMap e.toLinearMap σ y) =
        (h.fiber σ).inner x y) : h.maxSlope = g.maxSlope := by
  apply le_antisymm (maxSlope_le_of_isometric_injection h g e.toLinearMap e.injective he)
  apply maxSlope_le_of_isometric_injection g h e.symm.toLinearMap e.symm.injective
  intro σ x y
  have hi (z : ComplexFiber N σ) :
      fiberMap e.toLinearMap σ (fiberMap e.symm.toLinearMap σ z) = z := by
    let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
    exact (e.baseChange (𝓞 K) ℂ M N).apply_symm_apply z
  simpa only [hi] using (he σ (fiberMap e.symm.toLinearMap σ x)
    (fiberMap e.symm.toLinearMap σ y)).symm

end BostConjecture.Arithmetic.HermitianMetric
