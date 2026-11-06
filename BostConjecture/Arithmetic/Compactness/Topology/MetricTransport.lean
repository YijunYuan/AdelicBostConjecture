/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Compactness.Topology.SemistabilityTopology
public import BostConjecture.Arithmetic.Submodule.NestedQuotient

/-!
# Transport of normalization and semistability along actual module isomorphisms

The existing pullback metric preserves degree under an integral isomorphism.
Submodules correspond by image, so every semistability inequality is retained.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace BostConjecture.Arithmetic.HermitianMetric

variable {K : Type*} [Field K] [NumberField K]
variable {M N : Type*} [AddCommGroup M] [Module (𝓞 K) M]
    [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
    [AddCommGroup N] [Module (𝓞 K) N]
    [Module.Finite (𝓞 K) N] [Module.Projective (𝓞 K) N]

/-- Pullback by a genuine integral isomorphism preserves degree. -/
theorem degree_pullback_equiv (h : HermitianMetric (K := K) N) (e : M ≃ₗ[𝓞 K] N) :
    (h.pullback e.toLinearMap e.injective).degree = h.degree :=
  degree_eq_of_equiv _ h e (fun _ _ _ => rfl)

/-- Pullback by an integral isomorphism preserves slope. -/
theorem slope_pullback_equiv (h : HermitianMetric (K := K) N) (e : M ≃ₗ[𝓞 K] N) :
    (h.pullback e.toLinearMap e.injective).slope = h.slope := by
  rw [slope, slope, degree_pullback_equiv,
    (e.baseChange (𝓞 K) K M N).finrank_eq]

/-- Induced degrees agree on corresponding actual integral submodules. -/
theorem degree_submodule_pullback_equiv (h : HermitianMetric (K := K) N)
    (e : M ≃ₗ[𝓞 K] N) (P : Submodule (𝓞 K) M) :
    ((h.pullback e.toLinearMap e.injective).submodule P).degree =
      (h.submodule (P.map e.toLinearMap)).degree := by
  let eP := Submodule.equivMapOfInjective e.toLinearMap e.injective P
  apply degree_eq_of_equiv _ _ eP
  intro σ x y
  change (h.fiber σ).inner
      (fiberMap (P.map e.toLinearMap).subtype σ (fiberMap eP.toLinearMap σ x))
      (fiberMap (P.map e.toLinearMap).subtype σ (fiberMap eP.toLinearMap σ y)) =
    (h.fiber σ).inner (fiberMap e.toLinearMap σ (fiberMap P.subtype σ x))
      (fiberMap e.toLinearMap σ (fiberMap P.subtype σ y))
  have he : (P.map e.toLinearMap).subtype.comp eP.toLinearMap =
      e.toLinearMap.comp P.subtype := by ext; rfl
  have he' := congrArg (fun f => fiberMap f σ) he
  simp only [fiberMap_comp] at he'
  exact congrArg₂ (h.fiber σ).inner (LinearMap.congr_fun he' x) (LinearMap.congr_fun he' y)

/-- Every semistability inequality transports along the actual module equivalence. -/
theorem IsSemistable.pullback_equiv {h : HermitianMetric (K := K) N}
    (hs : h.IsSemistable) (e : M ≃ₗ[𝓞 K] N) :
    (h.pullback e.toLinearMap e.injective).IsSemistable := by
  intro P hP
  let eP := Submodule.equivMapOfInjective e.toLinearMap e.injective P
  have hr := (eP.baseChange (𝓞 K) K P (P.map e.toLinearMap)).finrank_eq
  rw [slope_pullback_equiv, slope, degree_submodule_pullback_equiv, hr]
  exact hs _ (hr ▸ hP)

end BostConjecture.Arithmetic.HermitianMetric
