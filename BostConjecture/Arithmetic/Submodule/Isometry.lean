/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.HN.QuotientSemistable

/-!
# Intrinsic subspace degree under integral isometries

An integral equivalence commutes with taking integral parts of generic subspaces.
Its restrictions preserve degree when its actual complex fiber maps are isometries.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace BostConjecture.Arithmetic

variable {K : Type*} [Field K] [NumberField K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]

omit [NumberField K] in
/-- An integral automorphism commutes with taking the integral part of a generic subspace. -/
lemma integralPart_map_equiv (e : M ≃ₗ[𝓞 K] M) (X : Submodule K (K ⊗[𝓞 K] M)) :
    integralPart (X.map (e.baseChange (𝓞 K) K M M).toLinearMap) =
      (integralPart X).map e.toLinearMap := by
  ext x
  rw [mem_integralPart, Submodule.mem_map_equiv, Submodule.mem_map_equiv, mem_integralPart]
  rfl

namespace HermitianMetric

variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]

/-- Restrictions of an integral fiberwise isometry preserve submodule degree. -/
lemma degree_submodule_map_equiv (h : HermitianMetric K M)
    (e : M ≃ₗ[𝓞 K] M)
    (he : ∀ (σ : K →+* ℂ) (x y : ComplexFiber M σ),
      (h.fiber σ).inner (fiberMap e.toLinearMap σ x) (fiberMap e.toLinearMap σ y) =
        (h.fiber σ).inner x y)
    (P : Submodule (𝓞 K) M) :
    (h.submodule (P.map e.toLinearMap)).degree = (h.submodule P).degree := by
  let f := Submodule.equivMapOfInjective e.toLinearMap e.injective P
  symm
  apply degree_eq_of_equiv _ _ f
  intro σ x y
  have hf : (P.map e.toLinearMap).subtype.comp f.toLinearMap = e.toLinearMap.comp P.subtype := rfl
  change (h.fiber σ).inner
    ((fiberMap (P.map e.toLinearMap).subtype σ).comp (fiberMap f.toLinearMap σ) x)
    ((fiberMap (P.map e.toLinearMap).subtype σ).comp (fiberMap f.toLinearMap σ) y) = _
  rw [← fiberMap_comp, hf, fiberMap_comp]
  exact he σ _ _

/-- An actual integral isometry preserves the intrinsic generic subspace degree. -/
lemma subspaceDegree_map_equiv (h : HermitianMetric K M)
    (e : M ≃ₗ[𝓞 K] M)
    (he : ∀ (σ : K →+* ℂ) (x y : ComplexFiber M σ),
      (h.fiber σ).inner (fiberMap e.toLinearMap σ x) (fiberMap e.toLinearMap σ y) =
        (h.fiber σ).inner x y)
    (X : Submodule K (K ⊗[𝓞 K] M)) :
    h.subspaceDegree (X.map (e.baseChange (𝓞 K) K M M).toLinearMap) = h.subspaceDegree X := by
  exact (congrArg (fun P : Submodule (𝓞 K) M => (h.submodule P).degree)
    (integralPart_map_equiv e X)).trans (h.degree_submodule_map_equiv e he _)

end HermitianMetric
end BostConjecture.Arithmetic
