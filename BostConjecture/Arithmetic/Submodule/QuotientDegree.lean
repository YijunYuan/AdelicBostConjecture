/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Submodule.Supermodular
public import BostConjecture.Arithmetic.Degree.Isometry

/-!
# Degree of an integral submodule of a quotient

The inverse image under the quotient map is an actual integral submodule.
The induced quotient is canonically isometric to the given submodule, so
exact degree and rank additivity give its degree and dimension.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace BostConjecture.Arithmetic

variable {K : Type*} [Field K] [NumberField K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]

/-- The canonical identification of the quotient of a preimage with its image. -/
def quotientPreimageEquiv (P : Submodule (𝓞 K) M) (N : Submodule (𝓞 K) (M ⧸ P)) :
    ((N.comap P.mkQ) ⧸ P.comap (N.comap P.mkQ).subtype) ≃ₗ[𝓞 K] N := by
  let f := submoduleQuotientMap P (N.comap P.mkQ)
  have hf : ∀ x, f x ∈ N := by
    intro x
    obtain ⟨y, rfl⟩ := (P.comap (N.comap P.mkQ).subtype).mkQ_surjective x
    exact y.property
  refine LinearEquiv.ofBijective (f.codRestrict N hf) ⟨?_, ?_⟩
  · intro x y hxy
    exact submoduleQuotientMap_injective P _ (congrArg Subtype.val hxy)
  · intro y
    obtain ⟨x, hx⟩ := P.mkQ_surjective y
    refine ⟨(P.comap (N.comap P.mkQ).subtype).mkQ ⟨x, ?_⟩, ?_⟩
    · change P.mkQ x ∈ N
      rw [hx]
      exact y.property
    · exact Subtype.ext hx

omit [NumberField K] in
lemma quotientPreimageEquiv_comp (P : Submodule (𝓞 K) M)
    (N : Submodule (𝓞 K) (M ⧸ P)) :
    N.subtype.comp (quotientPreimageEquiv P N).toLinearMap =
      submoduleQuotientMap P (N.comap P.mkQ) := rfl

omit [NumberField K] in
lemma le_quotient_preimage (P : Submodule (𝓞 K) M)
    (N : Submodule (𝓞 K) (M ⧸ P)) : P ≤ N.comap P.mkQ := by
  intro x hx
  change P.mkQ x ∈ N
  rw [show P.mkQ x = 0 from (Submodule.Quotient.mk_eq_zero P).mpr hx]
  exact N.zero_mem

namespace HermitianMetric

variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]

omit [Module.Projective (𝓞 K) M] in
/-- The canonical quotient/preimage identification preserves the actual fiber forms. -/
lemma quotientPreimageEquiv_inner (h : HermitianMetric (K := K) M)
    (P : Submodule (𝓞 K) M) (N : Submodule (𝓞 K) (M ⧸ P)) (σ : K →+* ℂ)
    (x y : ComplexFiber ((N.comap P.mkQ) ⧸ P.comap (N.comap P.mkQ).subtype) σ) :
    (((h.quotient P).submodule N).fiber σ).inner
      (fiberMap (quotientPreimageEquiv P N).toLinearMap σ x)
      (fiberMap (quotientPreimageEquiv P N).toLinearMap σ y) =
    (((h.submodule (N.comap P.mkQ)).quotient
      (P.comap (N.comap P.mkQ).subtype)).fiber σ).inner x y := by
  rw [h.quotient_submodule (le_quotient_preimage P N)]
  change ((h.quotient P).fiber σ).inner
      ((fiberMap N.subtype σ).comp (fiberMap (quotientPreimageEquiv P N).toLinearMap σ) x)
      ((fiberMap N.subtype σ).comp (fiberMap (quotientPreimageEquiv P N).toLinearMap σ) y) = _
  rw [← fiberMap_comp, quotientPreimageEquiv_comp]
  rfl

/-- Induced degree on a quotient submodule is the degree difference of its preimage. -/
theorem degree_quotient_submodule (h : HermitianMetric (K := K) M)
    (P : Submodule (𝓞 K) M) [Module.Projective (𝓞 K) (M ⧸ P)]
    (N : Submodule (𝓞 K) (M ⧸ P)) :
    ((h.quotient P).submodule N).degree =
      (h.submodule (N.comap P.mkQ)).degree - (h.submodule P).degree := by
  let T := N.comap P.mkQ
  let e := quotientPreimageEquiv P N
  let : Module.Projective (𝓞 K) (T ⧸ P.comap T.subtype) :=
    Module.Projective.of_equiv e.symm
  have he := degree_eq_of_equiv ((h.submodule T).quotient (P.comap T.subtype))
    ((h.quotient P).submodule N) e (h.quotientPreimageEquiv_inner P N)
  have hd := (h.submodule T).degree_exact (Submodule.inclusion (le_quotient_preimage P N))
    (P.comap T.subtype).mkQ (exact_inclusion_quotient (le_quotient_preimage P N))
    (Submodule.inclusion_injective _) (P.comap T.subtype).mkQ_surjective
  rw [pullback_submodule_inclusion] at hd
  change (h.submodule T).degree = (h.submodule P).degree +
    ((h.submodule T).quotient (P.comap T.subtype)).degree at hd
  linarith

omit [Module.Projective (𝓞 K) M] in
/-- Generic rank on a quotient submodule is the rank difference of its preimage. -/
lemma finrank_quotient_submodule (P : Submodule (𝓞 K) M)
    [Module.Projective (𝓞 K) (M ⧸ P)] (N : Submodule (𝓞 K) (M ⧸ P)) :
    Module.finrank K (K ⊗[𝓞 K] N) =
      Module.finrank K (K ⊗[𝓞 K] (N.comap P.mkQ)) -
        Module.finrank K (K ⊗[𝓞 K] P) := by
  let T := N.comap P.mkQ
  let e := quotientPreimageEquiv P N
  let : Module.Projective (𝓞 K) (T ⧸ P.comap T.subtype) :=
    Module.Projective.of_equiv e.symm
  have hr := generic_finrank_exact (Submodule.inclusion (le_quotient_preimage P N))
    (P.comap T.subtype).mkQ (exact_inclusion_quotient (le_quotient_preimage P N))
    (Submodule.inclusion_injective _) (P.comap T.subtype).mkQ_surjective
  rw [(e.baseChange (𝓞 K) K _ _).finrank_eq] at hr
  omega

end HermitianMetric
end BostConjecture.Arithmetic
