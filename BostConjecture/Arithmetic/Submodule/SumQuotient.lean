/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Submodule.NestedQuotient

/-!
# The actual sum quotient of two integral submodules

The sum quotient embeds in the ambient quotient and is projective when
that ambient quotient is torsion-free. Both standard exact sequences are
expressed using Mathlib's canonical inclusion and second-isomorphism maps.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace BostConjecture.Arithmetic

variable {K : Type*} [Field K] [NumberField K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]

/-- Submodule quotients of a torsion-free ambient quotient are torsion-free. -/
instance submoduleQuotientTorsionFree (V T : Submodule (𝓞 K) M)
    [Module.IsTorsionFree (𝓞 K) (M ⧸ V)] :
    Module.IsTorsionFree (𝓞 K) (T ⧸ V.comap T.subtype) := by
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro a x hx
  by_cases ha : a = 0
  · exact Or.inl ha
  right
  apply submoduleQuotientMap_injective V T
  rw [map_zero]
  apply (smul_eq_zero.mp (show a • submoduleQuotientMap V T x = 0 from by
    rw [← map_smul, hx, map_zero])).resolve_left ha

/-- The intermediate quotient is finite projective over the ring of integers. -/
instance submoduleQuotientProjective [Module.Finite (𝓞 K) M]
    (V T : Submodule (𝓞 K) M) [Module.IsTorsionFree (𝓞 K) (M ⧸ V)] :
    Module.Projective (𝓞 K) (T ⧸ V.comap T.subtype) := by
  let : Module.FinitePresentation (𝓞 K) (T ⧸ V.comap T.subtype) :=
    Module.finitePresentation_of_finite (𝓞 K) _
  exact Module.Flat.projective_of_finitePresentation

omit [NumberField K] in
/-- The usual quotient map from the first summand onto the sum quotient is surjective. -/
lemma subToSupQuotient_surjective (U V : Submodule (𝓞 K) M) :
    Function.Surjective (LinearMap.subToSupQuotient U V) := by
  intro z
  obtain ⟨w, rfl⟩ := (LinearMap.quotientInfEquivSupQuotient U V).surjective z
  obtain ⟨x, rfl⟩ := (U.comap U.subtype ⊓ V.comap U.subtype).mkQ_surjective w
  exact ⟨x, rfl⟩

omit [NumberField K] in
/-- The intersection is exactly the kernel of the first sum-quotient map. -/
lemma exact_inf_subToSupQuotient (U V : Submodule (𝓞 K) M) :
    Function.Exact (Submodule.inclusion (inf_le_left : U ⊓ V ≤ U))
      (LinearMap.subToSupQuotient U V) := by
  intro x
  change (V.comap (U ⊔ V).subtype).mkQ (Submodule.inclusion le_sup_left x) = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · intro hx
    exact ⟨⟨x, x.property, hx⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    exact y.property.2

omit [NumberField K] in
/-- The second summand is exactly the kernel of the sum-quotient projection. -/
lemma exact_inclusion_quotient {V T : Submodule (𝓞 K) M} (hVT : V ≤ T) :
    Function.Exact (Submodule.inclusion hVT) (V.comap T.subtype).mkQ := by
  intro x
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    exact y.property

end BostConjecture.Arithmetic
