/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Line.Hermitian

/-!
# Contraction and intrinsic line degree

An injective integral map between Hermitian lines increases normalized degree
when it contracts every archimedean norm. The finite contribution is proved
using an injective map between the actual quotients by a nonzero section.
Neither freeness nor a degree-inequality assumption is used.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace BostConjecture.Arithmetic

/-- An injection induces an injection on the quotients by a section and its image. -/
lemma quotient_span_card_le {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (hf : Function.Injective f) (x : M)
    [Finite (N ⧸ (R ∙ f x))] :
    Nat.card (M ⧸ (R ∙ x)) ≤ Nat.card (N ⧸ (R ∙ f x)) := by
  have hp : (R ∙ x) = (R ∙ f x).comap f := by
    ext y
    simp only [Submodule.mem_comap, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, (f.map_smul a x).symm⟩
    · rintro ⟨a, ha⟩
      exact ⟨a, hf (by simpa only [map_smul] using ha)⟩
  let q := (R ∙ x).mapQ (R ∙ f x) f hp.le
  apply Nat.card_le_card_of_injective q
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.ker_mapQ, ← hp, Submodule.mkQ_map_self]

namespace HermitianMetric

variable {K : Type*} [Field K] [NumberField K]
variable {M N : Type*} [AddCommGroup M] [Module (𝓞 K) M]
variable [AddCommGroup N] [Module (𝓞 K) N]
variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M] [Nontrivial M]
variable [Module.Finite (𝓞 K) N] [Module.Projective (𝓞 K) N] [Nontrivial N]

/-- An injective contraction between intrinsic projective lines increases degree. -/
theorem lineDegree_le_of_injective (h : HermitianMetric K M)
    (g : HermitianMetric K N) (f : M →ₗ[𝓞 K] N) (hf : Function.Injective f)
    (hM : Module.finrank K (K ⊗[𝓞 K] M) = 1)
    (hN : Module.finrank K (K ⊗[𝓞 K] N) = 1)
    (hcontract : ∀ (σ : K →+* ℂ) (x : M), g.sectionNorm σ (f x) ≤ h.sectionNorm σ x) :
    h.lineDegree hM ≤ g.lineDegree hN := by
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  have hfx : f x ≠ 0 := fun heq => hx (hf (by simpa using heq))
  let := line_quotient_finite hM hx
  let := line_quotient_finite hN hfx
  rw [h.lineDegree_eq_sum_embeddings hM hx, g.lineDegree_eq_sum_embeddings hN hfx]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply sub_le_sub
  · apply Real.log_le_log
    · exact Nat.cast_pos.mpr Nat.card_pos
    · exact_mod_cast quotient_span_card_le f hf x
  · apply Finset.sum_le_sum
    intro σ _
    exact Real.log_le_log (g.sectionNorm_pos σ hfx) (hcontract σ x)

end HermitianMetric
end BostConjecture.Arithmetic
