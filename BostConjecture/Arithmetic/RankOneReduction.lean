module

public import BostConjecture.Arithmetic.IntegralSubspace
public import BostConjecture.Arithmetic.IntegralExactDeterminant

/-!
# Saturated rank-one reduction of a projective arithmetic module

The integral part of a generic line is a finite projective rank-one
submodule. Its actual quotient is finite projective, with rank one smaller.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace BostConjecture.Arithmetic

variable {K : Type*} [Field K] [NumberField K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]
    [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]

omit [Module.Projective (𝓞 K) M] in
/-- Generic rank is additive for an actual saturated submodule quotient. -/
lemma generic_finrank_submodule_quotient (P : Submodule (𝓞 K) M)
    [Module.Projective (𝓞 K) (M ⧸ P)] :
    Module.finrank K (K ⊗[𝓞 K] M) =
      Module.finrank K (K ⊗[𝓞 K] P) + Module.finrank K (K ⊗[𝓞 K] (M ⧸ P)) := by
  rw [(TensorProduct.isBaseChange (𝓞 K) M K).finrank_eq,
    (TensorProduct.isBaseChange (𝓞 K) P K).finrank_eq,
    (TensorProduct.isBaseChange (𝓞 K) (M ⧸ P) K).finrank_eq]
  exact exteriorPower.finrank_exact P.subtype P.mkQ (LinearMap.exact_subtype_mkQ P)
    P.injective_subtype P.mkQ_surjective

/-- Every positive-rank finite projective module has an actual saturated line
with finite projective quotient of rank one smaller. -/
theorem exists_rank_one_submodule (hr : 0 < Module.finrank K (K ⊗[𝓞 K] M)) :
    ∃ P : Submodule (𝓞 K) M, Module.Projective (𝓞 K) (M ⧸ P) ∧
      Module.finrank K (K ⊗[𝓞 K] P) = 1 ∧
      Module.finrank K (K ⊗[𝓞 K] M) = 1 + Module.finrank K (K ⊗[𝓞 K] (M ⧸ P)) := by
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hr
  let X := Submodule.span K ({v} : Set (K ⊗[𝓞 K] M))
  let P := integralPart X
  have hp : Module.finrank K (K ⊗[𝓞 K] P) = 1 := by
    rw [integralPart_generic_finrank]
    exact finrank_span_singleton hv
  refine ⟨P, inferInstance, hp, ?_⟩
  rw [generic_finrank_submodule_quotient P, hp]

end BostConjecture.Arithmetic
