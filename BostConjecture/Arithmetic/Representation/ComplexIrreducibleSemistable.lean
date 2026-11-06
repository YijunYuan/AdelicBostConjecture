/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Representation.IrreducibleSemistable
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# Irreducibility at one complex embedding implies semistability

The invariant first HN term extends to a nonzero subrepresentation in the
actual complex fiber. Irreducibility and rank comparison force it to be the
whole bundle.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace BostConjecture.Arithmetic

variable {K : Type*} [Field K] [NumberField K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]
variable {G : Type*} [Group G]

/-- The actual representation on the complex fiber at an embedding. -/
def complexRepresentation (ρ : Representation (𝓞 K) G M) (σ : K →+* ℂ) :
    Representation ℂ G (ComplexFiber M σ) :=
  let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  representationBaseChange ℂ ρ

namespace HermitianMetric

variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
variable [Nontrivial (K ⊗[𝓞 K] M)]

/-- Irreducibility at a single complex embedding suffices for intrinsic semistability. -/
theorem isSemistable_of_complex_irreducible (h : HermitianMetric (K := K) M)
    (ρ : Representation (𝓞 K) G M) (σ : K →+* ℂ)
    [Representation.IsIrreducible (complexRepresentation ρ σ)]
    (hρ : ∀ (g : G) (τ : K →+* ℂ) (x y : ComplexFiber M τ),
      (h.fiber τ).inner (fiberMap (ρ g) τ x) (fiberMap (ρ g) τ y) =
        (h.fiber τ).inner x y) : h.IsSemistable := by
  let : Algebra K ℂ := σ.toAlgebra
  let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  let : IsScalarTower (𝓞 K) K ℂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Module.Flat (𝓞 K) ℂ := Module.Flat.trans (𝓞 K) K ℂ
  let : Representation.IsIrreducible (representationBaseChange ℂ ρ) :=
    inferInstanceAs (Representation.IsIrreducible (complexRepresentation ρ σ))
  let P : Subrepresentation ρ :=
    { toSubmodule := h.hnSubmodule 1
      apply_mem_toSubmodule := by
        intro g x hx
        let e := LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom g)
        have hi := h.hnSubmodule_map_equiv e (hρ g) 1
        rw [← hi]
        exact ⟨x, hx, rfl⟩ }
  let W := subrepresentationBaseChange ℂ P
  have hdim : Module.finrank ℂ W.toSubmodule = Module.finrank K (h.hnFlag 1) := by
    change Module.finrank ℂ ((h.hnSubmodule 1).baseChange ℂ) = _
    rw [← (Submodule.toBaseChange.toLinearEquiv ℂ (h.hnSubmodule 1)).finrank_eq]
    exact (complexFiber_finrank (M := h.hnSubmodule 1) σ).trans
      (integralPart_generic_finrank (h.hnFlag 1))
  rcases eq_bot_or_eq_top W with hW | hW
  · have he := congrArg Subrepresentation.toSubmodule hW
    change W.toSubmodule = (⊥ : Submodule ℂ (ComplexFiber M σ)) at he
    rw [he] at hdim
    have hp := h.hnSubmodule_one_rank_pos
    rw [hnSubmodule, integralPart_generic_finrank, ← hdim] at hp
    simp at hp
  · have he := congrArg Subrepresentation.toSubmodule hW
    change W.toSubmodule = (⊤ : Submodule ℂ (ComplexFiber M σ)) at he
    have hfirst : h.hnFlag 1 = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [← hdim, he]
      simpa using complexFiber_finrank (M := M) σ
    apply h.isSemistable_iff_maxSlope_eq.mpr
    exact (congrArg (fun P : Submodule (𝓞 K) M => (h.submodule P).slope)
      (congrArg integralPart hfirst)).trans h.slope_submodule_top

end HermitianMetric
end BostConjecture.Arithmetic
