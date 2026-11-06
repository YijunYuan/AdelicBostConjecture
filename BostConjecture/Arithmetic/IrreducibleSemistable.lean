module

public import BostConjecture.Arithmetic.HNIsometry
public import Mathlib.RepresentationTheory.Irreducible

/-!
# Irreducible isometric actions imply intrinsic semistability

The action is a Mathlib representation on the actual integral module. Its
generic representation is obtained by the canonical endomorphism base-change
homomorphism. Irreducibility forces the invariant first HN term to be the whole
bundle. No finiteness hypothesis on the acting group is needed for this step.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace BostConjecture.Arithmetic

variable {K : Type*} [Field K] [NumberField K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]
variable {G : Type*} [Group G]

/-- The canonical generic scalar extension of an integral representation. -/
def genericRepresentation (ρ : Representation (𝓞 K) G M) :
    Representation K G (K ⊗[𝓞 K] M) :=
  (Module.End.baseChangeHom (𝓞 K) K M).toMonoidHom.comp ρ

namespace HermitianMetric

variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
variable [Nontrivial (K ⊗[𝓞 K] M)]

/-- An irreducible generic representation acting by actual integral isometries is semistable. -/
theorem isSemistable_of_irreducible (h : HermitianMetric (K := K) M)
    (ρ : Representation (𝓞 K) G M) [Representation.IsIrreducible (genericRepresentation ρ)]
    (hρ : ∀ (g : G) (σ : K →+* ℂ) (x y : ComplexFiber M σ),
      (h.fiber σ).inner (fiberMap (ρ g) σ x) (fiberMap (ρ g) σ y) =
        (h.fiber σ).inner x y) : h.IsSemistable := by
  have hinv (g : G) : (h.hnFlag 1).map (genericRepresentation ρ g) = h.hnFlag 1 := by
    let e : M ≃ₗ[𝓞 K] M :=
      { ρ g with
        invFun := ρ g⁻¹
        left_inv := fun x => by
          change (ρ g⁻¹ * ρ g) x = x
          rw [← map_mul, inv_mul_cancel, map_one]
          rfl
        right_inv := fun x => by
          change (ρ g * ρ g⁻¹) x = x
          rw [← map_mul, mul_inv_cancel, map_one]
          rfl }
    exact h.hnFlag_map_equiv e (hρ g) 1
  let W : Subrepresentation (genericRepresentation ρ) :=
    { toSubmodule := h.hnFlag 1
      apply_mem_toSubmodule := by
        intro g x hx
        rw [← hinv g]
        exact ⟨x, hx, rfl⟩ }
  rcases eq_bot_or_eq_top W with hW | hW
  · have hz : h.hnFlag 1 = ⊥ := congrArg Subrepresentation.toSubmodule hW
    have hr := h.hnSubmodule_one_rank_pos
    rw [hnSubmodule, hz, integralPart_bot] at hr
    simp at hr
  · have hz : h.hnFlag 1 = ⊤ := congrArg Subrepresentation.toSubmodule hW
    apply h.isSemistable_iff_maxSlope_eq.mpr
    exact (congrArg (fun P : Submodule (𝓞 K) M => (h.submodule P).slope)
      (congrArg integralPart hz)).trans h.slope_submodule_top

end HermitianMetric
end BostConjecture.Arithmetic
