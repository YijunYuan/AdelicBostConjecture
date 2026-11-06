module

public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Annihilators and irreducible dual representations

Finite-dimensional annihilator duality restricts to actual subrepresentations
of a group representation and its contragredient dual.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Arithmetic

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- The annihilator of an invariant subspace is invariant under the dual action. -/
def representationAnnihilator {ρ : Representation k G V} (P : Subrepresentation ρ) :
    Subrepresentation ρ.dual where
  toSubmodule := P.toSubmodule.dualAnnihilator
  apply_mem_toSubmodule := by
    intro g f hf
    rw [Submodule.mem_dualAnnihilator] at hf ⊢
    intro x hx
    exact hf _ (P.apply_mem_toSubmodule g⁻¹ hx)

/-- The common kernel of a dual subrepresentation is invariant. -/
def representationCoannihilator {ρ : Representation k G V} (P : Subrepresentation ρ.dual) :
    Subrepresentation ρ where
  toSubmodule := P.toSubmodule.dualCoannihilator
  apply_mem_toSubmodule := by
    intro g x hx
    rw [Submodule.mem_dualCoannihilator] at hx ⊢
    intro f hf
    have hh := hx _ (P.apply_mem_toSubmodule g⁻¹ hf)
    change f (ρ (g⁻¹)⁻¹ x) = 0 at hh
    simpa only [inv_inv] using hh

/-- Finite-dimensional duality on invariant subspaces. -/
def representationAnnihilatorOrderIso (ρ : Representation k G V) [FiniteDimensional k V] :
    Subrepresentation ρ ≃o (Subrepresentation ρ.dual)ᵒᵈ where
  toFun := representationAnnihilator
  invFun := representationCoannihilator
  left_inv P := by
    apply Subrepresentation.toSubmodule_injective
    exact Subspace.dualAnnihilator_dualCoannihilator_eq (W := P.toSubmodule)
  right_inv P := by
    apply Subrepresentation.toSubmodule_injective
    exact Subspace.dualCoannihilator_dualAnnihilator_eq (W := P.toSubmodule)
  map_rel_iff' := by
    intro P Q
    exact Subspace.dualAnnihilator_le_dualAnnihilator_iff

/-- The contragredient of a finite-dimensional irreducible representation is irreducible. -/
theorem isIrreducible_dual (ρ : Representation k G V) [FiniteDimensional k V]
    [Representation.IsIrreducible ρ] : Representation.IsIrreducible ρ.dual := by
  have : IsSimpleOrder (Subrepresentation ρ.dual)ᵒᵈ :=
    (representationAnnihilatorOrderIso ρ).isSimpleOrder_iff.mp inferInstance
  exact isSimpleOrder_iff_isSimpleOrder_orderDual.mpr this

end BostConjecture.Arithmetic
