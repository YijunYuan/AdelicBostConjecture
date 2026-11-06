/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Scalar extension of representations and invariant submodules

Both constructions use the canonical tensor scalar extension.
-/

@[expose] public section

noncomputable section

open TensorProduct

namespace BostConjecture.Arithmetic

variable {R G M : Type*} [CommRing R] [Monoid G] [AddCommGroup M] [Module R M]
variable (A : Type*) [CommRing A] [Algebra R A]

/-- Scalar extension of an action through the canonical endomorphism homomorphism. -/
def representationBaseChange (ρ : Representation R G M) :
    Representation A G (A ⊗[R] M) :=
  (Module.End.baseChangeHom R A M).toMonoidHom.comp ρ

/-- The actual scalar extension of an invariant submodule remains invariant. -/
def subrepresentationBaseChange {ρ : Representation R G M} (P : Subrepresentation ρ) :
    Subrepresentation (representationBaseChange A ρ) where
  toSubmodule := P.toSubmodule.baseChange A
  apply_mem_toSubmodule := by
    intro g x hx
    rw [Submodule.baseChange_eq_span] at hx ⊢
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      exact Submodule.subset_span ⟨ρ g y, P.apply_mem_toSubmodule g hy, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
    | smul a x _ hx => simpa only [map_smul] using Submodule.smul_mem _ a hx

section Equivalence

variable {k V W : Type*} [Field k] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W]

/-- Irreducibility transports along an actual intertwining equivalence. -/
theorem isIrreducible_of_equiv {ρ : Representation k G V} {τ : Representation k G W}
    (e : ρ.Equiv τ) [Representation.IsIrreducible τ] : Representation.IsIrreducible ρ := by
  apply (Representation.irreducible_iff_isSimpleModule_asModule ρ).mpr
  exact (LinearMap.isSimpleModule_iff_of_bijective
    (Representation.IntertwiningMap.equivLinearMapAsModule ρ τ e.toIntertwiningMap)
    e.toLinearEquiv.bijective).mpr inferInstance

end Equivalence

end BostConjecture.Arithmetic
