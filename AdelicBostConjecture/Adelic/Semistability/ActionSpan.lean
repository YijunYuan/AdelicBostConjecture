/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import AdelicBostConjecture.Arithmetic.Representation.BaseChange
public import AdelicBostConjecture.Arithmetic.Representation.Density
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Scalar extension of the span of an action

For finite-dimensional representations, the action spans all endomorphisms
after a field extension exactly when it does before extension. This permits
absolute irreducibility of integral Specht representations to be descended
from the complex representation to its rational form and then extended to
every characteristic-zero field.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace AdelicBostConjecture.Arithmetic

variable {K G E : Type*} [Field K] [Monoid G] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (L : Type*) [Field L] [Algebra K L]

local instance : Module.FinitePresentation K E := Module.finitePresentation_of_finite K E

/-- Scalar extension identifies the full endomorphism spaces in finite dimension. -/
def endBaseChangeEquiv :
    L ⊗[K] Module.End K E ≃ₗ[L] Module.End L (L ⊗[K] E) :=
  (Module.FinitePresentation.isBaseChange_map K E E L).equiv

@[simp] theorem endBaseChangeEquiv_tmul (a : L) (f : Module.End K E) :
    endBaseChangeEquiv (K := K) (E := E) L (a ⊗ₜ[K] f) = a • f.baseChange L :=
  (Module.FinitePresentation.isBaseChange_map K E E L).equiv_tmul a f

/-- The span of the scalar-extended action is the scalar extension of the
original span, through the canonical endomorphism equivalence. -/
theorem map_baseChange_span_representation (ρ : Representation K G E) :
    ((Submodule.span K (Set.range ρ)).baseChange L).map
        (endBaseChangeEquiv (K := K) (E := E) L).toLinearMap =
      Submodule.span L (Set.range (representationBaseChange L ρ)) := by
  rw [Submodule.baseChange_span, Submodule.map_span, Set.image_image, ← Set.range_comp]
  congr 1
  funext g
  simp [representationBaseChange]
  rfl

/-- This paper, proof of Proposition 3.14, equations (3.11)–(3.12).

Having full endomorphism span is unchanged by extension of fields. -/
theorem span_representationBaseChange_eq_top_iff (ρ : Representation K G E) :
    Submodule.span L (Set.range (representationBaseChange L ρ)) = ⊤ ↔
      Submodule.span K (Set.range ρ) = ⊤ := by
  rw [← map_baseChange_span_representation L ρ]
  constructor
  · intro h
    apply Submodule.baseChange_injective (A := L)
    apply Submodule.map_injective_of_injective
      (endBaseChangeEquiv (K := K) (E := E) L).injective
    simpa only [Submodule.baseChange_top, Submodule.map_top,
      LinearEquiv.range] using h
  · intro h
    simp [h]

end AdelicBostConjecture.Arithmetic
