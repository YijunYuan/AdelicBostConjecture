/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import AdelicBostConjecture.Adelic.Semistability.ActionSpan
public import AdelicBostConjecture.Arithmetic.Specht.Representation
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Absolute irreducibility of the integral Specht action

The actual orbit lattice, after scalar extension to any characteristic-zero
field, is irreducible. We use the already proved complex Specht theorem and
descend its full endomorphism action span to the rational form. Extension of
that rational span proves the result over every characteristic-zero field.
No embedding of the target field into the complex numbers is required.
-/

@[expose] public section

noncomputable section

open Module TensorProduct

namespace AdelicBostConjecture.Arithmetic

section Tower

variable {R A B G M : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
  [Monoid G] [AddCommGroup M] [Module R M]

/-- Iterated scalar extension intertwines through the canonical cancellation map. -/
def representationBaseChangeTowerEquiv (ρ : Representation R G M) :
    (representationBaseChange B (representationBaseChange A ρ)).Equiv
      (representationBaseChange B ρ) :=
  Representation.Equiv.mk (AlgebraTensorModule.cancelBaseChange R A B B M) (by
    intro g
    apply LinearMap.ext
    intro z
    change AlgebraTensorModule.cancelBaseChange R A B B M
      (((ρ g).baseChange A).baseChange B z) =
        (ρ g).baseChange B (AlgebraTensorModule.cancelBaseChange R A B B M z)
    rw [LinearMap.baseChange_baseChange]
    simp)

end Tower

namespace Specht

open AdelicBostConjecture.Specht

variable {n : ℕ} {μ : YoungDiagram}

/-- The integral lattice is nonzero, witnessed by its polytabloid. -/
instance orbitLattice_nontrivial (t : OAI.Saxl.Tableau n μ) : Nontrivial (orbitLattice t) :=
  ⟨⟨⟨polytabloidInt t, polytabloidInt_mem_orbitLattice t⟩, 0,
    fun h => polytabloidInt_ne_zero t (congrArg Subtype.val h)⟩⟩

/-- Extension of the free integral orbit lattice remains nonzero. -/
instance orbitLattice_baseChange_nontrivial (K : Type*) [Field K]
    (t : OAI.Saxl.Tableau n μ) : Nontrivial (K ⊗[ℤ] orbitLattice t) := by
  let b := (Module.Free.chooseBasis ℤ (orbitLattice t)).baseChange K
  exact b.repr.symm.injective.nontrivial

/-- The existing complexification is an equivalence of representations. -/
def integralRepresentationComplexEquiv (t : OAI.Saxl.Tableau n μ) :
    (representationBaseChange ℂ (integralRepresentation t)).Equiv (OAI.Saxl.spechtRep t) :=
  Representation.Equiv.mk (complexSpechtEquiv t) (by
    intro g
    apply LinearMap.ext
    intro x
    exact complexSpechtEquiv_equivariant t g x)

/-- The rational Specht action already spans every rational endomorphism. -/
theorem span_rationalRepresentation_eq_top (t : OAI.Saxl.Tableau n μ) :
    Submodule.span ℚ (Set.range (representationBaseChange ℚ (integralRepresentation t))) = ⊤ := by
  let := OAI.Saxl.specht_irreducible t
  let : Representation.IsIrreducible (representationBaseChange ℂ (integralRepresentation t)) :=
    isIrreducible_of_equiv (integralRepresentationComplexEquiv t)
  let : Representation.IsIrreducible
      (representationBaseChange ℂ (representationBaseChange ℚ (integralRepresentation t))) :=
    isIrreducible_of_equiv (representationBaseChangeTowerEquiv (A := ℚ) (integralRepresentation t))
  exact (span_representationBaseChange_eq_top_iff ℂ _).mp (span_representation_eq_top _)

/-- The actual integral Specht lattice gives an irreducible representation over
every characteristic-zero field, hence an absolutely irreducible representation. -/
theorem integralRepresentation_baseChange_isIrreducible (K : Type*) [Field K] [CharZero K]
    (t : OAI.Saxl.Tableau n μ) :
    Representation.IsIrreducible (representationBaseChange K (integralRepresentation t)) := by
  let : Representation.IsIrreducible
      (representationBaseChange K (representationBaseChange ℚ (integralRepresentation t))) :=
    isIrreducible_of_span_eq_top _
      ((span_representationBaseChange_eq_top_iff K _).mpr (span_rationalRepresentation_eq_top t))
  exact isIrreducible_of_equiv
    (representationBaseChangeTowerEquiv (A := ℚ) (B := K) (integralRepresentation t)).symm

/-- This paper, Proposition 3.14. See [Bürgisser et al., Lemma 3.9][bgow] and [Kowalski, Theorem
2.7.24][kowalski].

Absolute irreducibility in the exact iterated scalar-extension form used
by the independent-product semistability criterion. -/
theorem integralRepresentation_baseChange_isAbsolutelyIrreducible
    (K L : Type*) [Field K] [CharZero K] [Field L] [Algebra K L]
    (t : OAI.Saxl.Tableau n μ) :
    Representation.IsIrreducible
      (representationBaseChange L (representationBaseChange K (integralRepresentation t))) := by
  let : CharZero L :=
    (RingHom.charZero_iff (FaithfulSMul.algebraMap_injective K L)).mp inferInstance
  let := integralRepresentation_baseChange_isIrreducible L t
  exact isIrreducible_of_equiv
    (representationBaseChangeTowerEquiv (A := K) (integralRepresentation t))

end Specht

end AdelicBostConjecture.Arithmetic
