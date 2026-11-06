module

public import BostConjecture.Specht.Integral
public import BostConjecture.Arithmetic.RepresentationBaseChange
public import BostConjecture.Geometry.LatticeMetric

/-!
# The actual integral Specht representation

The action is the restriction of position permutations to the existing orbit
lattice. Its complexification is the accepted irreducible Specht representation,
and preserves the canonical word Gram form.

Reference: `bost_specht_manuscript.pdf`, §§3, 6, pages 4 and 9.
-/

@[expose] public section

noncomputable section

open TensorProduct

namespace BostConjecture.Arithmetic.Specht

open BostConjecture.Specht

variable {n : ℕ} {μ : YoungDiagram}

/-- The existing orbit-lattice action, with its representation laws. -/
def integralRepresentation (t : OAI.Saxl.Tableau n μ) :
    Representation ℤ (Equiv.Perm (Fin n)) (orbitLattice t) where
  toFun := orbitAction t
  map_one' := by ext x w; rfl
  map_mul' g h := by ext x w; rfl

/-- Equivariant identification with the accepted complex Specht representation. -/
def complexRepresentationEquiv (t : OAI.Saxl.Tableau n μ) :
    (representationBaseChange ℂ (integralRepresentation t)).Equiv (OAI.Saxl.spechtRep t) :=
  Representation.Equiv.mk (complexSpechtEquiv t) (by
    intro g
    apply LinearMap.ext
    intro x
    exact complexSpechtEquiv_equivariant t g x)

/-- The complexified integral orbit action is irreducible. -/
instance complexRepresentation_irreducible (t : OAI.Saxl.Tableau n μ) :
    Representation.IsIrreducible (representationBaseChange ℂ (integralRepresentation t)) := by
  let := OAI.Saxl.specht_irreducible t
  exact isIrreducible_of_equiv (complexRepresentationEquiv t)

/-- The complexification map intertwines the word-coordinate action. -/
theorem complexification_action (t : OAI.Saxl.Tableau n μ) (g : Equiv.Perm (Fin n))
    (x : ℂ ⊗[ℤ] orbitLattice t) :
    complexification t ((orbitAction t g).baseChange ℂ x) =
      OAI.Saxl.wordRep n (μ.colLen 0) g (complexification t x) := by
  exact congrArg Subtype.val (complexSpechtEquiv_equivariant t g x)

/-- Position permutations preserve the canonical complex lattice Gram form. -/
theorem latticeComplexCore_action_inner (t : OAI.Saxl.Tableau n μ)
    (g : Equiv.Perm (Fin n)) (x y : ℂ ⊗[ℤ] orbitLattice t) :
    (Geometry.latticeComplexCore t).inner
      ((orbitAction t g).baseChange ℂ x) ((orbitAction t g).baseChange ℂ y) =
        (Geometry.latticeComplexCore t).inner x y := by
  simp only [Geometry.latticeComplexCore_inner, complexification_action]
  exact (Equiv.arrowCongr g.symm (Equiv.refl (Fin (μ.colLen 0)))).sum_comp
    (fun w => star (complexification t x w) * complexification t y w)

variable (R : Type*) [CommRing R] [Algebra R ℂ]

/-- Scalar-extension cancellation intertwines the actual integral actions. -/
def scalarExtensionRepresentationEquiv (t : OAI.Saxl.Tableau n μ) :
    (representationBaseChange ℂ (representationBaseChange R (integralRepresentation t))).Equiv
      (representationBaseChange ℂ (integralRepresentation t)) :=
  Representation.Equiv.mk
    (AlgebraTensorModule.cancelBaseChange ℤ R ℂ ℂ (orbitLattice t)) (by
      intro g
      ext x
      rfl)

end BostConjecture.Arithmetic.Specht
