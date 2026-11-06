module

public import BostConjecture.Arithmetic.Specht.Representation
public import BostConjecture.Geometry.ProjectivePermutation
public import BostConjecture.Geometry.IntrinsicContraction

/-!
# The determinant-twisted integral Specht action

The permutation group acts trivially on the actual determinant tensor power
and by its orbit-lattice action on the second factor. After complex scalar
extension, determinant coordinates identify this representation with the
accepted complex Specht representation.

Reference: `bost_specht_manuscript.pdf`, Lemma 6.1, pages 8–9.
-/

@[expose] public section

noncomputable section

open Module TensorProduct

namespace BostConjecture.Arithmetic.Specht

open BostConjecture.Specht

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  {n a k : ℕ}

local instance (t : OAI.Saxl.Tableau n (rectangle a k)) :
    AddCommGroup ((⨂[R] (_ : Fin k), ⋀[R]^a M) ⊗[R] (R ⊗[ℤ] orbitLattice t)) :=
  Module.addCommMonoidToAddCommGroup R

/-- The position action on GEOM's actual determinant-twisted module. -/
def determinantRepresentation (t : OAI.Saxl.Tableau n (rectangle a k)) :
    Representation R (Equiv.Perm (Fin n))
      ((⨂[R] (_ : Fin k), ⋀[R]^a M) ⊗[R] (R ⊗[ℤ] orbitLattice t)) :=
  Representation.tprod
    (Representation.trivial R (Equiv.Perm (Fin n)) (⨂[R] (_ : Fin k), ⋀[R]^a M))
    (representationBaseChange R (integralRepresentation t))

@[simp]
theorem determinantRepresentation_apply (t : OAI.Saxl.Tableau n (rectangle a k))
    (g : Equiv.Perm (Fin n)) :
    determinantRepresentation (R := R) (M := M) t g =
      TensorProduct.map LinearMap.id ((orbitAction t g).baseChange R) := rfl

/-- The actual projective determinant inclusion intertwines position permutations. -/
theorem projectiveDeterminantMap_equivariant [Module.Finite R M] [Module.Projective R M]
    (hk : 0 < k) (t : OAI.Saxl.Tableau n (rectangle a k))
    (ha : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = a)
    (g : Equiv.Perm (Fin n))
    (z : (⨂[R] (_ : Fin k), ⋀[R]^a M) ⊗[R] (R ⊗[ℤ] orbitLattice t)) :
    Geometry.projectiveDeterminantMap hk t ha (determinantRepresentation t g z) =
      PiTensorProduct.reindex R (fun _ : Fin n => M) g
        (Geometry.projectiveDeterminantMap hk t ha z) :=
  Geometry.projectiveDeterminantMap_reindex hk t ha g z

variable [Algebra R ℂ]

/-- Determinant coordinates retain the one-dimensional determinant factor before
identifying the complex fiber with the accepted Specht space. -/
def determinantSpechtEquiv (t : OAI.Saxl.Tableau n (rectangle a k))
    (b : Basis (Fin a) ℂ (ℂ ⊗[R] M)) :
    ℂ ⊗[R] ((⨂[R] (_ : Fin k), ⋀[R]^a M) ⊗[R] (R ⊗[ℤ] orbitLattice t)) ≃ₗ[ℂ]
      OAI.Saxl.Specht t :=
  (Geometry.determinantTwistBaseChangeEquiv (orbitLattice t) k a).trans
    ((TensorProduct.congr (Geometry.determinantPowerCoordinates k b)
      (LinearEquiv.refl ℂ (ℂ ⊗[ℤ] orbitLattice t))).trans
        ((TensorProduct.lid ℂ _).trans (complexSpechtEquiv t)))

@[simp]
theorem determinantSpechtEquiv_tmul (t : OAI.Saxl.Tableau n (rectangle a k))
    (b : Basis (Fin a) ℂ (ℂ ⊗[R] M)) (z : ℂ)
    (η : ⨂[R] (_ : Fin k), ⋀[R]^a M) (x : orbitLattice t) :
    determinantSpechtEquiv t b (z ⊗ₜ[R] (η ⊗ₜ[R] (1 ⊗ₜ[ℤ] x))) =
      z • (Geometry.determinantPowerCoordinates k b
        (Geometry.determinantPowerScalarExtension k a η) • complexSpechtEquiv t (1 ⊗ₜ[ℤ] x)) := by
  simp [determinantSpechtEquiv]

/-- The determinant factor has trivial permutation action, so the full actual
complex determinant-twisted module is equivariantly a Specht representation. -/
def determinantRepresentationEquiv (t : OAI.Saxl.Tableau n (rectangle a k))
    (b : Basis (Fin a) ℂ (ℂ ⊗[R] M)) :
    (representationBaseChange ℂ (determinantRepresentation (R := R) (M := M) t)).Equiv
      (OAI.Saxl.spechtRep t) :=
  Representation.Equiv.mk (determinantSpechtEquiv t b) (by
    intro g
    apply TensorProduct.AlgebraTensorModule.ext
    intro z u
    induction u using TensorProduct.inductionOn with
    | tmul η w =>
      induction w using TensorProduct.inductionOn with
      | tmul r x =>
        rw [TensorProduct.tmul_eq_smul_one_tmul r x,
          TensorProduct.tmul_smul, TensorProduct.tmul_smul]
        change determinantSpechtEquiv t b
          ((r • z) ⊗ₜ[R] (η ⊗ₜ[R] (1 ⊗ₜ[ℤ] orbitAction t g x))) =
            OAI.Saxl.spechtRep t g (determinantSpechtEquiv t b
              ((r • z) ⊗ₜ[R] (η ⊗ₜ[R] (1 ⊗ₜ[ℤ] x))))
        simp only [determinantSpechtEquiv_tmul, map_smul]
        rw [← complexSpechtEquiv_equivariant]
        rfl
      | add x y hx hy => simpa only [tmul_add, map_add] using congrArg₂ (· + ·) hx hy
    | add x y hx hy => simpa only [tmul_add, map_add] using congrArg₂ (· + ·) hx hy)

/-- Complex irreducibility of the actual determinant-twisted projective module. -/
theorem determinantRepresentation_irreducible (t : OAI.Saxl.Tableau n (rectangle a k))
    (b : Basis (Fin a) ℂ (ℂ ⊗[R] M)) :
    Representation.IsIrreducible
      (representationBaseChange ℂ (determinantRepresentation (R := R) (M := M) t)) := by
  let := OAI.Saxl.specht_irreducible t
  exact isIrreducible_of_equiv (determinantRepresentationEquiv t b)

/-- A finite projective module of constant rank supplies the complex frame;
no integral freeness or irreducibility hypothesis is needed. -/
theorem determinantRepresentation_irreducible_of_rankAtStalk
    [Module.Finite R M] [Module.Projective R M]
    (t : OAI.Saxl.Tableau n (rectangle a k))
    (ha : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = a) :
    Representation.IsIrreducible
      (representationBaseChange ℂ (determinantRepresentation (R := R) (M := M) t)) := by
  exact determinantRepresentation_irreducible t
    ((Module.finBasis ℂ (ℂ ⊗[R] M)).reindex
      (finCongr (Geometry.scalarExtension_finrank_of_rankAtStalk ha)))

end BostConjecture.Arithmetic.Specht
