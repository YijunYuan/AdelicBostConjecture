module

public import BostConjecture.InvariantTheory.Coaction
public import BostConjecture.InvariantTheory.SpecialLinearDetection
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Detecting homogeneous invariants by the coordinate map

Rational-point detection of the coefficient ring identifies coefficientwise
fixed vectors with the existing invariant subspace of the actual representation.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.InvariantTheory

open Module exteriorPower
open scoped TensorProduct

section CoefficientDetection

variable {K A X τ : Type*} [Field K] [CommRing A] [Algebra K A]
  [AddCommGroup X] [Module K X]

/-- Extracting a tensor coefficient commutes with specializing its scalar algebra. -/
theorem polynomialCoefficientEval_coord [DecidableEq τ]
    (b : Basis τ K (SymmetricAlgebra K (Dual K X))) (e : A →ₐ[K] K)
    (z : A ⊗[K] SymmetricAlgebra K (Dual K X)) (i : τ) :
    e (TensorProduct.equivFinsuppOfBasisRight b z i) =
      b.coord i (polynomialCoefficientEval e z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a p =>
    simp [Basis.coord_apply, smul_eq_mul, mul_comm]
  | add z w hz hw => simp [hz, hw]

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  [Infinite K]

/-- Special-linear rational points detect tensor-valued polynomial coefficients. -/
theorem polynomialCoefficientEval_detects (i₀ : ι) (j₀ : κ)
    {z : SpecialLinearPairCoordinateRing K ι κ ⊗[K]
      SymmetricAlgebra K (Dual K X)}
    (hz : ∀ g : Matrix.SpecialLinearGroup ι K × Matrix.SpecialLinearGroup κ K,
      polynomialCoefficientEval (specialLinearPairEval g) z = 0) : z = 0 := by
  classical
  let b := Module.Free.chooseBasis K (SymmetricAlgebra K (Dual K X))
  apply (TensorProduct.equivFinsuppOfBasisRight b).injective
  ext i
  simp only [map_zero, Finsupp.zero_apply]
  apply specialLinearPairEval_detects K ι κ i₀ j₀
  intro g
  rw [polynomialCoefficientEval_coord, hz g, map_zero]

end CoefficientDetection

section PluckerInvariants

variable {K U W ι κ : Type*} [Field K] [Infinite K]
  [AddCommGroup U] [Module K U] [AddCommGroup W] [Module K W]
  [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  [LinearOrder (ι × κ)]

/-- Invariance under actual intrinsic special-linear elements is a coefficientwise identity. -/
theorem pluckerCoordinatePullback_eq_of_invariant
    (bU : Basis ι K U) (bW : Basis κ K W) (i₀ : ι) (j₀ : κ) (s : ℕ)
    (p : SymmetricAlgebra K (Dual K (⋀[K]^s (U ⊗[K] W))))
    (hp : ∀ g, polynomialPullback (pluckerRepresentation K U W s g) p = p) :
    pluckerCoordinatePullback bU bW s p =
      (1 : SpecialLinearPairCoordinateRing K ι κ) ⊗ₜ[K] p := by
  apply sub_eq_zero.mp
  apply polynomialCoefficientEval_detects i₀ j₀
  rintro ⟨g, h⟩
  let g' := (Matrix.SpecialLinearGroup.toLin_equiv bU g,
    Matrix.SpecialLinearGroup.toLin_equiv bW h)
  have he : specialLinearPairEval (g, h) = pluckerGroupEval bU bW g' := by
    simp [pluckerGroupEval, specialLinearMatrix, g']
  rw [he, map_sub, polynomialCoefficientEval_pluckerCoordinatePullback, hp]
  simp

/-- Rational-point invariants coincide with fixed vectors of the degree coordinate map. -/
theorem mem_homogeneousInvariants_iff_pluckerPolynomialCoaction_eq
    (bU : Basis ι K U) (bW : Basis κ K W) (i₀ : ι) (j₀ : κ) (s d : ℕ)
    (p : homogeneousPolynomials K (⋀[K]^s (U ⊗[K] W)) d) :
    (p : SymmetricAlgebra K (Dual K (⋀[K]^s (U ⊗[K] W)))) ∈
        homogeneousInvariants (pluckerRepresentation K U W s) d ↔
      pluckerPolynomialCoaction bU bW s d p =
        (1 : SpecialLinearPairCoordinateRing K ι κ) ⊗ₜ[K] p := by
  constructor
  · intro hp
    have h := pluckerCoordinatePullback_eq_of_invariant bU bW i₀ j₀ s p
      ((mem_homogeneousInvariants_iff _ _ _).mp hp).2
    apply (homogeneousPolynomials K (⋀[K]^s (U ⊗[K] W)) d).toBaseChange_injective
      (SpecialLinearPairCoordinateRing K ι κ)
    apply Subtype.ext
    exact (pluckerPolynomialCoaction_include bU bW s d p).trans (h.trans (by simp))
  · exact mem_homogeneousInvariants_of_pluckerPolynomialCoaction_eq bU bW s d p

/-- The linear equations expressing invariance in the actual coefficient algebra. -/
def pluckerInvariantConstraint (bU : Basis ι K U) (bW : Basis κ K W) (s d : ℕ) :
    homogeneousPolynomials K (⋀[K]^s (U ⊗[K] W)) d →ₗ[K]
      SpecialLinearPairCoordinateRing K ι κ ⊗[K]
        homogeneousPolynomials K (⋀[K]^s (U ⊗[K] W)) d :=
  pluckerPolynomialCoaction bU bW s d -
    TensorProduct.mk K (SpecialLinearPairCoordinateRing K ι κ) _ 1

/-- The kernel of the explicit coefficient equations is the canonical invariant submodule. -/
theorem ker_pluckerInvariantConstraint
    (bU : Basis ι K U) (bW : Basis κ K W) (i₀ : ι) (j₀ : κ) (s d : ℕ) :
    LinearMap.ker (pluckerInvariantConstraint bU bW s d) =
      (homogeneousPolynomialRepresentation (pluckerRepresentation K U W s) d).invariants := by
  ext p
  constructor
  · intro hp
    have he : pluckerPolynomialCoaction bU bW s d p = 1 ⊗ₜ[K] p := sub_eq_zero.mp hp
    have hi := (mem_homogeneousInvariants_iff_pluckerPolynomialCoaction_eq
      bU bW i₀ j₀ s d p).mpr he
    exact fun g => Subtype.ext (hi.2 g)
  · intro hp
    have hi : (p : SymmetricAlgebra K (Dual K (⋀[K]^s (U ⊗[K] W)))) ∈
        homogeneousInvariants (pluckerRepresentation K U W s) d :=
      ⟨p.property, fun g => congrArg Subtype.val (hp g)⟩
    exact sub_eq_zero.mpr ((mem_homogeneousInvariants_iff_pluckerPolynomialCoaction_eq
      bU bW i₀ j₀ s d p).mp hi)

end PluckerInvariants

end BostConjecture.InvariantTheory
