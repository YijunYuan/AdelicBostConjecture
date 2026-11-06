module

public import BostConjecture.InvariantTheory.Coaction
public import Mathlib.RingTheory.Nullstellensatz

/-!
# The actual Plücker orbit as a polynomial image

The determinant-one zero locus parametrizes precisely the actual intrinsic
special-linear pairs. The explicit orbit polynomials therefore have exactly
the intrinsic Plücker orbit as their image.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.InvariantTheory

open Module exteriorPower
open scoped TensorProduct

variable {K U W ι κ : Type*} [Field K]
  [AddCommGroup U] [Module K U] [AddCommGroup W] [Module K W]
  [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Every zero-locus tuple is the entry tuple of an actual intrinsic special-linear pair. -/
theorem mem_specialLinearPair_zeroLocus_iff
    (bU : Basis ι K U) (bW : Basis κ K W)
    (a : ((ι × ι) ⊕ (κ × κ)) → K) :
    a ∈ MvPolynomial.zeroLocus K (specialLinearPairIdeal K ι κ) ↔
      ∃ g : SpecialLinearGroup K U × SpecialLinearGroup K W,
        matrixPairEntries bU bW (g.1 : U →ₗ[K] U) (g.2 : W →ₗ[K] W) = a := by
  constructor
  · intro ha
    let e : SpecialLinearPairCoordinateRing K ι κ →ₐ[K] K :=
      Ideal.Quotient.liftₐ _ (MvPolynomial.aeval a) ha
    let g := specialLinearPairPoint e
    refine ⟨(Matrix.SpecialLinearGroup.toLin_equiv bU g.1,
      Matrix.SpecialLinearGroup.toLin_equiv bW g.2), ?_⟩
    funext i
    cases i with
    | inl ij =>
      change bU.coord ij.1 ((Matrix.SpecialLinearGroup.toLin_equiv bU g.1 : U →ₗ[K] U)
        (bU ij.2)) = a (Sum.inl ij)
      rw [Matrix.SpecialLinearGroup.toLin_equiv.toLinearMap_eq]
      simp [g, specialLinearPairPoint, e, Basis.coord_apply, Finsupp.single_apply]
      exact MvPolynomial.aeval_X (R := K) a (Sum.inl ij)
    | inr ij =>
      change bW.coord ij.1 ((Matrix.SpecialLinearGroup.toLin_equiv bW g.2 : W →ₗ[K] W)
        (bW ij.2)) = a (Sum.inr ij)
      rw [Matrix.SpecialLinearGroup.toLin_equiv.toLinearMap_eq]
      simp [g, specialLinearPairPoint, e, Basis.coord_apply, Finsupp.single_apply]
      exact MvPolynomial.aeval_X (R := K) a (Sum.inr ij)
  · rintro ⟨g, rfl⟩ p hp
    have h := specialLinearPairIdeal_le_ker
      (K := K) (specialLinearMatrix bU g.1, specialLinearMatrix bW g.2) hp
    change pluckerGroupEval bU bW g (Ideal.Quotient.mkₐ K (specialLinearPairIdeal K ι κ) p) = 0 at h
    rwa [pluckerGroupEval_mk] at h

variable [LinearOrder (ι × κ)]

/-- The explicit polynomial orbit map has exactly the actual intrinsic orbit as image. -/
theorem pluckerOrbit_polynomial_image
    (bU : Basis ι K U) (bW : Basis κ K W) (s : ℕ)
    (z : ⋀[K]^s (U ⊗[K] W)) :
    (fun a => ∑ I, MvPolynomial.eval a (pluckerOrbitPolynomial bU bW s z I) •
        ((bU.tensorProduct bW).exteriorPower s) I) ''
      MvPolynomial.zeroLocus K (specialLinearPairIdeal K ι κ) =
        Set.range (fun g => pluckerRepresentation K U W s g z) := by
  have he (g : SpecialLinearGroup K U × SpecialLinearGroup K W) :
      (∑ I, MvPolynomial.eval
        (matrixPairEntries bU bW (g.1 : U →ₗ[K] U) (g.2 : W →ₗ[K] W))
        (pluckerOrbitPolynomial bU bW s z I) •
          ((bU.tensorProduct bW).exteriorPower s) I) =
        pluckerRepresentation K U W s g z := by
    simp_rw [← MvPolynomial.aeval_eq_eval,
      aeval_pluckerOrbitPolynomial_specialLinear, Basis.coord_apply]
    exact
      ((bU.tensorProduct bW).exteriorPower s).sum_repr (pluckerRepresentation K U W s g z)
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨g, rfl⟩ := (mem_specialLinearPair_zeroLocus_iff bU bW a).mp ha
    exact ⟨g, (he g).symm⟩
  · rintro ⟨g, rfl⟩
    exact ⟨_, (mem_specialLinearPair_zeroLocus_iff bU bW _).mpr ⟨g, rfl⟩, he g⟩

end BostConjecture.InvariantTheory
