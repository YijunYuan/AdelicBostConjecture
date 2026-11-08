/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.InvariantTheory.Plucker.Coordinates
public import BostConjecture.InvariantTheory.SpecialLinear.Coordinates
public import BostConjecture.InvariantTheory.Polynomial.Basic
public import Mathlib.CategoryTheory.Category.Basic

/-!
# Coordinate pullback for the actual Plücker action

Polynomial coefficients lie in the determinant-one coordinate algebra. The
forward convention is evaluation at `(g,x)` equal to `p (ρ(g) x)`.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.InvariantTheory

open Module exteriorPower
open scoped TensorProduct

section MatrixPullback

variable {K A X τ : Type*} [Field K] [CommRing A] [Algebra K A]
  [AddCommGroup X] [Module K X] [Fintype τ] [DecidableEq τ]

/-- Specialize only the coefficients of an intrinsic polynomial. -/
def polynomialCoefficientEval (e : A →ₐ[K] K) :
    A ⊗[K] SymmetricAlgebra K (Dual K X) →ₐ[K] SymmetricAlgebra K (Dual K X) :=
  (Algebra.TensorProduct.lid K _).toAlgHom.comp
    (Algebra.TensorProduct.map e (AlgHom.id K _))

@[simp]
theorem polynomialCoefficientEval_tmul (e : A →ₐ[K] K) (a : A)
    (p : SymmetricAlgebra K (Dual K X)) :
    polynomialCoefficientEval e (a ⊗ₜ[K] p) = e a • p := by
  simp [polynomialCoefficientEval]

/-- Linear substitution with matrix entries in a coefficient algebra. -/
def matrixPolynomialPullback (b : Basis τ K X) (C : Matrix τ τ A) :
    SymmetricAlgebra K (Dual K X) →ₐ[K] A ⊗[K] SymmetricAlgebra K (Dual K X) :=
  SymmetricAlgebra.lift (b.dualBasis.constr K
    (fun i => ∑ j, C i j ⊗ₜ[K] SymmetricAlgebra.ι K _ (b.dualBasis j)))

@[simp]
theorem matrixPolynomialPullback_ι_dualBasis (b : Basis τ K X) (C : Matrix τ τ A)
    (i : τ) :
    matrixPolynomialPullback b C (SymmetricAlgebra.ι K _ (b.dualBasis i)) =
      ∑ j, C i j ⊗ₜ[K] SymmetricAlgebra.ι K _ (b.dualBasis j) := by
  simp only [matrixPolynomialPullback, SymmetricAlgebra.lift_ι_apply, Basis.constr_basis]

/-- Coefficient specialization recovers the intrinsic linear pullback. -/
theorem polynomialCoefficientEval_comp_matrixPolynomialPullback
    (b : Basis τ K X) (C : Matrix τ τ A) (e : A →ₐ[K] K) (f : X →ₗ[K] X)
    (hC : ∀ i j, e (C i j) = b.coord i (f (b j))) :
    (polynomialCoefficientEval e).comp (matrixPolynomialPullback b C) =
      polynomialPullback f := by
  apply SymmetricAlgebra.algHom_ext
  apply b.dualBasis.ext
  intro i
  change polynomialCoefficientEval e
    (matrixPolynomialPullback b C (SymmetricAlgebra.ι K _ (b.dualBasis i))) =
    polynomialPullback f (SymmetricAlgebra.ι K _ (b.dualBasis i))
  simp only [matrixPolynomialPullback_ι_dualBasis, map_sum, polynomialCoefficientEval_tmul,
    polynomialPullback_ι, ← map_smul]
  rw [← map_sum]
  congr 1
  apply b.ext
  intro j
  simp [hC, Basis.coord_apply, Finsupp.single_apply]

end MatrixPullback

section PluckerPullback

variable {K U W ι κ : Type*} [Field K]
  [AddCommGroup U] [Module K U] [AddCommGroup W] [Module K W]
  [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Coordinates of an intrinsic determinant-one automorphism in a supplied basis. -/
def specialLinearMatrix (b : Basis ι K U) (g : SpecialLinearGroup K U) :
    Matrix.SpecialLinearGroup ι K :=
  (Matrix.SpecialLinearGroup.toLin_equiv b).symm g

/-- Coordinate-algebra evaluation at the existing intrinsic group element. -/
def pluckerGroupEval (bU : Basis ι K U) (bW : Basis κ K W)
    (g : SpecialLinearGroup K U × SpecialLinearGroup K W) :
    SpecialLinearPairCoordinateRing K ι κ →ₐ[K] K :=
  specialLinearPairEval (specialLinearMatrix bU g.1, specialLinearMatrix bW g.2)

@[simp]
theorem pluckerGroupEval_mk (bU : Basis ι K U) (bW : Basis κ K W)
    (g : SpecialLinearGroup K U × SpecialLinearGroup K W)
    (p : MvPolynomial ((ι × ι) ⊕ (κ × κ)) K) :
    pluckerGroupEval bU bW g (Ideal.Quotient.mkₐ K (specialLinearPairIdeal K ι κ) p) =
      MvPolynomial.aeval
        (matrixPairEntries bU bW (g.1 : U →ₗ[K] U) (g.2 : W →ₗ[K] W)) p := by
  unfold pluckerGroupEval
  rw [specialLinearPairEval_mk]
  congr 2
  funext i
  cases i <;> simp [specialLinearMatrix,
    Matrix.SpecialLinearGroup.toLin_equiv.symm_toLinearMap_eq,
    matrixPairEntries, LinearMap.toMatrix_apply,
    Basis.coord_apply]

variable [LinearOrder (ι × κ)]

/-- The pullback of intrinsic polynomials along the actual algebraic Plücker action. -/
def pluckerCoordinatePullback (bU : Basis ι K U) (bW : Basis κ K W) (s : ℕ) :
    SymmetricAlgebra K (Dual K (⋀[K]^s (U ⊗[K] W))) →ₐ[K]
      SpecialLinearPairCoordinateRing K ι κ ⊗[K]
        SymmetricAlgebra K (Dual K (⋀[K]^s (U ⊗[K] W))) :=
  matrixPolynomialPullback ((bU.tensorProduct bW).exteriorPower s)
    (fun I J => Ideal.Quotient.mkₐ K (specialLinearPairIdeal K ι κ)
      (pluckerMatrixPolynomial (K := K) s I J))

/-- Specialization of the coefficient ring is exactly forward pullback by the actual action. -/
theorem polynomialCoefficientEval_comp_pluckerCoordinatePullback
    (bU : Basis ι K U) (bW : Basis κ K W) (s : ℕ)
    (g : SpecialLinearGroup K U × SpecialLinearGroup K W) :
    (polynomialCoefficientEval (pluckerGroupEval bU bW g)).comp
      (pluckerCoordinatePullback bU bW s) =
        polynomialPullback (pluckerRepresentation K U W s g) := by
  apply polynomialCoefficientEval_comp_matrixPolynomialPullback
  intro I J
  rw [pluckerGroupEval_mk, aeval_pluckerMatrixPolynomial]
  rfl

@[simp]
theorem polynomialCoefficientEval_pluckerCoordinatePullback
    (bU : Basis ι K U) (bW : Basis κ K W) (s : ℕ)
    (g : SpecialLinearGroup K U × SpecialLinearGroup K W)
    (p : SymmetricAlgebra K (Dual K (⋀[K]^s (U ⊗[K] W)))) :
    polynomialCoefficientEval (pluckerGroupEval bU bW g) (pluckerCoordinatePullback bU bW s p) =
      polynomialPullback (pluckerRepresentation K U W s g) p :=
  DFunLike.congr_fun (polynomialCoefficientEval_comp_pluckerCoordinatePullback bU bW s g) p

end PluckerPullback

end BostConjecture.InvariantTheory
