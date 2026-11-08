/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.InvariantTheory.Polynomial.Coaction

/-!
# Specialization of polynomial coefficients

Tensor coefficient extraction commutes with specializing the coefficient algebra.
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

end CoefficientDetection

end BostConjecture.InvariantTheory
