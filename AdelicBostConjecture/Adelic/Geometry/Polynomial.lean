/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.InvariantTheory.Semistability
public import AdelicBostConjecture.InvariantTheory.Polynomial.HomogeneousComponents
public import AdelicBostConjecture.Geometry.Plucker.Polynomial

/-!
# Coordinate and intrinsic invariant polynomials

The coordinate definition of polynomial semistability in ArakelovGeometry agrees
with the intrinsic symmetric-algebra invariants used by the determinant pairing.
The comparison preserves the degree, the representation, and evaluation at the
original vector. No orbit-closure or numerical criterion is assumed.
-/

@[expose] public section

noncomputable section

namespace AdelicBostConjecture.Adelic.Geometry

open Module AdelicBostConjecture.InvariantTheory

variable {K G X ι : Type*} [Field K] [Infinite K] [Group G]
  [AddCommGroup X] [Module K X] [FiniteDimensional K X] [Finite ι]

/-- Coordinate semistability is exactly nonvanishing of a positive-degree
intrinsic homogeneous invariant for the same representation. -/
theorem isPolynomialSemistable_iff_exists_homogeneousInvariant
    (b : Basis ι K X) (ρ : Representation K G X) (x : X) :
    ArakelovGeometry.InvariantTheory.IsPolynomialSemistable b ρ x ↔
      ∃ (d : ℕ) (p : SymmetricAlgebra K (Dual K X)),
        0 < d ∧ p ∈ homogeneousInvariants ρ d ∧ polynomialEval x p ≠ 0 := by
  classical
  let e := SymmetricAlgebra.equivMvPolynomial b.dualBasis
  have heval (y : X) (p : SymmetricAlgebra K (Dual K X)) :
      polynomialEval y p = MvPolynomial.eval (b.repr y) (e p) := by
    simpa only [MvPolynomial.aeval_eq_eval, Basis.coord_apply] using
      polynomialEval_eq_aeval_equivMvPolynomial b y p
  constructor
  · rintro ⟨d, p, hd, hp, hi, hx⟩
    have hp' : p ∈ (homogeneousPolynomials K X d).map e.toLinearMap := by
      rwa [map_homogeneousPolynomials_equivMvPolynomial b d]
    obtain ⟨q, hq, hqp⟩ := hp'
    change e q = p at hqp
    refine ⟨d, q, hd, (mem_homogeneousInvariants_iff ρ d q).mpr ⟨hq, ?_⟩, ?_⟩
    · intro g
      apply AdelicBostConjecture.Geometry.polynomial_ext
      intro y
      rw [polynomialEval_pullback, heval, heval, hqp]
      exact hi g y
    · rwa [heval, hqp]
  · rintro ⟨d, p, hd, hp, hx⟩
    obtain ⟨hp, hi⟩ := (mem_homogeneousInvariants_iff ρ d p).mp hp
    refine ⟨d, e p, hd, ?_, ?_, ?_⟩
    · change e p ∈ MvPolynomial.homogeneousSubmodule ι K d
      rw [← map_homogeneousPolynomials_equivMvPolynomial b d]
      exact ⟨p, hp, rfl⟩
    · intro g y
      rw [← heval, ← heval, ← polynomialEval_pullback, hi]
    · rwa [← heval]

end AdelicBostConjecture.Adelic.Geometry
