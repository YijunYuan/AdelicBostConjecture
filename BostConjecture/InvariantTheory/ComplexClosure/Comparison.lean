/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.InvariantTheory.ComplexClosure.ConstructibleClosure

/-!
# Polynomial-image closure comparison over the complex numbers

The coordinate comparison is transported through the homeomorphism associated
to the given finite basis, using the canonical intrinsic polynomial closure.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.InvariantTheory

/-- Coordinate polynomial images have the same Euclidean and algebraic closures. -/
theorem closure_coordinate_polynomial_image_zeroLocus {σ τ : Type*} [Finite σ] [Finite τ]
    (I : Ideal (MvPolynomial σ ℂ)) (q : τ → MvPolynomial σ ℂ) :
    closure ((fun a : σ → ℂ => fun i => MvPolynomial.eval a (q i)) ''
      MvPolynomial.zeroLocus ℂ I) =
    MvPolynomial.zeroLocus ℂ (MvPolynomial.vanishingIdeal ℂ
      ((fun a : σ → ℂ => fun i => MvPolynomial.eval a (q i)) ''
        MvPolynomial.zeroLocus ℂ I)) := by
  obtain ⟨S, hS, he⟩ := exists_constructible_polynomial_image I q
  simpa only [he] using closure_constructible_eq_zeroLocus_vanishingIdeal hS

/-- The complex polynomial-image closure comparison used in Lemma 7.2. -/
theorem closure_polynomial_image_zeroLocus
    {σ τ E : Type*} [Finite σ] [Fintype τ]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (b : Module.Basis τ ℂ E) (I : Ideal (MvPolynomial σ ℂ))
    (q : τ → MvPolynomial σ ℂ) :
    closure ((fun a : σ → ℂ => ∑ i, MvPolynomial.eval a (q i) • b i) ''
      MvPolynomial.zeroLocus ℂ I) =
    polynomialZariskiClosure (K := ℂ)
      ((fun a : σ → ℂ => ∑ i, MvPolynomial.eval a (q i) • b i) ''
        MvPolynomial.zeroLocus ℂ I) := by
  classical
  let S := (fun a : σ → ℂ => ∑ i, MvPolynomial.eval a (q i) • b i) ''
    MvPolynomial.zeroLocus ℂ I
  let e : E ≃ₜ (τ → ℂ) := b.equivFunL.toHomeomorph
  have he : b.equivFun '' S =
      (fun a : σ → ℂ => fun i => MvPolynomial.eval a (q i)) '' MvPolynomial.zeroLocus ℂ I := by
    rw [Set.image_image]
    congr 1
    funext a
    rw [← b.equivFun_symm_apply, b.equivFun.apply_symm_apply]
  change closure S = polynomialZariskiClosure S
  rw [polynomialZariskiClosure_eq_preimage_zeroLocus b, he,
    ← closure_coordinate_polynomial_image_zeroLocus I q, ← he]
  change closure S = e ⁻¹' closure (e '' S)
  rw [e.preimage_closure, Set.preimage_image_eq _ e.injective]

end BostConjecture.InvariantTheory
