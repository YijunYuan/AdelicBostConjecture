/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Detection by points in a principal affine open

Over an infinite field, evaluating at the points where a nonzero polynomial
does not vanish detects elements of the corresponding localized polynomial ring.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.InvariantTheory

variable {K σ : Type*} [Field K]

/-- Evaluation extends to the principal open on which the denominator is nonzero. -/
def localizationPolynomialEval (D : MvPolynomial σ K) (x : σ → K)
    (hx : MvPolynomial.aeval x D ≠ 0) : Localization.Away D →ₐ[K] K :=
  IsLocalization.Away.liftAlgHom D (isUnit_iff_ne_zero.mpr hx)

@[simp]
theorem localizationPolynomialEval_algebraMap (D : MvPolynomial σ K) (x : σ → K)
    (hx : MvPolynomial.aeval x D ≠ 0) (p : MvPolynomial σ K) :
    localizationPolynomialEval D x hx (algebraMap _ (Localization.Away D) p) =
      MvPolynomial.aeval x p :=
  IsLocalization.Away.lift_eq D (isUnit_iff_ne_zero.mpr hx) p

/-- An infinite-field polynomial vanishing on a nonempty principal open is zero. -/
theorem polynomial_eq_zero_of_eval_on_principalOpen [Infinite K]
    {D p : MvPolynomial σ K} (hD : D ≠ 0)
    (hp : ∀ x : σ → K, MvPolynomial.aeval x D ≠ 0 → MvPolynomial.aeval x p = 0) :
    p = 0 := by
  have hmul : p * D = 0 := by
    apply MvPolynomial.funext
    intro x
    change MvPolynomial.aeval x (p * D) = MvPolynomial.aeval x 0
    by_cases hx : MvPolynomial.aeval x D = 0
    · rw [map_mul, hx, mul_zero, map_zero]
    · rw [map_mul, hp x hx, zero_mul, map_zero]
  exact (mul_eq_zero.mp hmul).resolve_right hD

/-- Rational-point evaluation detects every element of a localized polynomial algebra. -/
theorem localizationPolynomialEval_detects [Infinite K]
    {D : MvPolynomial σ K} (hD : D ≠ 0) {z : Localization.Away D}
    (hz : ∀ (x : σ → K) (hx : MvPolynomial.aeval x D ≠ 0),
      localizationPolynomialEval D x hx z = 0) : z = 0 := by
  obtain ⟨n, p, hzp⟩ := IsLocalization.Away.surj D z
  have hp : p = 0 := polynomial_eq_zero_of_eval_on_principalOpen hD (by
    intro x hx
    have he := congrArg (localizationPolynomialEval D x hx) hzp
    simpa only [map_mul, hz x hx, zero_mul, localizationPolynomialEval_algebraMap] using he.symm)
  rw [hp, map_zero] at hzp
  obtain ⟨u, hu⟩ := IsLocalization.Away.algebraMap_pow_isUnit D n (S := Localization.Away D)
  rw [← hu] at hzp
  calc
    z = (z * (u : Localization.Away D)) * ↑u⁻¹ := by simp [mul_assoc]
    _ = 0 := by rw [hzp, zero_mul]

end BostConjecture.InvariantTheory
