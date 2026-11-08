/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Degree.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Differentiating arithmetic degree on a fixed integral module

The finite determinant quotient is constant along a metric curve. The actual
arithmetic derivative is therefore the negative embedding sum of logarithmic
derivatives of the determinant section norms. No freeness or integral basis
is used.

Reference: this paper, Proposition 7.3, page 13.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace BostConjecture.Arithmetic.HermitianMetric

variable {K : Type*} [Field K] [NumberField K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]
variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]

/-- Differentiating the actual section formula for degree; the finite
determinant quotient contributes no derivative. -/
theorem hasDerivAt_degree (h : ℝ → HermitianMetric K M)
    {ξ : DeterminantLine (K := K) M} (hξ : ξ ≠ 0) {t₀ : ℝ}
    (a : (K →+* ℂ) → ℝ)
    (ha : ∀ σ, HasDerivAt (fun t => (h t).determinant.sectionNorm σ ξ) (a σ) t₀) :
    HasDerivAt (fun t => (h t).degree)
      (-(∑ σ, a σ / (h t₀).determinant.sectionNorm σ ξ) /
        (Module.finrank ℚ K : ℝ)) t₀ := by
  have hs := HasDerivAt.sum fun σ (_ : σ ∈ (Finset.univ : Finset (K →+* ℂ))) =>
    (ha σ).log ((h t₀).determinant.sectionNorm_pos σ hξ).ne'
  convert (hs.const_sub (Real.log (Nat.card
    (DeterminantLine (K := K) M ⧸ (𝓞 K ∙ ξ))))).div_const
      (Module.finrank ℚ K : ℝ) using 1
  · funext t
    simpa only [Finset.sum_apply] using (h t).degree_eq hξ

/-- The squared-norm form of the arithmetic degree derivative. -/
theorem hasDerivAt_degree_of_norm_sq (h : ℝ → HermitianMetric K M)
    {ξ : DeterminantLine (K := K) M} (hξ : ξ ≠ 0) {t₀ : ℝ}
    (a : (K →+* ℂ) → ℝ)
    (ha : ∀ σ, HasDerivAt (fun t => ((h t).determinant.sectionNorm σ ξ) ^ 2)
      (a σ) t₀) :
    HasDerivAt (fun t => (h t).degree)
      (-(∑ σ, a σ / (2 * ((h t₀).determinant.sectionNorm σ ξ) ^ 2)) /
        (Module.finrank ℚ K : ℝ)) t₀ := by
  have hn (σ : K →+* ℂ) : 0 < (h t₀).determinant.sectionNorm σ ξ :=
    (h t₀).determinant.sectionNorm_pos σ hξ
  have hd (σ : K →+* ℂ) : HasDerivAt
      (fun t => (h t).determinant.sectionNorm σ ξ)
      (a σ / (2 * (h t₀).determinant.sectionNorm σ ξ)) t₀ := by
    simpa only [Real.sqrt_sq (le_of_lt ((h _).determinant.sectionNorm_pos σ hξ))] using
      (ha σ).sqrt (pow_ne_zero 2 (hn σ).ne')
  convert hasDerivAt_degree h hξ _ hd using 1
  congr 2
  apply Finset.sum_congr rfl
  intro σ _
  rw [div_div, pow_two, mul_assoc]

end BostConjecture.Arithmetic.HermitianMetric
