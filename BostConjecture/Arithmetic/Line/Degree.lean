/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.NumberTheory.NumberField.FractionalIdeal
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.Ring

/-!
# Section independence of arithmetic line degree

For a nonzero fractional ideal `I` and positive fiber lengths `ρ`, the generic
coordinate formula is `(-log N(I) - ∑ v, v.mult * log (ρ v)) / [K : ℚ]`.
Changing a generic section multiplies its coefficient ideal by `(a⁻¹)` and
its fiber lengths by `|a|ᵥ`. `lineDegree_changeSection` proves that these changes
cancel, using the actual fractional-ideal norm and the number-field product
formula. No principal-ideal hypothesis on `I` is used.

Reference: this paper, §2, page 3.
-/

@[expose] public section

noncomputable section

open NumberField
open scoped nonZeroDivisors

namespace BostConjecture.Arithmetic

variable {K : Type*} [Field K] [NumberField K]

/-- The weighted sum of logarithms over the archimedean places. -/
def archLog (ρ : InfinitePlace K → ℝ) : ℝ :=
  ∑ v, (v.mult : ℝ) * Real.log (ρ v)

/-- The logarithm of the absolute fractional-ideal norm. -/
def logIdealNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ :=
  Real.log (FractionalIdeal.absNorm I : ℝ)

lemma idealNorm_pos {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) :
    0 < (FractionalIdeal.absNorm I : ℝ) := by
  exact_mod_cast (lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg I)
    (Ne.symm (FractionalIdeal.absNorm_eq_zero_iff.not.mpr hI)))

lemma logIdealNorm_mul {I J : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0) :
    logIdealNorm (I * J) = logIdealNorm I + logIdealNorm J := by
  simp only [logIdealNorm, map_mul, Rat.cast_mul]
  exact Real.log_mul (ne_of_gt (idealNorm_pos hI)) (ne_of_gt (idealNorm_pos hJ))

/-- The logarithmic product formula in the normalization used by arithmetic degree. -/
theorem logIdealNorm_spanSingleton {a : K} (ha : a ≠ 0) :
    logIdealNorm (FractionalIdeal.spanSingleton (𝓞 K)⁰ a) = archLog (fun v => v a) := by
  rw [logIdealNorm, FractionalIdeal.absNorm_span_singleton,
    ← InfinitePlace.prod_eq_abs_norm]
  rw [Real.log_prod (fun v _ => pow_ne_zero _ (ne_of_gt (InfinitePlace.pos_iff.mpr ha)))]
  simp only [archLog, Real.log_pow]

lemma archLog_mul {ρ τ : InfinitePlace K → ℝ}
    (hρ : ∀ v, ρ v ≠ 0) (hτ : ∀ v, τ v ≠ 0) :
    archLog (fun v => ρ v * τ v) = archLog ρ + archLog τ := by
  simp only [archLog, Real.log_mul (hρ _) (hτ _), mul_add, Finset.sum_add_distrib]

lemma archLog_inv (ρ : InfinitePlace K → ℝ) :
    archLog (fun v => (ρ v)⁻¹) = -archLog ρ := by
  simp [archLog, Real.log_inv, Finset.sum_neg_distrib]

/-- Degree in a generic coordinate `Ie`, with `ρ v = ‖e‖ᵥ`.
The fractional ideal may be nonprincipal. -/
def lineDegree (I : FractionalIdeal (𝓞 K)⁰ K) (ρ : InfinitePlace K → ℝ) : ℝ :=
  (-logIdealNorm I - archLog ρ) / (Module.finrank ℚ K : ℝ)

/-- Changing the generic section from `e` to `a • e` leaves its degree unchanged. -/
theorem lineDegree_changeSection (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0)
    (ρ : InfinitePlace K → ℝ) (hρ : ∀ v, 0 < ρ v) {a : K} (ha : a ≠ 0) :
    lineDegree (FractionalIdeal.spanSingleton (𝓞 K)⁰ a⁻¹ * I)
      (fun v => v a * ρ v) = lineDegree I ρ := by
  have hp : FractionalIdeal.spanSingleton (𝓞 K)⁰ a⁻¹ ≠ 0 := by
    exact FractionalIdeal.spanSingleton_ne_zero_iff.mpr (inv_ne_zero ha)
  rw [lineDegree, lineDegree, logIdealNorm_mul hp hI,
    logIdealNorm_spanSingleton (inv_ne_zero ha),
    archLog_mul (fun v => ne_of_gt (InfinitePlace.pos_iff.mpr ha))
      (fun v => ne_of_gt (hρ v))]
  have hi : archLog (fun v : InfinitePlace K => v a⁻¹) = -archLog (fun v => v a) := by
    simpa only [map_inv₀] using archLog_inv (fun v : InfinitePlace K => v a)
  rw [hi]
  ring

/-- The expression using a nonzero section agrees with the generic-coordinate
formula. Identifying the norm ratio with the quotient cardinality is separate. -/
theorem lineDegree_eq_section (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0)
    (ρ : InfinitePlace K → ℝ) (hρ : ∀ v, 0 < ρ v) {x : K} (hx : x ≠ 0) :
    (Real.log ((FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 K)⁰ x) : ℝ) /
      (FractionalIdeal.absNorm I : ℝ)) - archLog (fun v => v x * ρ v)) /
      (Module.finrank ℚ K : ℝ) = lineDegree I ρ := by
  have hp : FractionalIdeal.spanSingleton (𝓞 K)⁰ x ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx
  rw [Real.log_div (ne_of_gt (idealNorm_pos hp)) (ne_of_gt (idealNorm_pos hI))]
  change (logIdealNorm (FractionalIdeal.spanSingleton (𝓞 K)⁰ x) - logIdealNorm I -
    archLog (fun v => v x * ρ v)) / _ = _
  rw [logIdealNorm_spanSingleton hx,
    archLog_mul (fun v => ne_of_gt (InfinitePlace.pos_iff.mpr hx))
      (fun v => ne_of_gt (hρ v)), lineDegree]
  ring

end BostConjecture.Arithmetic
