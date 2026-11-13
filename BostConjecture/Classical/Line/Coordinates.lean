/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.FractionalIdeal.Norm

/-!
# Coordinates and normalized degrees of arithmetic lines

Injective coordinates identify an integral line with a fractional ideal.
The product formula gives the coordinate-independent normalized line degree.
-/

@[expose] public section
noncomputable section

open NumberField
open scoped nonZeroDivisors Pointwise

namespace BostConjecture.Arithmetic

variable {K : Type*} [Field K] [NumberField K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M] [Module.Finite (𝓞 K) M]

/-- The actual fractional ideal of coordinates of the integral module. -/
def coordinateIdeal (f : M →ₗ[𝓞 K] K) : FractionalIdeal (𝓞 K)⁰ K :=
  ⟨f.range, FractionalIdeal.isFractional_of_fg (Submodule.fg_range f)⟩

/-- A coordinate scales the entire fractional ideal, not merely its generators. -/
lemma coordinateIdeal_smul (f : M →ₗ[𝓞 K] K) (a : K) :
    coordinateIdeal (a • f) = FractionalIdeal.spanSingleton (𝓞 K)⁰ a * coordinateIdeal f := by
  apply FractionalIdeal.coeToSubmodule_injective
  dsimp only
  change (a • f).range = _
  rw [FractionalIdeal.coe_mul, FractionalIdeal.coe_spanSingleton, Submodule.span_singleton_mul]
  ext x
  simp only [LinearMap.mem_range, LinearMap.smul_apply,
    Submodule.mem_smul_pointwise_iff_exists, coordinateIdeal, FractionalIdeal.coe_mk]
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨f m, ⟨m, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨m, rfl⟩, rfl⟩
    exact ⟨m, rfl⟩

lemma coordinateIdeal_ne_zero [Nontrivial M]
    (f : M →ₗ[𝓞 K] K) (hf : Function.Injective f) : coordinateIdeal f ≠ 0 := by
  intro heq
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  have hx' : f x ∈ coordinateIdeal f := ⟨x, rfl⟩
  rw [heq] at hx'
  have hzero : f x = 0 := by simpa only [FractionalIdeal.mem_zero_iff] using hx'
  exact hx (hf (by simpa using hzero))

omit [Module.Finite (𝓞 K) M] in
/-- Clear denominators in a line coordinate to compare two integral sections. -/
lemma exists_smul_eq_of_injective (f : M →ₗ[𝓞 K] K) (hf : Function.Injective f)
    {x : M} (hx : x ≠ 0) (y : M) :
    ∃ a b : 𝓞 K, b ≠ 0 ∧ a • x = b • y := by
  have hfx : f x ≠ 0 := fun h => hx (hf (by simpa using h))
  obtain ⟨a, b, hb, heq⟩ := IsFractionRing.div_surjective (𝓞 K) (f y / f x)
  have hb' : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : (algebraMap (𝓞 K) K b) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hb'
  refine ⟨a, b, hb', hf ?_⟩
  simp only [map_smul, Algebra.smul_def]
  simpa only [mul_comm] using (div_eq_div_iff hbK hfx).mp heq

omit [Module.Finite (𝓞 K) M] in
/-- Two coordinates of an integral line differ by the ratio on any nonzero
section. This assertion uses an injective coordinate, not freeness over integers. -/
lemma linearMap_eq_smul_of_injective (f g : M →ₗ[𝓞 K] K)
    (hf : Function.Injective f) {x : M} (hx : x ≠ 0) :
    g = (g x / f x) • f := by
  have hfx : f x ≠ 0 := fun h => hx (hf (by simpa using h))
  ext y
  obtain ⟨a, b, hb, hab⟩ := exists_smul_eq_of_injective f hf hx y
  have hbK : (b : K) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hb
  have h₁ := congrArg f hab
  have h₂ := congrArg g hab
  simp only [map_smul, Algebra.smul_def] at h₁ h₂
  change g y = (g x / f x) * f y
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hfx).mpr
  apply mul_left_cancel₀ hbK
  change (algebraMap (𝓞 K) K b) * (g y * f x) =
    (algebraMap (𝓞 K) K b) * (g x * f y)
  linear_combination (g x) * h₁ - (f x) * h₂

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
  have hp : FractionalIdeal.spanSingleton (𝓞 K)⁰ a⁻¹ ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr (inv_ne_zero ha)
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
