/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Line.Degree
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination

/-!
# Integral coefficient ideals of lines

The image of a finite integral module under a linear coordinate in the number
field is a fractional ideal. An injective coordinate identifies the module
with this ideal, without an integral basis or principal-ideal assumption.
These concrete ideals supply the finite part of the line-degree formula.
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

@[simp]
lemma mem_coordinateIdeal (f : M →ₗ[𝓞 K] K) (x : K) :
    x ∈ coordinateIdeal f ↔ ∃ m, f m = x := Iff.rfl

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

/-- An injective coordinate presents the integral module as its coefficient ideal. -/
def coordinateEquiv (f : M →ₗ[𝓞 K] K) (hf : Function.Injective f) :
    M ≃ₗ[𝓞 K] coordinateIdeal f :=
  LinearEquiv.ofInjective f hf

lemma coordinateIdeal_ne_zero [Nontrivial M]
    (f : M →ₗ[𝓞 K] K) (hf : Function.Injective f) : coordinateIdeal f ≠ 0 := by
  intro heq
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  have hx' : f x ∈ coordinateIdeal f := ⟨x, rfl⟩
  rw [heq] at hx'
  have hzero : f x = 0 := by simpa only [FractionalIdeal.mem_zero_iff] using hx'
  exact hx (hf (by simpa using hzero))

/-- Product-formula cancellation for the coefficient ideal of an actual integral
module under a change of generic coordinate. -/
theorem coordinateIdeal_degree_smul [Nontrivial M]
    (f : M →ₗ[𝓞 K] K) (hf : Function.Injective f)
    (ρ : InfinitePlace K → ℝ) (hρ : ∀ v, 0 < ρ v) {a : K} (ha : a ≠ 0) :
    lineDegree (coordinateIdeal (a⁻¹ • f)) (fun v => v a * ρ v) =
      lineDegree (coordinateIdeal f) ρ := by
  rw [coordinateIdeal_smul]
  exact lineDegree_changeSection _ (coordinateIdeal_ne_zero f hf) ρ hρ ha

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

end BostConjecture.Arithmetic
