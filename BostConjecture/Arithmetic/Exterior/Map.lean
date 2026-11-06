/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Degree.Normalization
public import BostConjecture.Arithmetic.Submodule.Metric

/-!
# Maps of intrinsic determinant lines

Exterior-power scalar extension is natural on actual integral sections.
This proves preservation of injections for finite projective integral
modules by comparison with their complex fibers.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct exteriorPower

namespace BostConjecture.Arithmetic

variable {K : Type*} [Field K]
variable {M N : Type*} [AddCommGroup M] [Module (𝓞 K) M]
    [AddCommGroup N] [Module (𝓞 K) N]

/-- Naturality of exterior scalar extension on integral sections. -/
lemma exteriorMap_section (f : M →ₗ[𝓞 K] N) (σ : K →+* ℂ) (r : ℕ)
    (x : ⋀[𝓞 K]^r M) :
    letI : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
    exteriorPower.baseChangeEquiv (𝓞 K) N ℂ r
        (fiberSection (⋀[𝓞 K]^r N) σ (map r f x)) =
      map r (fiberMap f σ)
        (exteriorPower.baseChangeEquiv (𝓞 K) M ℂ r
          (fiberSection (⋀[𝓞 K]^r M) σ x)) := by
  let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  have he :
      (((exteriorPower.baseChangeEquiv (𝓞 K) N ℂ r).toLinearMap.restrictScalars (𝓞 K)).comp
        (TensorProduct.mk (𝓞 K) ℂ (⋀[𝓞 K]^r N) 1)).comp (map r f) =
      ((map r (fiberMap f σ)).restrictScalars (𝓞 K)).comp
        (((exteriorPower.baseChangeEquiv (𝓞 K) M ℂ r).toLinearMap.restrictScalars (𝓞 K)).comp
          (TensorProduct.mk (𝓞 K) ℂ (⋀[𝓞 K]^r M) 1)) := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change exteriorPower.baseChangeEquiv (𝓞 K) N ℂ r
      (1 ⊗ₜ[𝓞 K] (map r f (ιMulti (𝓞 K) r v))) =
      map r (fiberMap f σ)
        (exteriorPower.baseChangeEquiv (𝓞 K) M ℂ r (1 ⊗ₜ[𝓞 K] ιMulti (𝓞 K) r v))
    rw [map_apply_ιMulti, exteriorPower.baseChangeEquiv_apply_tmul,
      exteriorPower.baseChangeEquiv_apply_tmul, map_apply_ιMulti]
    rfl
  exact LinearMap.congr_fun he x

variable [NumberField K] [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]

/-- Exterior powers preserve injections from finite projective integral modules. -/
lemma exteriorMap_injective (f : M →ₗ[𝓞 K] N) (hf : Function.Injective f) (r : ℕ) :
    Function.Injective (map r f) := by
  let σ : K →+* ℂ := Classical.choice inferInstance
  let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  intro x y hxy
  apply fiberSection_injective (⋀[𝓞 K]^r M) σ
  apply (exteriorPower.baseChangeEquiv (𝓞 K) M ℂ r).injective
  apply exteriorPower.map_injective_field (n := r) (fiberMap_injective f hf σ)
  rw [← exteriorMap_section f σ r x, ← exteriorMap_section f σ r y, hxy]

end BostConjecture.Arithmetic

namespace BostConjecture.Arithmetic

variable {K : Type*} [Field K]
variable {M N : Type*} [AddCommGroup M] [Module (𝓞 K) M]
    [AddCommGroup N] [Module (𝓞 K) N]

/-- The canonical map on determinant lines of equal-rank integral modules. -/
def determinantMap (f : M →ₗ[𝓞 K] N)
    (hr : Module.finrank K (K ⊗[𝓞 K] M) = Module.finrank K (K ⊗[𝓞 K] N)) :
    DeterminantLine (K := K) M →ₗ[𝓞 K] DeterminantLine (K := K) N :=
  (degreeCongr hr).toLinearMap.comp (map (Module.finrank K (K ⊗[𝓞 K] M)) f)

/-- Change of exterior degree commutes with the scalar-extension equivalence. -/
lemma exteriorDegreeCongr_section (σ : K →+* ℂ) {r s : ℕ} (hrs : r = s)
    (x : ⋀[𝓞 K]^r M) :
    letI : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
    exteriorPower.baseChangeEquiv (𝓞 K) M ℂ s
        (fiberSection (⋀[𝓞 K]^s M) σ (degreeCongr hrs x)) =
      degreeCongr hrs (exteriorPower.baseChangeEquiv (𝓞 K) M ℂ r
        (fiberSection (⋀[𝓞 K]^r M) σ x)) := by
  subst s
  rfl

/-- Naturality of the determinant fiber identification, including the rank transport. -/
lemma determinantMap_section (f : M →ₗ[𝓞 K] N)
    (hr : Module.finrank K (K ⊗[𝓞 K] M) = Module.finrank K (K ⊗[𝓞 K] N))
    (σ : K →+* ℂ) (x : DeterminantLine (K := K) M) :
    determinantComplexEquiv N σ (fiberSection _ σ (determinantMap f hr x)) =
      degreeCongr hr (map (Module.finrank K (K ⊗[𝓞 K] M)) (fiberMap f σ)
        (determinantComplexEquiv M σ (fiberSection _ σ x))) := by
  let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  change exteriorPower.baseChangeEquiv (𝓞 K) N ℂ _
    (fiberSection _ σ (degreeCongr hr (map _ f x))) = _
  rw [exteriorDegreeCongr_section, exteriorMap_section]
  rfl

/-- Naturality on all complex determinant vectors, extended from integral generators. -/
lemma determinantMap_fiber (f : M →ₗ[𝓞 K] N)
    (hr : Module.finrank K (K ⊗[𝓞 K] M) = Module.finrank K (K ⊗[𝓞 K] N))
    (σ : K →+* ℂ) (x : ComplexFiber (DeterminantLine (K := K) M) σ) :
    determinantComplexEquiv N σ (fiberMap (determinantMap f hr) σ x) =
      degreeCongr hr (map (Module.finrank K (K ⊗[𝓞 K] M)) (fiberMap f σ)
        (determinantComplexEquiv M σ x)) := by
  let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  have he : (determinantComplexEquiv N σ).toLinearMap.comp (fiberMap (determinantMap f hr) σ) =
      (degreeCongr hr).toLinearMap.comp
        ((map (Module.finrank K (K ⊗[𝓞 K] M)) (fiberMap f σ)).comp
          (determinantComplexEquiv M σ).toLinearMap) := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a y
    have he := determinantMap_section f hr σ y
    change determinantComplexEquiv N σ
      ((determinantMap f hr).baseChange ℂ (a ⊗ₜ[𝓞 K] y)) =
      degreeCongr hr (map _ (fiberMap f σ)
        (determinantComplexEquiv M σ (a ⊗ₜ[𝓞 K] y)))
    have ht (z : DeterminantLine (K := K) M) :
        a ⊗ₜ[𝓞 K] z = a • fiberSection _ σ z := by
      simp only [fiberSection, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [ht, map_smul, map_smul, map_smul, map_smul, map_smul]
    simpa only [fiberSection, LinearMap.baseChange_tmul] using congrArg (a • ·) he
  exact LinearMap.congr_fun he x

variable [NumberField K] [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]

/-- The determinant of an injective equal-rank integral map is injective. -/
lemma determinantMap_injective (f : M →ₗ[𝓞 K] N) (hf : Function.Injective f)
    (hr : Module.finrank K (K ⊗[𝓞 K] M) = Module.finrank K (K ⊗[𝓞 K] N)) :
    Function.Injective (determinantMap f hr) :=
  (degreeCongr hr).injective.comp (exteriorMap_injective f hf _)

end BostConjecture.Arithmetic
