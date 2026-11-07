/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Bundle.Basic
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Flat.EquationalCriterion

/-!
# Induced Hermitian metrics on integral submodules

Complex scalar extension preserves every integral injection, because it is
the composite of localization to the number field and extension of fields.
The actual fiber map therefore pulls back positive Hermitian metrics, and
its section norms agree with the ambient section norms.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace BostConjecture.Arithmetic

variable {K : Type*} [Field K]
variable {M N : Type*} [AddCommGroup M] [Module (𝓞 K) M]
variable [AddCommGroup N] [Module (𝓞 K) N]

/-- The canonical complex scalar extension of an integral linear map. -/
def fiberMap (f : N →ₗ[𝓞 K] M) (σ : K →+* ℂ) :
    ComplexFiber N σ →ₗ[ℂ] ComplexFiber M σ :=
  let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  f.baseChange ℂ

@[simp]
lemma fiberMap_section (f : N →ₗ[𝓞 K] M) (σ : K →+* ℂ) (x : N) :
    fiberMap f σ (fiberSection N σ x) = fiberSection M σ (f x) := rfl

variable [NumberField K]

/-- Archimedean scalar extension preserves integral injections. -/
lemma fiberMap_injective (f : N →ₗ[𝓞 K] M) (hf : Function.Injective f) (σ : K →+* ℂ) :
    Function.Injective (fiberMap f σ) := by
  let : Algebra K ℂ := σ.toAlgebra
  let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  let : IsScalarTower (𝓞 K) K ℂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Module.Flat (𝓞 K) ℂ := Module.Flat.trans (𝓞 K) K ℂ
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := ℂ) f hf

/-- Every integral submodule of a finite projective module over the ring of
integers is projective, without an integral basis. Finiteness is supplied by
Noetherianity. -/
instance submoduleProjective [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
    (P : Submodule (𝓞 K) M) : Module.Projective (𝓞 K) P := by
  let : Module.FinitePresentation (𝓞 K) P := Module.finitePresentation_of_finite (𝓞 K) P
  exact Module.Flat.projective_of_finitePresentation

namespace HermitianMetric

/-- Pull back a Hermitian metric along an injective integral linear map. -/
def pullback (h : HermitianMetric K M) (f : N →ₗ[𝓞 K] M)
    (hf : Function.Injective f) : HermitianMetric K N where
  fiber σ :=
    { inner := fun x y => (h.fiber σ).inner (fiberMap f σ x) (fiberMap f σ y)
      conj_inner_symm := fun x y => (h.fiber σ).conj_inner_symm _ _
      re_inner_nonneg := fun x => (h.fiber σ).re_inner_nonneg _
      add_left := by
        intro x y z
        rw [map_add, (h.fiber σ).add_left]
      smul_left := by
        intro x y a
        rw [map_smul, (h.fiber σ).smul_left]
      definite := by
        intro x hx
        apply fiberMap_injective f hf σ
        simpa only [map_zero] using (h.fiber σ).definite (fiberMap f σ x) hx }
  conjugate := by
    intro σ x y
    change (h.fiber (ComplexEmbedding.conjugate σ)).inner
      (fiberMap f (ComplexEmbedding.conjugate σ) (fiberSection N _ x))
      (fiberMap f (ComplexEmbedding.conjugate σ) (fiberSection N _ y)) =
      star ((h.fiber σ).inner (fiberMap f σ (fiberSection N σ x))
        (fiberMap f σ (fiberSection N σ y)))
    simp only [fiberMap_section, h.conjugate]

lemma pullback_inner (h : HermitianMetric K M) (f : N →ₗ[𝓞 K] M)
    (hf : Function.Injective f) (σ : K →+* ℂ) (x y : ComplexFiber N σ) :
    ((h.pullback f hf).fiber σ).inner x y =
      (h.fiber σ).inner (fiberMap f σ x) (fiberMap f σ y) := rfl

@[simp]
lemma sectionNorm_pullback (h : HermitianMetric K M) (f : N →ₗ[𝓞 K] M)
    (hf : Function.Injective f) (σ : K →+* ℂ) (x : N) :
    (h.pullback f hf).sectionNorm σ x = h.sectionNorm σ (f x) := by
  simp only [sectionNorm, pullback_inner, fiberMap_section]

/-- The induced Hermitian metric on an actual integral submodule. -/
def submodule (h : HermitianMetric K M) (P : Submodule (𝓞 K) M) :
    HermitianMetric K P := h.pullback P.subtype P.injective_subtype

@[simp]
lemma sectionNorm_submodule (h : HermitianMetric K M)
    (P : Submodule (𝓞 K) M) (σ : K →+* ℂ) (x : P) :
    (h.submodule P).sectionNorm σ x = h.sectionNorm σ x :=
  h.sectionNorm_pullback P.subtype P.injective_subtype σ x

end HermitianMetric
end BostConjecture.Arithmetic
