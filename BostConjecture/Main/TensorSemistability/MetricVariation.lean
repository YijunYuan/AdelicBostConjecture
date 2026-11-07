/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Bundle.Conjugation
public import BostConjecture.Arithmetic.Bundle.Scaling

/-!
# Archimedean changes of an actual Hermitian metric

Conjugation-compatible complex fiber automorphisms pull back an actual
Hermitian metric. Determinant-one automorphisms preserve its determinant
metric and hence its arithmetic degree, without acting on the integral module.

Reference: this paper, Proposition 7.3, page 13.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct exteriorPower

namespace BostConjecture.Arithmetic.HermitianMetric

variable {K : Type*} [Field K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]

/-- Pull back the archimedean forms by a conjugation-compatible family of
fiber automorphisms, keeping the integral module fixed. -/
def archimedeanPullback (h : HermitianMetric K M)
    (g : ∀ σ : K →+* ℂ, ComplexFiber M σ ≃ₗ[ℂ] ComplexFiber M σ)
    (hc : ∀ (σ : K →+* ℂ) (x : ComplexFiber M σ),
      g (ComplexEmbedding.conjugate σ) (fiberConjugate M σ x) =
        fiberConjugate M σ (g σ x)) : HermitianMetric K M where
  fiber σ :=
    { inner := fun x y => (h.fiber σ).inner (g σ x) (g σ y)
      conj_inner_symm := fun x y => (h.fiber σ).conj_inner_symm _ _
      re_inner_nonneg := fun x => (h.fiber σ).re_inner_nonneg _
      add_left := by intros; simp only [map_add, (h.fiber σ).add_left]
      smul_left := by intros; simp only [map_smul, (h.fiber σ).smul_left]
      definite := by
        intro x hx
        exact (g σ).injective (by simpa only [map_zero] using (h.fiber σ).definite _ hx) }
  conjugate := by
    intro σ x y
    change (h.fiber (ComplexEmbedding.conjugate σ)).inner
      (g (ComplexEmbedding.conjugate σ) (fiberSection M _ x))
      (g (ComplexEmbedding.conjugate σ) (fiberSection M _ y)) = _
    rw [← fiberConjugate_section M σ x, ← fiberConjugate_section M σ y, hc, hc]
    exact h.inner_conjugate σ _ _

@[simp]
lemma archimedeanPullback_inner (h : HermitianMetric K M)
    (g : ∀ σ : K →+* ℂ, ComplexFiber M σ ≃ₗ[ℂ] ComplexFiber M σ)
    (hc : ∀ (σ : K →+* ℂ) (x : ComplexFiber M σ),
      g (ComplexEmbedding.conjugate σ) (fiberConjugate M σ x) =
        fiberConjugate M σ (g σ x))
    (σ : K →+* ℂ) (x y : ComplexFiber M σ) :
    ((h.archimedeanPullback g hc).fiber σ).inner x y =
      (h.fiber σ).inner (g σ x) (g σ y) := rfl

variable [Module.Finite (𝓞 K) M]

/-- Determinant-one changes preserve the actual determinant metric at every fiber. -/
theorem determinant_archimedeanPullback (h : HermitianMetric K M)
    (g : ∀ σ : K →+* ℂ, ComplexFiber M σ ≃ₗ[ℂ] ComplexFiber M σ)
    (hc : ∀ (σ : K →+* ℂ) (x : ComplexFiber M σ),
      g (ComplexEmbedding.conjugate σ) (fiberConjugate M σ x) =
        fiberConjugate M σ (g σ x))
    (hd : ∀ σ, LinearMap.det (g σ).toLinearMap = 1) :
    (h.archimedeanPullback g hc).determinant = h.determinant := by
  apply ext
  intro σ
  symm
  apply (h.archimedeanPullback g hc).determinantFiber_unique σ
  intro x
  let b := (Module.finBasis ℂ (ComplexFiber M σ)).reindex
    (finCongr (complexFiber_finrank M σ))
  have hw : ιMulti ℂ _ (g σ ∘ x) = ιMulti ℂ _ x := by
    apply (Geometry.determinantCoordinates b).injective
    rw [Geometry.determinantCoordinates_ιMulti, Geometry.determinantCoordinates_ιMulti]
    change b.det ((g σ).toLinearMap ∘ x) = b.det x
    rw [b.det_comp, hd, one_mul]
  have he := h.determinantFiber_inner_ιMulti σ (g σ ∘ x) (g σ ∘ x)
  rw [hw] at he
  exact congrArg Complex.re he

variable [NumberField K]

/-- These archimedean changes preserve arithmetic normalization exactly. -/
theorem degree_archimedeanPullback (h : HermitianMetric K M)
    (g : ∀ σ : K →+* ℂ, ComplexFiber M σ ≃ₗ[ℂ] ComplexFiber M σ)
    (hc : ∀ (σ : K →+* ℂ) (x : ComplexFiber M σ),
      g (ComplexEmbedding.conjugate σ) (fiberConjugate M σ x) =
        fiberConjugate M σ (g σ x))
    (hd : ∀ σ, LinearMap.det (g σ).toLinearMap = 1) :
    (h.archimedeanPullback g hc).degree = h.degree := by
  unfold degree
  rw [determinant_archimedeanPullback h g hc hd]

end BostConjecture.Arithmetic.HermitianMetric
