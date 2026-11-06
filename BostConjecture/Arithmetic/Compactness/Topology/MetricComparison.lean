/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Determinant.Contraction
public import BostConjecture.Arithmetic.Bundle.Scaling

/-!
# Uniform comparison of actual Hermitian metrics

An exponential bound between actual fiber norms bounds the change of every
induced degree by the generic rank times the exponent. The proof uses the
existing determinant contraction and rescaling theorems.

Reference: this paper, page 12.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace BostConjecture.Arithmetic.HermitianMetric

variable {K : Type*} [Field K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]

/-- The norm supplied by a metric on its actual complex fiber. -/
def fiberNorm (h : HermitianMetric (K := K) M) (σ : K →+* ℂ)
    (x : ComplexFiber M σ) : ℝ := Real.sqrt (((h.fiber σ).inner x x).re)

lemma fiberNorm_nonneg (h : HermitianMetric (K := K) M) (σ : K →+* ℂ)
    (x : ComplexFiber M σ) : 0 ≤ h.fiberNorm σ x := Real.sqrt_nonneg _

@[simp]
lemma fiberNorm_section (h : HermitianMetric (K := K) M) (σ : K →+* ℂ) (x : M) :
    h.fiberNorm σ (fiberSection M σ x) = h.sectionNorm σ x := rfl

@[simp]
lemma fiberNorm_rescale (h : HermitianMetric (K := K) M) (t : ℝ)
    (σ : K →+* ℂ) (x : ComplexFiber M σ) :
    (h.rescale t).fiberNorm σ x = Real.exp t * h.fiberNorm σ x := by
  simp only [fiberNorm, rescale_inner, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  rw [Real.sqrt_mul (Real.exp_pos _).le, show Real.exp (2 * t) = Real.exp t ^ 2 by
    rw [two_mul, Real.exp_add, pow_two], Real.sqrt_sq (Real.exp_pos _).le]

variable [NumberField K]

@[simp]
lemma fiberNorm_submodule (h : HermitianMetric (K := K) M) (P : Submodule (𝓞 K) M)
    (σ : K →+* ℂ) (x : ComplexFiber P σ) :
    (h.submodule P).fiberNorm σ x = h.fiberNorm σ (fiberMap P.subtype σ x) := rfl

variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]

/-- An exponential norm bound gives the corresponding one-sided degree bound. -/
theorem degree_sub_rank_mul_le_of_fiberNorm_le
    (h g : HermitianMetric (K := K) M) (t : ℝ)
    (hc : ∀ (σ : K →+* ℂ) (x : ComplexFiber M σ),
      g.fiberNorm σ x ≤ Real.exp t * h.fiberNorm σ x) :
    h.degree - (Module.finrank K (K ⊗[𝓞 K] M) : ℝ) * t ≤ g.degree := by
  rw [← h.degree_rescale t]
  apply (h.rescale t).degree_le_of_injective g LinearMap.id Function.injective_id rfl
  intro σ x
  have he : fiberMap (LinearMap.id : M →ₗ[𝓞 K] M) σ x = x := by
    let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
    exact LinearMap.congr_fun LinearMap.baseChange_id x
  change g.fiberNorm σ (fiberMap LinearMap.id σ x) ≤ (h.rescale t).fiberNorm σ x
  rw [he, fiberNorm_rescale]
  exact hc σ x

/-- Uniformly equivalent actual fiber norms give a rank-sharp degree estimate. -/
theorem abs_degree_sub_le_of_fiberNorm_le
    (h g : HermitianMetric (K := K) M) (t : ℝ)
    (hgh : ∀ (σ : K →+* ℂ) (x : ComplexFiber M σ),
      g.fiberNorm σ x ≤ Real.exp t * h.fiberNorm σ x)
    (hhg : ∀ (σ : K →+* ℂ) (x : ComplexFiber M σ),
      h.fiberNorm σ x ≤ Real.exp t * g.fiberNorm σ x) :
    |g.degree - h.degree| ≤ (Module.finrank K (K ⊗[𝓞 K] M) : ℝ) * t := by
  have h₁ := h.degree_sub_rank_mul_le_of_fiberNorm_le g t hgh
  have h₂ := g.degree_sub_rank_mul_le_of_fiberNorm_le h t hhg
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The same bound holds simultaneously for every actual induced submodule metric. -/
theorem abs_degree_submodule_sub_le_of_fiberNorm_le
    (h g : HermitianMetric (K := K) M) (t : ℝ)
    (hgh : ∀ (σ : K →+* ℂ) (x : ComplexFiber M σ),
      g.fiberNorm σ x ≤ Real.exp t * h.fiberNorm σ x)
    (hhg : ∀ (σ : K →+* ℂ) (x : ComplexFiber M σ),
      h.fiberNorm σ x ≤ Real.exp t * g.fiberNorm σ x)
    (P : Submodule (𝓞 K) M) :
    |(g.submodule P).degree - (h.submodule P).degree| ≤
      (Module.finrank K (K ⊗[𝓞 K] P) : ℝ) * t := by
  exact (h.submodule P).abs_degree_sub_le_of_fiberNorm_le (g.submodule P) t
    (fun σ x => hgh σ (fiberMap P.subtype σ x))
    (fun σ x => hhg σ (fiberMap P.subtype σ x))

end BostConjecture.Arithmetic.HermitianMetric
