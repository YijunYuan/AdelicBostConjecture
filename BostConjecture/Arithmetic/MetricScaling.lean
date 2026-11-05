module

public import BostConjecture.Arithmetic.Degree
public import BostConjecture.Arithmetic.SubmoduleMetric

/-!
# Uniform rescaling of intrinsic Hermitian metrics

Rescaling norms by `exp t` multiplies the positive Hermitian form by `exp (2*t)`.
The Gram formula identifies the rescaled determinant metric; the intrinsic
section formula then gives the change of normalized degree and slope.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct exteriorPower

namespace BostConjecture.Arithmetic.HermitianMetric

variable {K : Type*} [Field K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]

/-- Uniformly multiply all archimedean norms by `exp t`. -/
def rescale (h : HermitianMetric (K := K) M) (t : ℝ) : HermitianMetric (K := K) M where
  fiber σ :=
    { inner := fun x y => (Real.exp (2 * t) : ℂ) * (h.fiber σ).inner x y
      conj_inner_symm := by
        intro x y
        rw [map_mul]
        change (starRingEnd ℂ) (Real.exp (2 * t) : ℂ) *
          (starRingEnd ℂ) ((h.fiber σ).inner y x) = _
        rw [Complex.conj_ofReal, (h.fiber σ).conj_inner_symm]
      re_inner_nonneg := by
        intro x
        change 0 ≤ ((Real.exp (2 * t) : ℂ) * (h.fiber σ).inner x x).re
        rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        exact mul_nonneg (Real.exp_pos (2 * t)).le ((h.fiber σ).re_inner_nonneg x)
      add_left := by
        intro x y z
        rw [(h.fiber σ).add_left, mul_add]
      smul_left := by
        intro x y a
        rw [(h.fiber σ).smul_left]
        ring
      definite := by
        intro x hx
        exact (h.fiber σ).definite x ((mul_eq_zero.mp hx).resolve_left
          (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))) }
  conjugate := by
    intro σ x y
    change (Real.exp (2 * t) : ℂ) * (h.fiber (ComplexEmbedding.conjugate σ)).inner
      (fiberSection M (ComplexEmbedding.conjugate σ) x)
      (fiberSection M (ComplexEmbedding.conjugate σ) y) =
      star ((Real.exp (2 * t) : ℂ) * (h.fiber σ).inner
        (fiberSection M σ x) (fiberSection M σ y))
    rw [h.conjugate, star_mul, Complex.star_def, Complex.conj_ofReal]
    exact mul_comm _ _

lemma rescale_inner (h : HermitianMetric (K := K) M) (t : ℝ) (σ : K →+* ℂ)
    (x y : ComplexFiber M σ) :
    ((h.rescale t).fiber σ).inner x y =
      (Real.exp (2 * t) : ℂ) * (h.fiber σ).inner x y := rfl

/-- The constructed rescaling has the prescribed effect on actual section norms. -/
lemma sectionNorm_rescale (h : HermitianMetric (K := K) M) (t : ℝ)
    (σ : K →+* ℂ) (x : M) :
    (h.rescale t).sectionNorm σ x = Real.exp t * h.sectionNorm σ x := by
  simp only [sectionNorm, rescale_inner, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  rw [Real.sqrt_mul (Real.exp_pos _).le, show Real.exp (2 * t) = Real.exp t ^ 2 by
    rw [two_mul, Real.exp_add, pow_two], Real.sqrt_sq (Real.exp_pos _).le]

/-- Metrics with equal fiber forms are equal. -/
@[ext]
lemma ext {h g : HermitianMetric (K := K) M}
    (hf : ∀ σ, h.fiber σ = g.fiber σ) : h = g := by
  cases h with
  | mk f hc =>
    cases g with
    | mk g gc =>
      have hfg : f = g := funext hf
      cases hfg
      rfl

/-- Rescaling commutes with an actual induced metric. -/
lemma pullback_rescale [NumberField K]
    {N : Type*} [AddCommGroup N] [Module (𝓞 K) N]
    (h : HermitianMetric (K := K) M) (f : N →ₗ[𝓞 K] M)
    (hf : Function.Injective f) (t : ℝ) :
    (h.rescale t).pullback f hf = (h.pullback f hf).rescale t := by
  apply ext
  intro σ
  rfl

/-- Every integral submodule inherits the same uniform norm scaling. -/
lemma submodule_rescale [NumberField K] (h : HermitianMetric (K := K) M)
    (P : Submodule (𝓞 K) M) (t : ℝ) :
    (h.rescale t).submodule P = (h.submodule P).rescale t :=
  h.pullback_rescale P.subtype P.injective_subtype t

variable [Module.Finite (𝓞 K) M]

/-- Uniform rescaling commutes with the intrinsic determinant metric, with
parameter multiplied by the generic rank. -/
theorem determinant_rescale (h : HermitianMetric (K := K) M) (t : ℝ) :
    (h.rescale t).determinant =
      h.determinant.rescale ((Module.finrank K (K ⊗[𝓞 K] M) : ℝ) * t) := by
  apply ext
  intro σ
  symm
  apply (h.rescale t).determinantFiber_unique σ
  intro x
  simp only [rescale_inner]
  change ((Real.exp (2 * ((Module.finrank K (K ⊗[𝓞 K] M) : ℝ) * t)) : ℂ) *
    (h.determinantFiber σ).inner ((determinantComplexEquiv M σ).symm (ιMulti ℂ _ x)) ((determinantComplexEquiv M σ).symm (ιMulti ℂ _ x))).re = _
  rw [h.determinantFiber_inner_ιMulti σ x x]
  have hm : (Matrix.of fun i j => (Real.exp (2 * t) : ℂ) *
      (h.fiber σ).inner (x i) (x j)) =
      (Real.exp (2 * t) : ℂ) • (Matrix.of fun i j => (h.fiber σ).inner (x i) (x j)) := rfl
  rw [hm, Matrix.det_smul, Fintype.card_fin]
  have he : (Real.exp (2 * ((Module.finrank K (K ⊗[𝓞 K] M) : ℝ) * t)) : ℂ) =
      (Real.exp (2 * t) : ℂ) ^ Module.finrank K (K ⊗[𝓞 K] M) := by
    rw [← Complex.ofReal_pow, ← Real.exp_nat_mul]
    congr 2
    ring
  rw [he]

variable [NumberField K] [Module.Projective (𝓞 K) M]

/-- Scaling line norms by `exp t` subtracts `t` from normalized degree. -/
theorem lineDegree_rescale [Nontrivial M] (h : HermitianMetric (K := K) M)
    (hr : Module.finrank K (K ⊗[𝓞 K] M) = 1) (t : ℝ) :
    (h.rescale t).lineDegree hr = h.lineDegree hr - t := by
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  rw [(h.rescale t).lineDegree_eq_sum_embeddings hr hx,
    h.lineDegree_eq_sum_embeddings hr hx]
  simp_rw [sectionNorm_rescale, Real.log_mul (Real.exp_ne_zero t)
    (ne_of_gt (h.sectionNorm_pos _ hx)), Real.log_exp]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, NumberField.Embeddings.card]
  have hD : (Module.finrank ℚ K : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'
  field_simp
  ring

/-- Uniform rescaling of norms subtracts rank times the parameter from degree. -/
theorem degree_rescale (h : HermitianMetric (K := K) M) (t : ℝ) :
    (h.rescale t).degree = h.degree - (Module.finrank K (K ⊗[𝓞 K] M) : ℝ) * t := by
  rw [degree, determinant_rescale, lineDegree_rescale]
  rfl

/-- Every positive-rank slope decreases by the norm-scaling parameter. -/
theorem slope_rescale (h : HermitianMetric (K := K) M)
    (hr : Module.finrank K (K ⊗[𝓞 K] M) ≠ 0) (t : ℝ) :
    (h.rescale t).slope = h.slope - t := by
  rw [slope, slope, degree_rescale, sub_div, mul_div_cancel_left₀ t (Nat.cast_ne_zero.mpr hr)]

/-- Rescaling by the original slope produces a bundle of slope zero. -/
theorem slope_rescale_self (h : HermitianMetric (K := K) M)
    (hr : Module.finrank K (K ⊗[𝓞 K] M) ≠ 0) : (h.rescale h.slope).slope = 0 := by
  rw [slope_rescale h hr, sub_self]

/-- Degree scaling for every actual integral submodule of a Hermitian bundle. -/
theorem degree_submodule_rescale (h : HermitianMetric (K := K) M)
    (P : Submodule (𝓞 K) M) (t : ℝ) :
    ((h.rescale t).submodule P).degree = (h.submodule P).degree -
      (Module.finrank K (K ⊗[𝓞 K] P) : ℝ) * t := by
  rw [submodule_rescale, degree_rescale]

/-- Every positive-rank submodule's slope decreases by the same parameter. -/
theorem slope_submodule_rescale (h : HermitianMetric (K := K) M)
    (P : Submodule (𝓞 K) M) (hr : Module.finrank K (K ⊗[𝓞 K] P) ≠ 0) (t : ℝ) :
    ((h.rescale t).submodule P).slope = (h.submodule P).slope - t := by
  rw [submodule_rescale, slope_rescale _ hr]

end BostConjecture.Arithmetic.HermitianMetric
