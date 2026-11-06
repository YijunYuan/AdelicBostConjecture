module

public import BostConjecture.Main.TensorSemistability.DegreeDerivative
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Gram determinants and intrinsic arithmetic degree variation

Express a fixed nonzero integral determinant section in any complex basis.
Its squared norm is a fixed positive coordinate factor times the Gram
determinant. Thus derivatives of actual fiber Gram matrices compute the
arithmetic degree derivative without choosing an integral basis.

Reference: bost_specht_manuscript.pdf, Proposition 7.3, page 13.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct exteriorPower

namespace BostConjecture.Arithmetic.HermitianMetric

variable {K : Type*} [Field K] [NumberField K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]
variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]

omit [NumberField K] [Module.Projective (𝓞 K) M] in
/-- The norm of a fixed integral determinant section is the Gram determinant
times the squared norm of its coordinate in the top exterior basis. -/
theorem determinant_sectionNorm_sq_eq_gram (h : HermitianMetric (K := K) M)
    (σ : K →+* ℂ)
    (b : Module.Basis (Fin (Module.finrank K (K ⊗[𝓞 K] M))) ℂ (ComplexFiber M σ))
    (ξ : DeterminantLine (K := K) M) :
    h.determinant.sectionNorm σ ξ ^ 2 =
      Complex.normSq ((Geometry.determinantCoordinates b)
        (determinantComplexEquiv M σ (fiberSection _ σ ξ))) *
      (Matrix.of fun i j => (h.fiber σ).inner (b i) (b j)).det.re := by
  let e := determinantComplexEquiv M σ ≪≫ₗ Geometry.determinantCoordinates b
  let c := e (fiberSection _ σ ξ)
  have hv : fiberSection _ σ ξ =
      c • (determinantComplexEquiv M σ).symm (ιMulti ℂ _ b) := by
    calc
      _ = e.symm (e (fiberSection _ σ ξ)) := (e.symm_apply_apply _).symm
      _ = _ := by
        simp only [e, LinearEquiv.symm_trans_apply,
          Geometry.determinantCoordinates_symm_apply, map_smul]
        rfl
  unfold sectionNorm
  have hn : 0 ≤ (((h.determinant.fiber σ).inner
      (fiberSection _ σ ξ) (fiberSection _ σ ξ)).re) :=
    (h.determinant.fiber σ).re_inner_nonneg _
  rw [Real.sq_sqrt hn]
  let : InnerProductSpace.Core ℂ (ComplexFiber (DeterminantLine (K := K) M) σ) :=
    h.determinantFiber σ
  change ((h.determinantFiber σ).inner _ _).re = Complex.normSq c * _
  conv_lhs => rw [hv]
  rw [InnerProductSpace.Core.inner_smul_left, InnerProductSpace.Core.inner_smul_right,
    h.determinantFiber_inner_ιMulti]
  change (star c * (c * (Matrix.of fun i j => (h.fiber σ).inner (b i) (b j)).det)).re =
    Complex.normSq c * _
  simp only [Complex.star_def, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  ring

/-- In an orthonormal frame at the base point, all determinant-coordinate
factors cancel from the arithmetic derivative. -/
theorem hasDerivAt_degree_of_gram (h : ℝ → HermitianMetric (K := K) M) {t₀ : ℝ}
    (b : ∀ σ : K →+* ℂ,
      Module.Basis (Fin (Module.finrank K (K ⊗[𝓞 K] M))) ℂ (ComplexFiber M σ))
    (hb : ∀ σ, (Matrix.of fun i j => ((h t₀).fiber σ).inner (b σ i) (b σ j)) = 1)
    (d : (K →+* ℂ) → ℝ)
    (hd : ∀ σ, HasDerivAt
      (fun t => (Matrix.of fun i j => ((h t).fiber σ).inner (b σ i) (b σ j)).det.re)
      (d σ) t₀) :
    HasDerivAt (fun t => (h t).degree)
      (-(∑ σ, d σ) / (2 * (Module.finrank ℚ K : ℝ))) t₀ := by
  obtain ⟨ξ, hξ⟩ := exists_ne (0 : DeterminantLine (K := K) M)
  let C := fun σ : K →+* ℂ => Complex.normSq ((Geometry.determinantCoordinates (b σ))
    (determinantComplexEquiv M σ (fiberSection _ σ ξ)))
  have hC (σ : K →+* ℂ) : C σ ≠ 0 := by
    apply mt Complex.normSq_eq_zero.mp
    apply (Geometry.determinantCoordinates (b σ)).map_ne_zero_iff.mpr
    apply (determinantComplexEquiv M σ).map_ne_zero_iff.mpr
    exact fun he => hξ (fiberSection_injective _ σ (by simpa [fiberSection] using he))
  have hq (σ : K →+* ℂ) : HasDerivAt
      (fun t => (h t).determinant.sectionNorm σ ξ ^ 2) (C σ * d σ) t₀ := by
    convert (hd σ).const_mul (C σ) using 1
    funext t
    exact (h t).determinant_sectionNorm_sq_eq_gram σ (b σ) ξ
  have hbase (σ : K →+* ℂ) : (h t₀).determinant.sectionNorm σ ξ ^ 2 = C σ := by
    rw [determinant_sectionNorm_sq_eq_gram _ σ (b σ), hb, Matrix.det_one]
    simp only [Complex.one_re, mul_one]
    rfl
  convert hasDerivAt_degree_of_norm_sq h hξ (fun σ => C σ * d σ) hq using 1
  simp_rw [hbase]
  have he (σ : K →+* ℂ) : C σ * d σ / (2 * C σ) = d σ / 2 := by
    field_simp [hC σ]
  simp_rw [he]
  rw [← Finset.sum_div]
  ring

/-- Local maximality of actual arithmetic degree forces vanishing of the
embedding sum of Gram derivatives. This is an intermediate stationarity
statement; admissible metric curves must still be constructed. -/
theorem sum_gram_deriv_eq_zero_of_isLocalMax
    (h : ℝ → HermitianMetric (K := K) M) {t₀ : ℝ}
    (b : ∀ σ : K →+* ℂ,
      Module.Basis (Fin (Module.finrank K (K ⊗[𝓞 K] M))) ℂ (ComplexFiber M σ))
    (hb : ∀ σ, (Matrix.of fun i j => ((h t₀).fiber σ).inner (b σ i) (b σ j)) = 1)
    (d : (K →+* ℂ) → ℝ)
    (hd : ∀ σ, HasDerivAt
      (fun t => (Matrix.of fun i j => ((h t).fiber σ).inner (b σ i) (b σ j)).det.re)
      (d σ) t₀)
    (hmax : IsLocalMax (fun t => (h t).degree) t₀) : ∑ σ, d σ = 0 := by
  have he := hmax.hasDerivAt_eq_zero (hasDerivAt_degree_of_gram h b hb d hd)
  have hD : (2 * (Module.finrank ℚ K : ℝ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (by exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne')
  exact neg_eq_zero.mp ((div_eq_zero_iff.mp he).resolve_right hD)

end BostConjecture.Arithmetic.HermitianMetric
