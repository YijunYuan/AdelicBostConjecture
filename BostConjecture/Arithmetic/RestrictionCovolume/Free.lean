/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.RestrictionCovolume.Covolume
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.RingTheory.AlgebraTower

/-!
# Discriminant calculation in an integral frame

The trace Gram matrix in the integer basis induced by an integral frame
factors through the matrix of all complex embeddings and the block diagonal
matrix of the Hermitian forms. Its determinant supplies the discriminant
factor with both members of every conjugate pair counted.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct MeasureTheory exteriorPower
open scoped Matrix Kronecker

namespace BostConjecture.Arithmetic.HermitianMetric

variable {K : Type*} [Field K] [NumberField K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]
variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
variable (h : HermitianMetric (K := K) M)

omit [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M] in
/-- The complex sum of section pairings is the real trace pairing. -/
lemma ofReal_traceSection_inner (x y : M) :
    (inner ℝ (h.traceSection x) (h.traceSection y) : ℂ) =
      ∑ σ : K →+* ℂ, (h.fiber σ).inner (fiberSection M σ x) (fiberSection M σ y) := by
  classical
  let f (σ : K →+* ℂ) := (h.fiber σ).inner (fiberSection M σ x) (fiberSection M σ y)
  have hc : star (∑ σ, f σ) = ∑ σ, f σ := by
    rw [star_sum]
    calc
      ∑ σ, star (f σ) = ∑ σ, f (ComplexEmbedding.conjugate σ) := by
        apply Finset.sum_congr rfl
        intro σ _
        exact (h.conjugate σ x y).symm
      _ = ∑ σ, f σ := Equiv.sum_comp (ComplexEmbedding.involutive_conjugate K).toPerm f
  have hi : (∑ σ, f σ).im = 0 := by
    have hh := congrArg Complex.im hc
    simp only [Complex.star_def, Complex.conj_im] at hh
    linarith
  apply Complex.ext
  · change (∑ σ, (f σ).re) = (∑ σ, f σ).re
    simp
  · exact hi.symm

/-- The integral frame, expanded in the fixed integer basis of the number field. -/
def traceIntegerBasis {r : ℕ} (b : Module.Basis (Fin r) (𝓞 K) M) :
    Module.Basis (Fin r × (K →+* ℂ)) ℤ M :=
  ((((RingOfIntegers.basis K).reindex (equivReindex K).symm).smulTower b).reindex
    (Equiv.prodComm _ _))

omit [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M] in
lemma traceIntegerBasis_apply {r : ℕ} (b : Module.Basis (Fin r) (𝓞 K) M)
    (i : Fin r) (τ : K →+* ℂ) :
    traceIntegerBasis b (i, τ) = RingOfIntegers.basis K (equivReindex K τ) • b i := by
  simp [traceIntegerBasis]

open Classical in
/-- The embedding matrix has squared absolute determinant equal to the absolute discriminant. -/
lemma norm_det_basisMatrix_sq : ‖(basisMatrix K).det‖ ^ 2 = |(NumberField.discr K : ℝ)| := by
  classical
  have hh := congrArg norm (NumberField.discr_eq_basisMatrix_det_sq K)
  simpa only [norm_pow, Complex.norm_intCast, Int.norm_eq_abs, Int.cast_abs] using hh.symm

omit [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M] in
open Classical in
/-- The trace Gram matrix factors through the embedding matrix and the actual fiber Gram blocks. -/
lemma traceGram_factorization {r : ℕ} (b : Module.Basis (Fin r) (𝓞 K) M) :
    let E := (1 : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ (basisMatrix K).transpose
    let G := Matrix.blockDiagonal (fun σ : K →+* ℂ => Matrix.of fun i j =>
      (h.fiber σ).inner (fiberSection M σ (b i)) (fiberSection M σ (b j)))
    (Matrix.gram ℝ (fun i => h.traceSection (traceIntegerBasis b i))).map
      Complex.ofRealHom = E.conjTranspose * G * E := by
  classical
  let : ∀ σ : K →+* ℂ, InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber
  dsimp only
  ext ⟨i, τ⟩ ⟨j, υ⟩
  rw [Matrix.map_apply]
  change (inner ℝ (h.traceSection (traceIntegerBasis b (i, τ)))
    (h.traceSection (traceIntegerBasis b (j, υ))) : ℂ) = _
  rw [h.ofReal_traceSection_inner, traceIntegerBasis_apply, traceIntegerBasis_apply]
  simp only [fiberSection_smul, InnerProductSpace.Core.inner_smul_left,
    InnerProductSpace.Core.inner_smul_right]
  simp only [basisMatrix, canonicalEmbedding.latticeBasis_apply, integralBasis_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Matrix.transpose_apply, Matrix.of_apply, canonicalEmbedding.apply_at, ite_mul, one_mul,
    zero_mul, apply_ite, RCLike.star_def, star_zero, Matrix.blockDiagonal_apply, mul_zero,
    Fintype.sum_prod_type, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
    Finset.sum_ite_irrel, Finset.sum_const_zero]
  apply Finset.sum_congr rfl
  intro σ _
  ring

/-- Squared trace covolume in an integral frame, before replacing each fiber
Gram determinant by the induced determinant norm. -/
theorem traceCovolume_sq_eq_discr_mul_prod {r : ℕ}
    (b : Module.Basis (Fin r) (𝓞 K) M) :
    h.traceCovolume ^ 2 = |(NumberField.discr K : ℝ)| ^ r *
      ∏ σ : K →+* ℂ, ‖(Matrix.of fun i j =>
        (h.fiber σ).inner (fiberSection M σ (b i)) (fiberSection M σ (b j))).det‖ := by
  classical
  have hf := congrArg (fun A => ‖A.det‖) (h.traceGram_factorization b)
  have hg : (Matrix.gram ℝ (fun i => h.traceSection (traceIntegerBasis b i))).det =
      h.traceCovolume ^ 2 := (h.traceCovolume_sq_eq_det (traceIntegerBasis b)).symm
  have hmap (A : Matrix (Fin r × (K →+* ℂ)) (Fin r × (K →+* ℂ)) ℝ) :
      (A.map Complex.ofRealHom).det = (A.det : ℂ) :=
    (Complex.ofRealHom.map_det A).symm
  rw [hmap] at hf
  change ‖((Matrix.gram ℝ (fun i => h.traceSection (traceIntegerBasis b i))).det : ℂ)‖ = _ at hf
  simp only [Complex.norm_real,
    Real.norm_eq_abs, hg, abs_of_pos h.traceCovolume_pos, Matrix.det_mul, Matrix.det_conjTranspose,
    Matrix.det_kronecker, Matrix.det_one, one_pow, one_mul, Matrix.det_transpose,
    Matrix.det_blockDiagonal, norm_mul, norm_star, norm_pow, norm_prod,
    Fintype.card_fin] at hf
  calc
    h.traceCovolume ^ 2 = (‖(basisMatrix K).det‖ ^ r) ^ 2 *
        ∏ σ : K →+* ℂ, ‖(Matrix.of fun i j =>
          (h.fiber σ).inner (fiberSection M σ (b i)) (fiberSection M σ (b j))).det‖ := by
      rw [hf]
      ring
    _ = _ := by rw [← pow_mul, Nat.mul_comm r 2, pow_mul, norm_det_basisMatrix_sq]

omit [NumberField K] [Module.Projective (𝓞 K) M] in
/-- A determinant metric norm squares to the absolute complex Gram determinant. -/
lemma norm_det_gram_eq_sectionNorm_sq (σ : K →+* ℂ)
    (x : Fin (Module.finrank K (K ⊗[𝓞 K] M)) → M) :
    ‖(Matrix.of fun i j => (h.fiber σ).inner
      (fiberSection M σ (x i)) (fiberSection M σ (x j))).det‖ =
      (h.determinant.sectionNorm σ (ιMulti (𝓞 K) _ x)) ^ 2 := by
  let := h.determinantFiber σ
  rw [← h.determinantFiber_inner_wedge, ← InnerProductSpace.Core.inner_self_ofReal_re]
  change ‖(((h.determinantFiber σ).inner
    (fiberSection (DeterminantLine (K := K) M) σ (ιMulti (𝓞 K) _ x))
    (fiberSection (DeterminantLine (K := K) M) σ (ιMulti (𝓞 K) _ x))).re : ℂ)‖ = _
  have hn : 0 ≤ ((h.determinantFiber σ).inner
    (fiberSection (DeterminantLine (K := K) M) σ (ιMulti (𝓞 K) _ x))
    (fiberSection (DeterminantLine (K := K) M) σ (ιMulti (𝓞 K) _ x))).re :=
    (h.determinantFiber σ).re_inner_nonneg _
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn, h.determinantFiber_inner_wedge]
  exact (h.determinant_sectionNorm_wedge_sq σ x).symm

/-- Exact covolume expressed using the determinant norms of an integral frame. -/
theorem traceCovolume_eq_discr_mul_prod
    (b : Module.Basis (Fin (Module.finrank K (K ⊗[𝓞 K] M))) (𝓞 K) M) :
    h.traceCovolume = |(NumberField.discr K : ℝ)| ^
        ((Module.finrank K (K ⊗[𝓞 K] M) : ℝ) / 2) *
      ∏ σ : K →+* ℂ, h.determinant.sectionNorm σ (ιMulti (𝓞 K) _ b) := by
  have hs := h.traceCovolume_sq_eq_discr_mul_prod b
  simp_rw [h.norm_det_gram_eq_sectionNorm_sq, Finset.prod_pow] at hs
  have hp : (|(NumberField.discr K : ℝ)| ^
      ((Module.finrank K (K ⊗[𝓞 K] M) : ℝ) / 2)) ^ 2 =
      |(NumberField.discr K : ℝ)| ^ Module.finrank K (K ⊗[𝓞 K] M) := by
    rw [← Real.rpow_mul_natCast (abs_nonneg _)]
    norm_num [Real.rpow_natCast]
  have hn : 0 ≤ |(NumberField.discr K : ℝ)| ^
      ((Module.finrank K (K ⊗[𝓞 K] M) : ℝ) / 2) *
      ∏ σ : K →+* ℂ, h.determinant.sectionNorm σ (ιMulti (𝓞 K) _ b) :=
    mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (Finset.prod_nonneg fun _ _ =>
      Real.sqrt_nonneg _)
  nlinarith [h.traceCovolume_pos, mul_pow
    (|(NumberField.discr K : ℝ)| ^ ((Module.finrank K (K ⊗[𝓞 K] M) : ℝ) / 2))
    (∏ σ : K →+* ℂ, h.determinant.sectionNorm σ (ιMulti (𝓞 K) _ b)) 2]

/-- A free integral frame computes the existing intrinsic degree without an index term. -/
theorem degree_eq_neg_sum_log_of_basis
    (b : Module.Basis (Fin (Module.finrank K (K ⊗[𝓞 K] M))) (𝓞 K) M) :
    h.degree = -(∑ σ : K →+* ℂ,
      Real.log (h.determinant.sectionNorm σ (ιMulti (𝓞 K) _ b))) /
        (Module.finrank ℚ K : ℝ) := by
  let e : DeterminantLine (K := K) M ≃ₗ[𝓞 K] 𝓞 K := Geometry.determinantCoordinates b
  let ξ := e.symm 1
  have hξ : ξ ≠ 0 := e.symm.map_ne_zero_iff.mpr one_ne_zero
  have he : ξ = ιMulti (𝓞 K) _ b := by
    simp [ξ, e, Geometry.determinantCoordinates_symm_apply]
  have hs : (𝓞 K ∙ ξ) = ⊤ := by
    apply top_unique
    intro y _
    obtain ⟨a, rfl⟩ := e.symm.surjective y
    exact Submodule.mem_span_singleton.mpr ⟨a, by simp [ξ, ← map_smul]⟩
  have hq : Nat.card (DeterminantLine (K := K) M ⧸ (𝓞 K ∙ ξ)) = 1 := by
    rw [hs]
    exact Nat.card_unique
  rw [h.degree_eq hξ, hq, he]
  simp

/-- The exact restriction-covolume formula for a module with an integral frame. -/
theorem traceCovolume_eq_discr_degree_of_basis
    (b : Module.Basis (Fin (Module.finrank K (K ⊗[𝓞 K] M))) (𝓞 K) M) :
    h.traceCovolume = |(NumberField.discr K : ℝ)| ^
        ((Module.finrank K (K ⊗[𝓞 K] M) : ℝ) / 2) *
      Real.exp (-(Module.finrank ℚ K : ℝ) * h.degree) := by
  rw [h.traceCovolume_eq_discr_mul_prod b, h.degree_eq_neg_sum_log_of_basis b]
  congr 1
  have hD : (Module.finrank ℚ K : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Module.finrank_pos (R := ℚ) (M := K)))
  have ha (s : ℝ) : -(Module.finrank ℚ K : ℝ) * (-s / (Module.finrank ℚ K : ℝ)) = s := by
    field_simp
  rw [ha, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro σ _
  apply (Real.exp_log _).symm
  apply h.determinant.sectionNorm_pos
  have he := (Geometry.determinantCoordinates b).symm.map_ne_zero_iff.mpr
    (one_ne_zero : (1 : 𝓞 K) ≠ 0)
  simpa using he

end BostConjecture.Arithmetic.HermitianMetric
