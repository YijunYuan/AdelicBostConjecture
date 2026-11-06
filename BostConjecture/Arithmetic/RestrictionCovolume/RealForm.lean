module

public import BostConjecture.Arithmetic.RestrictionCovolume.Conjugation
public import BostConjecture.Arithmetic.DeterminantLine

/-!
# The actual trace space as a real form

Complexifying the constructed trace space recovers the product of all
complex fibers. Its real vectors are exactly the conjugation-compatible
families. This identifies the domain of componentwise orthogonal lifts
needed by trace quotient metrics.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct
open scoped Classical

namespace BostConjecture.Arithmetic.HermitianMetric

variable {K : Type*} [Field K] [NumberField K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]
variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
variable (h : HermitianMetric (K := K) M)

omit [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M] in
/-- The pairing sum of two conjugation-compatible families is real. -/
lemma sum_inner_im_eq_zero_of_conjugate
    (x y : (σ : K →+* ℂ) → ComplexFiber M σ)
    (hx : ∀ σ, fiberConjugate M σ (x σ) = x (ComplexEmbedding.conjugate σ))
    (hy : ∀ σ, fiberConjugate M σ (y σ) = y (ComplexEmbedding.conjugate σ)) :
    (∑ σ, (h.fiber σ).inner (x σ) (y σ)).im = 0 := by
  let f (σ : K →+* ℂ) := (h.fiber σ).inner (x σ) (y σ)
  have hc : star (∑ σ, f σ) = ∑ σ, f σ := by
    rw [star_sum]
    calc
      ∑ σ, star (f σ) = ∑ σ, f (ComplexEmbedding.conjugate σ) := by
        apply Finset.sum_congr rfl
        intro σ _
        dsimp only [f]
        rw [← hx, ← hy, h.inner_conjugate]
      _ = ∑ σ, f σ := Equiv.sum_comp (ComplexEmbedding.involutive_conjugate K).toPerm f
  have hh := congrArg Complex.im hc
  simp only [Complex.star_def, Complex.conj_im] at hh
  linarith

/-- The real trace pairing equals the full complex sum on real trace vectors. -/
lemma ofReal_trace_inner (x y : h.TraceSpace) :
    (inner ℝ x y : ℂ) = ∑ σ, (h.fiber σ).inner
      (h.traceInclusion x σ) (h.traceInclusion y σ) := by
  apply Complex.ext
  · change (∑ σ, ((h.fiber σ).inner (h.traceInclusion x σ) (h.traceInclusion y σ)).re) = _
    simp
  · exact (h.sum_inner_im_eq_zero_of_conjugate _ _
      (h.traceInclusion_conjugate x) (h.traceInclusion_conjugate y)).symm

omit [NumberField K] [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M] in
/-- Separate the real and imaginary parts of a complexified real vector. -/
lemma complex_tensor_decompose (z : ℂ ⊗[ℝ] h.TraceSpace) :
    ∃ x y : h.TraceSpace, z = 1 ⊗ₜ[ℝ] x + Complex.I ⊗ₜ[ℝ] y := by
  induction z using TensorProduct.inductionOn with
  | tmul c x =>
    refine ⟨c.re • x, c.im • x, ?_⟩
    rw [← smul_tmul, ← smul_tmul, ← add_tmul]
    congr 1
    apply Complex.ext <;> simp
  | add u v hu hv =>
    obtain ⟨x, y, rfl⟩ := hu
    obtain ⟨x', y', rfl⟩ := hv
    refine ⟨x + x', y + y', ?_⟩
    simp only [tmul_add]
    abel

/-- Complex scalar extension of the actual trace inclusion. -/
def traceComplexification : ℂ ⊗[ℝ] h.TraceSpace →ₗ[ℂ]
    ((σ : K →+* ℂ) → ComplexFiber M σ) := h.traceInclusion.liftBaseChange ℂ

omit [NumberField K] [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M] in
@[simp]
lemma traceComplexification_tmul (c : ℂ) (x : h.TraceSpace) :
    h.traceComplexification (c ⊗ₜ[ℝ] x) = c • h.traceInclusion x := rfl

/-- Imaginary pairing detects the imaginary component of a complexified vector. -/
lemma sum_inner_im_real_add_I (x y : h.TraceSpace) :
    (∑ σ, (h.fiber σ).inner (h.traceInclusion y σ)
      (h.traceInclusion x σ + Complex.I • h.traceInclusion y σ)).im = ‖y‖ ^ 2 := by
  let : ∀ σ : K →+* ℂ, InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber
  have he : (∑ σ, (h.fiber σ).inner (h.traceInclusion y σ)
      (h.traceInclusion x σ + Complex.I • h.traceInclusion y σ)) =
      (inner ℝ y x : ℂ) + Complex.I * (inner ℝ y y : ℂ) := by
    simp only [h.ofReal_trace_inner, InnerProductSpace.Core.inner_add_right,
      InnerProductSpace.Core.inner_smul_right, Finset.sum_add_distrib, Finset.mul_sum]
  rw [he]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, mul_zero, one_mul, zero_add]
  exact real_inner_self_eq_norm_sq y

/-- The actual trace space has no hidden complex linear relations. -/
lemma traceComplexification_injective : Function.Injective h.traceComplexification := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro z hz
  change z = 0
  change h.traceComplexification z = 0 at hz
  obtain ⟨x, y, rfl⟩ := h.complex_tensor_decompose z
  have he : h.traceInclusion x + Complex.I • h.traceInclusion y = 0 := by
    simpa using hz
  have hy : y = 0 := by
    let : ∀ σ : K →+* ℂ, InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber
    have hs := h.sum_inner_im_real_add_I x y
    have hzσ (σ : K →+* ℂ) : h.traceInclusion x σ +
        Complex.I • h.traceInclusion y σ = 0 := congrFun he σ
    simp only [hzσ, InnerProductSpace.Core.inner_zero_right, Finset.sum_const_zero,
      Complex.zero_im] at hs
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg y])
  have hx : x = 0 := by
    rw [hy, map_zero, smul_zero, add_zero] at he
    have hinj : Function.Injective h.traceInclusion := (archimedeanSpan M).subtype_injective
    apply hinj
    simpa only [map_zero] using he
  simp [hx, hy]

/-- Every complex fiber family comes from complexification of the trace space. -/
lemma traceComplexification_bijective : Function.Bijective h.traceComplexification := by
  refine ⟨h.traceComplexification_injective, ?_⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp
    h.traceComplexification_injective
  rw [Module.finrank_baseChange, h.traceSpace_finrank, Module.finrank_pi_fintype]
  simp [complexFiber_finrank, NumberField.Embeddings.card]

include h in
/-- Conjugation compatibility characterizes the actual real span of integral sections. -/
theorem mem_archimedeanSpan_iff_conjugate (z : (σ : K →+* ℂ) → ComplexFiber M σ) :
    z ∈ archimedeanSpan M ↔
      ∀ σ, fiberConjugate M σ (z σ) = z (ComplexEmbedding.conjugate σ) := by
  constructor
  · intro hz
    exact h.traceInclusion_conjugate ⟨z, hz⟩
  · intro hz
    obtain ⟨w, hw⟩ := h.traceComplexification_bijective.surjective z
    obtain ⟨x, y, rfl⟩ := h.complex_tensor_decompose w
    have he : h.traceInclusion x + Complex.I • h.traceInclusion y = z := by
      simpa using hw
    have hy : y = 0 := by
      have hs := h.sum_inner_im_real_add_I x y
      have hr := h.sum_inner_im_eq_zero_of_conjugate (h.traceInclusion y) z
        (h.traceInclusion_conjugate y) hz
      have hzσ (σ : K →+* ℂ) : h.traceInclusion x σ +
          Complex.I • h.traceInclusion y σ = z σ := congrFun he σ
      simp only [hzσ, hr] at hs
      exact norm_eq_zero.mp (by nlinarith [norm_nonneg y])
    rw [hy, map_zero, smul_zero, add_zero] at he
    exact he ▸ x.property

end BostConjecture.Arithmetic.HermitianMetric
