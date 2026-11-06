module

public import BostConjecture.Main.TensorSemistability.Extensions
public import BostConjecture.Arithmetic.TensorCompatibility

/-! # Uniform rescaling of the actual Hilbert tensor metric -/

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace BostConjecture.Arithmetic.HermitianMetric

universe u
variable {K M N : Type u} [Field K] [NumberField K]
    [AddCommGroup M] [Module (𝓞 K) M]
    [AddCommGroup N] [Module (𝓞 K) N]

/-- Rescaling the two factor norms multiplies the tensor norm by their product. -/
theorem tensor_rescale (h : HermitianMetric (K := K) M)
    (k : HermitianMetric (K := K) N) (a b : ℝ) :
    (h.rescale a).tensor (k.rescale b) = (h.tensor k).rescale (a + b) := by
  apply ext_inner
  intro σ x y
  apply Tensor.inner_ext_of_span
    (fun xy : M × N => fiberSection _ σ (xy.1 ⊗ₜ[𝓞 K] xy.2))
    (span_fiberSection_tmul σ) (((h.rescale a).tensor (k.rescale b)).fiber σ)
    (((h.tensor k).rescale (a + b)).fiber σ) LinearMap.id LinearMap.id _ x y
  intro v w
  simp only [LinearMap.id_apply, tensor_inner_section, rescale_inner]
  rw [mul_add, Real.exp_add, Complex.ofReal_mul]
  ring

end BostConjecture.Arithmetic.HermitianMetric
