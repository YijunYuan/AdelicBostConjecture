module

public import BostConjecture.Arithmetic.Compactness.MetricTopology
public import BostConjecture.Arithmetic.RestrictionCovolume.RealForm
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Complex coordinates of actual arithmetic trace frames

An integer basis of the original module extends to a complex basis of the
product of its actual fibers. The direct sum of the Hermitian pairings has
the real trace Gram matrix in that basis. This is the reconstruction route
from a nondegenerate limit of real frames to actual Hermitian fiber metrics.

Reference: bost_specht_manuscript.pdf, page 11, Lemma 7.1.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct Matrix
open scoped Classical

namespace BostConjecture.Arithmetic.HermitianMetric

variable {K : Type*} [Field K] [NumberField K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]
variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
variable {ι : Type*}

/-- The actual complexification equivalence, with no coordinate-model fibers. -/
def traceComplexEquiv (h : HermitianMetric (K := K) M) :
    ℂ ⊗[ℝ] h.TraceSpace ≃ₗ[ℂ] ((σ : K →+* ℂ) → ComplexFiber M σ) :=
  LinearEquiv.ofBijective h.traceComplexification h.traceComplexification_bijective

/-- Simultaneous integral sections form a complex basis of all actual fibers. -/
def complexTraceBasis (h : HermitianMetric (K := K) M) (b : Module.Basis ι ℤ M) :
    Module.Basis ι ℂ ((σ : K →+* ℂ) → ComplexFiber M σ) :=
  ((h.traceBasis b).baseChange ℂ).map h.traceComplexEquiv

@[simp]
lemma complexTraceBasis_apply (h : HermitianMetric (K := K) M)
    (b : Module.Basis ι ℤ M) (i : ι) (σ : K →+* ℂ) :
    h.complexTraceBasis b i σ = fiberSection M σ (b i) := by
  simp only [complexTraceBasis, Module.Basis.map_apply, Module.Basis.baseChange_apply,
    traceComplexEquiv, LinearEquiv.ofBijective_apply, traceComplexification_tmul,
    one_smul, traceBasis_apply, traceInclusion_section]

omit [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M] in
/-- The genuine direct sum of the actual fiber forms. -/
@[instance_reducible]
def fiberProductCore (h : HermitianMetric (K := K) M) :
    InnerProductSpace.Core ℂ ((σ : K →+* ℂ) → ComplexFiber M σ) where
  inner x y := ∑ σ, (h.fiber σ).inner (x σ) (y σ)
  conj_inner_symm x y := by simp only [map_sum, (h.fiber _).conj_inner_symm]
  re_inner_nonneg x := by
    change 0 ≤ (∑ σ, (h.fiber σ).inner (x σ) (x σ)).re
    rw [Complex.re_sum]
    exact Finset.sum_nonneg fun σ _ => (h.fiber σ).re_inner_nonneg _
  add_left x y z := by simp only [Pi.add_apply, (h.fiber _).add_left, Finset.sum_add_distrib]
  smul_left x y c := by
    simp only [Pi.smul_apply, (h.fiber _).smul_left, Finset.mul_sum]
  definite x hx := by
    funext σ
    have hr : ∑ τ, ((h.fiber τ).inner (x τ) (x τ)).re = 0 := by
      simpa only [Complex.re_sum, Complex.zero_re] using congrArg Complex.re hx
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun τ _ => (h.fiber τ).re_inner_nonneg _)).mp hr σ (Finset.mem_univ σ)
    apply (h.fiber σ).definite
    apply Complex.ext hz
    let := h.fiber σ
    exact InnerProductSpace.Core.inner_self_im (𝕜 := ℂ) _

/-- The product Hermitian Gram matrix in simultaneous integral coordinates
is precisely the real trace Gram matrix, viewed over the complex numbers. -/
lemma fiberProductCore_basis (h g : HermitianMetric (K := K) M)
    (b : Module.Basis ι ℤ M) (i j : ι) :
    g.fiberProductCore.inner (h.complexTraceBasis b i) (h.complexTraceBasis b j) =
      (inner ℝ (g.traceSection (b i)) (g.traceSection (b j)) : ℂ) := by
  change (∑ σ, (g.fiber σ).inner _ _) = _
  simp only [complexTraceBasis_apply]
  exact (g.ofReal_trace_inner (g.traceSection (b i)) (g.traceSection (b j))).symm

end BostConjecture.Arithmetic.HermitianMetric
