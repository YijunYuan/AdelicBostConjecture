module

public import BostConjecture.Arithmetic.Compactness.DegreeContinuity
public import BostConjecture.Arithmetic.TensorCompatibility

/-!
# Continuity of actual Hilbert tensor metrics

Finite tensor Gram coefficients are products of factor Gram coefficients.
This proves continuity on the existing intrinsic metric spaces.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace BostConjecture.Arithmetic.HermitianMetric

universe u
variable {K : Type*} [Field K] [NumberField K]
variable {M N : Type u} [AddCommGroup M] [Module (𝓞 K) M]
    [AddCommGroup N] [Module (𝓞 K) N]
    [Module.Finite (𝓞 K) M] [Module.Finite (𝓞 K) N]

/-- Hilbert tensor product varies continuously with its two actual metrics. -/
theorem continuous_tensor : Continuous
    (fun p : HermitianMetric (K := K) M × HermitianMetric (K := K) N =>
      p.1.tensor p.2) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro σ
  apply continuous_pi
  intro x
  apply continuous_pi
  intro y
  change Continuous (fun p : HermitianMetric (K := K) M × HermitianMetric (K := K) N =>
    ((p.1.tensor p.2).fiber σ).inner x y)
  let : Module.Finite ℂ (ComplexFiber M σ) := by dsimp [ComplexFiber]; infer_instance
  let : Module.Finite ℂ (ComplexFiber N σ) := by dsimp [ComplexFiber]; infer_instance
  let b := Module.finBasis ℂ (ComplexFiber M σ)
  let c := Module.finBasis ℂ (ComplexFiber N σ)
  let d := (b.tensorProduct c).map (binaryTensorFiberEquiv σ).symm
  have he (h : HermitianMetric (K := K) M) (g : HermitianMetric (K := K) N)
      (i j) : ((h.tensor g).fiber σ).inner (d i) (d j) =
        (h.fiber σ).inner (b i.1) (b j.1) *
          (g.fiber σ).inner (c i.2) (c j.2) := by
    rcases i with ⟨i₁, i₂⟩
    rcases j with ⟨j₁, j₂⟩
    rw [tensor_inner]
    simp only [d, Module.Basis.map_apply, LinearEquiv.apply_symm_apply,
      Module.Basis.tensorProduct_apply, Tensor.binaryCore_inner_tmul]
  have hform : (fun p : HermitianMetric (K := K) M × HermitianMetric (K := K) N =>
      ((p.1.tensor p.2).fiber σ).inner x y) = (fun p => ∑ i, ∑ j,
      star (d.repr x i) * (d.repr y j *
        ((p.1.fiber σ).inner (b i.1) (b j.1) *
          (p.2.fiber σ).inner (c i.2) (c j.2)))) := by
    funext p
    rw [fiber_inner_eq_sum _ σ d]
    simp only [he]
  rw [hform]
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  exact continuous_const.mul (continuous_const.mul
    (((continuous_inner_eval σ (b i.1) (b j.1)).comp continuous_fst).mul
      ((continuous_inner_eval σ (c i.2) (c j.2)).comp continuous_snd)))

/-- The maximum saturated tensor degree is continuous in both factors. -/
theorem continuous_tensor_maxDegree [Module.Projective (𝓞 K) M]
    [Module.Projective (𝓞 K) N] : Continuous
    (fun p : HermitianMetric (K := K) M × HermitianMetric (K := K) N =>
      (p.1.tensor p.2).maxDegree) :=
  continuous_maxDegree.comp continuous_tensor

end BostConjecture.Arithmetic.HermitianMetric
