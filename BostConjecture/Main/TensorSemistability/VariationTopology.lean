/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Main.TensorSemistability.ExponentialVariation
public import BostConjecture.Arithmetic.Compactness.Topology.MetricTopology
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# Admissible neighborhoods along actual exponential metric variations

The exponential metric curve is continuous in the topology of actual fiber
forms. Strict stability remains valid near zero for a traceless compatible
generator family. Reference: this paper, page 13.
-/

@[expose] public section

noncomputable section

open NumberField Filter
open scoped Topology

namespace BostConjecture.Arithmetic.HermitianMetric

variable {K : Type*} [Field K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M] [Module.Finite (𝓞 K) M]

/-- Compatible exponential curves are continuous in the actual metric topology. -/
theorem continuous_exponentialVariation (h : HermitianMetric K M)
    (A : ∀ σ : K →+* ℂ, Module.End ℂ (ComplexFiber M σ))
    (hs : ∀ σ x y, (h.fiber σ).inner (A σ x) y = (h.fiber σ).inner x (A σ y))
    (hc : ∀ σ x, A (ComplexEmbedding.conjugate σ) (fiberConjugate M σ x) =
      fiberConjugate M σ (A σ x)) :
    Continuous (h.exponentialVariation A hs hc) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro σ
  apply continuous_pi
  intro x
  apply continuous_pi
  intro y
  let : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
  let := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
  let : NormedSpace ℂ (ComplexFiber M σ) := inferInstance
  let : NormedRing (ComplexFiber M σ →L[ℂ] ComplexFiber M σ) := inferInstance
  let := FiniteDimensional.complete ℂ (ComplexFiber M σ)
  have he : Continuous (NormedSpace.exp :
      (ComplexFiber M σ →L[ℂ] ComplexFiber M σ) → _) := by
    rw [← continuousOn_univ, ← Metric.eball_top_eq_univ (0 :
      ComplexFiber M σ →L[ℂ] ComplexFiber M σ), ←
      NormedSpace.expSeries_radius_eq_top ℂ (ComplexFiber M σ →L[ℂ] ComplexFiber M σ)]
    exact NormedSpace.continuousOn_exp
  have hf (z : ComplexFiber M σ) : Continuous (fun t : ℝ =>
      NormedSpace.exp (t • LinearMap.toContinuousLinearMap (A σ)) z) :=
    (he.comp (continuous_id.smul continuous_const)).clm_apply continuous_const
  exact (hf x).inner (hf y)

end BostConjecture.Arithmetic.HermitianMetric
