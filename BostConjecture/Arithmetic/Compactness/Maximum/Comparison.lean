/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Compactness.Maximum.Degree
public import BostConjecture.Arithmetic.Compactness.Topology.MetricComparison

/-!
# Metric comparison of the maximum degree

The uniform estimate for all induced degrees passes to the actual attained
maximum. Its bound uses the ambient generic rank for every submodule.

Reference: this paper, page 12.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace BostConjecture.Arithmetic.HermitianMetric

variable {K : Type*} [Field K] [NumberField K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]
variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]

/-- Every induced degree satisfies the estimate with the ambient rank. -/
theorem abs_degree_submodule_sub_le_rank_mul
    (h g : HermitianMetric (K := K) M) {t : ℝ} (ht : 0 ≤ t)
    (hgh : ∀ (σ : K →+* ℂ) (x : ComplexFiber M σ),
      g.fiberNorm σ x ≤ Real.exp t * h.fiberNorm σ x)
    (hhg : ∀ (σ : K →+* ℂ) (x : ComplexFiber M σ),
      h.fiberNorm σ x ≤ Real.exp t * g.fiberNorm σ x)
    (P : Submodule (𝓞 K) M) :
    |(g.submodule P).degree - (h.submodule P).degree| ≤
      (Module.finrank K (K ⊗[𝓞 K] M) : ℝ) * t := by
  apply (h.abs_degree_submodule_sub_le_of_fiberNorm_le g t hgh hhg P).trans
  apply mul_le_mul_of_nonneg_right _ ht
  exact_mod_cast ((Submodule.toBaseChange.toLinearEquiv K P).finrank_eq.trans_le
    (P.baseChange K).finrank_le)

/-- The maximum degree changes by at most ambient rank times the logarithmic
distortion of the actual fiber norms. -/
theorem abs_maxDegree_sub_le_of_fiberNorm_le
    (h g : HermitianMetric (K := K) M) {t : ℝ} (ht : 0 ≤ t)
    (hgh : ∀ (σ : K →+* ℂ) (x : ComplexFiber M σ),
      g.fiberNorm σ x ≤ Real.exp t * h.fiberNorm σ x)
    (hhg : ∀ (σ : K →+* ℂ) (x : ComplexFiber M σ),
      h.fiberNorm σ x ≤ Real.exp t * g.fiberNorm σ x) :
    |g.maxDegree - h.maxDegree| ≤
      (Module.finrank K (K ⊗[𝓞 K] M) : ℝ) * t := by
  obtain ⟨P, hP, heP⟩ := h.exists_degree_eq_maxDegree
  obtain ⟨Q, hQ, heQ⟩ := g.exists_degree_eq_maxDegree
  let := hP
  let := hQ
  have h₁ := abs_le.mp (h.abs_degree_submodule_sub_le_rank_mul g ht hgh hhg P)
  have h₂ := abs_le.mp (h.abs_degree_submodule_sub_le_rank_mul g ht hgh hhg Q)
  have h₃ := g.degree_le_maxDegree P
  have h₄ := h.degree_le_maxDegree Q
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end BostConjecture.Arithmetic.HermitianMetric
