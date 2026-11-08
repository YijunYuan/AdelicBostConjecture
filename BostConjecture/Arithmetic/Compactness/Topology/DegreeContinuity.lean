/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Compactness.Topology.MetricTopology
public import BostConjecture.Arithmetic.Compactness.Maximum.Comparison

/-!
# Continuity of intrinsic degree and maximum degree

The actual topology of Hermitian forms yields uniform exponential norm bounds.
The previously proved rank-sharp comparison then gives continuity, including
for nonfree projective modules and in generic rank zero.

Reference: this paper, pages 11–12.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct Filter
open scoped Topology

namespace BostConjecture.Arithmetic.HermitianMetric

variable {K : Type*} [Field K] [NumberField K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]
variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]

/-- Intrinsic arithmetic degree is continuous in the actual fiber forms. -/
theorem continuous_degree :
    Continuous (fun h : HermitianMetric K M => h.degree) := by
  apply continuous_iff_continuousAt.mpr
  intro h
  apply Metric.continuousAt_iff'.mpr
  intro ε hε
  obtain ⟨t, ht, hsmall⟩ := exists_pos_mul_lt hε
    (Module.finrank K (K ⊗[𝓞 K] M) : ℝ)
  filter_upwards [h.eventually_all_fiberNorm_compare ht] with g hg
  simpa only [Real.dist_eq] using (h.abs_degree_sub_le_of_fiberNorm_le g t
    (fun σ x => (hg σ x).1) (fun σ x => (hg σ x).2)).trans_lt hsmall

/-- The attained maximum saturated degree is continuous in the actual metrics. -/
theorem continuous_maxDegree :
    Continuous (fun h : HermitianMetric K M => h.maxDegree) := by
  apply continuous_iff_continuousAt.mpr
  intro h
  apply Metric.continuousAt_iff'.mpr
  intro ε hε
  obtain ⟨t, ht, hsmall⟩ := exists_pos_mul_lt hε
    (Module.finrank K (K ⊗[𝓞 K] M) : ℝ)
  filter_upwards [h.eventually_all_fiberNorm_compare ht] with g hg
  simpa only [Real.dist_eq] using (h.abs_maxDegree_sub_le_of_fiberNorm_le g ht.le
    (fun σ x => (hg σ x).1) (fun σ x => (hg σ x).2)).trans_lt hsmall

omit [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M] in
/-- Taking the induced metric on a fixed integral submodule is continuous. -/
theorem continuous_submodule (P : Submodule (𝓞 K) M) :
    Continuous (fun h : HermitianMetric K M => h.submodule P) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro σ
  apply continuous_pi
  intro x
  apply continuous_pi
  exact fun y => continuous_inner_eval σ (fiberMap P.subtype σ x) (fiberMap P.subtype σ y)

end BostConjecture.Arithmetic.HermitianMetric
