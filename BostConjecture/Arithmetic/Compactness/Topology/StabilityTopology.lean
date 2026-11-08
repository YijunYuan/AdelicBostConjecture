/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Compactness.Topology.MetricTopology
public import BostConjecture.Arithmetic.Compactness.Topology.Stability

/-!
# Openness of normalized strict stability

The arithmetic uniform degree gap and the actual metric topology prove that
strict stability is open among metrics of degree zero.

Reference: this paper, page 12.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct Filter
open scoped Topology

namespace BostConjecture.Arithmetic.HermitianMetric

variable {K : Type*} [Field K] [NumberField K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]
variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]

/-- A normalized strictly stable metric has a neighborhood whose normalized
members remain strictly stable. -/
theorem IsStable.eventually_isStable_normalized {h : HermitianMetric K M}
    (hs : h.IsStable) (h0 : h.degree = 0) :
    ∀ᶠ g in 𝓝 h, g.degree = 0 → g.IsStable := by
  obtain ⟨δ, hδ, hgap⟩ := hs.exists_degree_gap h0
  obtain ⟨t, ht, hsmall⟩ := exists_pos_mul_lt hδ
    (Module.finrank K (K ⊗[𝓞 K] M) : ℝ)
  filter_upwards [h.eventually_all_fiberNorm_compare ht] with g hg hg0
  exact isStable_of_fiberNorm_compare hgap ht.le hsmall hg0
    (fun σ x => (hg σ x).1) (fun σ x => (hg σ x).2)

end BostConjecture.Arithmetic.HermitianMetric
