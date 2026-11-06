module

public import BostConjecture.Arithmetic.Compactness.MetricTopology
public import BostConjecture.Arithmetic.Compactness.Stability

/-!
# Openness of normalized strict stability

The arithmetic uniform degree gap and the actual metric topology prove that
strict stability is open among metrics of degree zero.

Reference: bost_specht_manuscript.pdf, page 12.
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
theorem IsStable.eventually_isStable_normalized {h : HermitianMetric (K := K) M}
    (hs : h.IsStable) (h0 : h.degree = 0) :
    ∀ᶠ g in 𝓝 h, g.degree = 0 → g.IsStable := by
  obtain ⟨δ, hδ, hgap⟩ := hs.exists_degree_gap h0
  obtain ⟨t, ht, hsmall⟩ := exists_pos_mul_lt hδ
    (Module.finrank K (K ⊗[𝓞 K] M) : ℝ)
  filter_upwards [h.eventually_all_fiberNorm_compare ht] with g hg hg0
  exact isStable_of_fiberNorm_compare hgap ht.le hsmall hg0
    (fun σ x => (hg σ x).1) (fun σ x => (hg σ x).2)

/-- The strictly stable locus is open in the subspace of normalized actual metrics. -/
theorem isOpen_isStable_normalized :
    IsOpen {h : {h : HermitianMetric (K := K) M // h.degree = 0} | h.val.IsStable} := by
  apply isOpen_iff_mem_nhds.mpr
  intro h hh
  have he := hh.eventually_isStable_normalized h.property
  have ht := (continuous_subtype_val.continuousAt (x := h)).eventually he
  exact ht.mono fun g hg => hg g.property

end BostConjecture.Arithmetic.HermitianMetric
