module

public import BostConjecture.Specht.BulkGap
public import BostConjecture.Specht.GapAsymptotics
public import BostConjecture.Specht.PrefixEvent

/-!
# Uniform separation of rectangular prefix occupancies
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Specht

open Finset Filter
open scoped Topology

/-- Bounded gaps have probability tending to zero uniformly over bulk prefix times,
under the actual normalized weighted occupancy law. -/
theorem occupancyGapProbability_uniform {a : ℕ} (ha : 2 ≤ a) {ε : ℝ} (hε : 0 < ε)
    (L : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℕ, ∀ k ≥ K, ∀ m l : ℕ, m + l = a * k →
      ε * (a * k : ℕ) ≤ m → ε * (a * k : ℕ) ≤ l →
      occupancyGapProbability a (k + a - 1) (m + staircaseSum a) L < δ := by
  let c := staircaseSum a
  let r : ℝ := 1 / 2 + 1 / (4 * (c : ℝ))
  let C : ℝ := (a.factorial : ℝ) * (∏ j ∈ range a, (j.factorial : ℝ)) *
    (ε / a) ^ (2 * c)
  have ha0 : 0 < a := by omega
  have hC : 0 < C := by dsimp [C]; positivity
  have hr := gap_cutoff_exponent (staircaseSum_pos ha)
  have hlim := (tendsto_gap_majorant ha0 hC L hr.1 hr.2).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hδ))
  refine ⟨max K 1, ?_⟩
  intro k hk m l hml hm hl
  have hk0 : 0 < k := by omega
  have hu : 0 < (k : ℝ) ^ r := Real.rpow_pos_of_pos (by positivity) r
  exact (occupancyGapProbability_bulk_le ha hk0 m l hml hε hm hl L hu).trans_lt
    (hK k (by omega))

/-- Uniform bulk separation for the prefixes of actual uniform standard rectangular tableaux. -/
theorem rectanglePrefixGapProbability_uniform {a : ℕ} (ha : 2 ≤ a)
    {ε : ℝ} (hε : 0 < ε) (L : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℕ, ∀ k ≥ K, ∀ m l : ℕ, m + l = a * k →
      ε * (a * k : ℕ) ≤ m → ε * (a * k : ℕ) ≤ l →
      rectanglePrefixGapProbability a k m l L < δ := by
  obtain ⟨K, hK⟩ := occupancyGapProbability_uniform ha hε L hδ
  refine ⟨max K 1, ?_⟩
  intro k hk m l hml hm hl
  rw [rectanglePrefixGapProbability_eq a (by omega : 0 < k) m l hml L]
  exact hK k (by omega) m l hml hm hl

end BostConjecture.Specht
