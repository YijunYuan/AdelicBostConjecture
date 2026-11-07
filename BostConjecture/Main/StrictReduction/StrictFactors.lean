/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Main.StrictReduction.TensorExtension
public import BostConjecture.Main.StrictReduction.MinimalRank
public import BostConjecture.Arithmetic.Compactness.Topology.Stability

/-!
# Strict stability of factors at the least counterexample rank sum

A proper degree-zero saturated factor cut would give two smaller normalized
counterexample-free tensor products. The tensor extension theorem then rules
out positive tensor maximum degree.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace BostConjecture.Arithmetic

universe u
variable {K : Type*} [Field K] [NumberField K]

variable {M : Type u} [AddCommGroup M] [Module (𝓞 K) M]
    [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]

/-- A nonzero proper saturated cut has two positive generic ranks, each smaller
than the ambient rank. This uses torsion-freeness, without integral freeness. -/
theorem generic_ranks_of_saturated_proper
    (P : Submodule (𝓞 K) M) [Module.Projective (𝓞 K) (M ⧸ P)]
    (hPb : P ≠ ⊥) (hPt : P ≠ ⊤) :
    0 < Module.finrank K (K ⊗[𝓞 K] P) ∧
    0 < Module.finrank K (K ⊗[𝓞 K] (M ⧸ P)) ∧
    Module.finrank K (K ⊗[𝓞 K] P) < Module.finrank K (K ⊗[𝓞 K] M) ∧
    Module.finrank K (K ⊗[𝓞 K] (M ⧸ P)) < Module.finrank K (K ⊗[𝓞 K] M) := by
  have hp : 0 < Module.finrank K (K ⊗[𝓞 K] P) := by
    rw [(TensorProduct.isBaseChange (𝓞 K) P K).finrank_eq]
    exact Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hPb)
  have hq : 0 < Module.finrank K (K ⊗[𝓞 K] (M ⧸ P)) := by
    rw [(TensorProduct.isBaseChange (𝓞 K) (M ⧸ P) K).finrank_eq]
    exact Module.finrank_pos_iff.mpr (Submodule.Quotient.nontrivial_iff.mpr hPt)
  have hr := generic_finrank_submodule_quotient (K := K) P
  exact ⟨hp, hq, by omega, by omega⟩

namespace HermitianMetric

variable {N : Type u} [AddCommGroup N] [Module (𝓞 K) N]
    [Module.Finite (𝓞 K) N] [Module.Projective (𝓞 K) N]

/-- The first factor of a least-rank normalized counterexample is strictly
stable: a degree-zero cut contradicts normalized tensor extension closure. -/
theorem isStable_left_of_minimal_rank_sum
    (h : HermitianMetric K M) (g : HermitianMetric K N)
    (h0 : h.degree = 0) (g0 : g.degree = 0)
    (hs : h.IsSemistable) (gs : g.IsSemistable)
    (hrN : 0 < Module.finrank K (K ⊗[𝓞 K] N))
    (hbad : ¬ (h.tensor g).IsSemistable)
    (hmin : ∀ a' b' : ℕ, 0 < a' → 0 < b' →
      a' + b' < Module.finrank K (K ⊗[𝓞 K] M) + Module.finrank K (K ⊗[𝓞 K] N) →
      ∀ d ∈ Compactness.tensorMaxDegreeValues.{u} K a' b', d ≤ 0) :
    h.IsStable := by
  apply (h.isStable_iff_degree_neg h0).mpr
  intro P hP hPb hPt
  let := hP
  let : Module.FinitePresentation (𝓞 K) (M ⧸ P) :=
    Module.finitePresentation_of_finite (𝓞 K) _
  let : Module.Projective (𝓞 K) (M ⧸ P) :=
    Module.Flat.projective_of_finitePresentation
  have hle := (h.isSemistable_iff_degree_nonpos h0).mp hs P
  apply lt_of_le_of_ne hle
  intro hP0
  have hr := generic_ranks_of_saturated_proper P hPb hPt
  have hPs := hs.submodule_of_degree_zero h0 P hP0
  obtain ⟨hQ0, hQs⟩ := hs.quotient_of_degree_zero h0 P hP0
  have hPT := Compactness.isSemistable_tensor_of_smaller_rank_sum hmin
    (h.submodule P) g hr.1 hrN (Nat.add_lt_add_right hr.2.2.1 _)
    hP0 g0 hPs gs
  have hQT := Compactness.isSemistable_tensor_of_smaller_rank_sum hmin
    (h.quotient P) g hr.2.1 hrN (Nat.add_lt_add_right hr.2.2.2 _)
    hQ0 g0 hQs gs
  exact hbad (h.isSemistable_tensor_of_submodule_quotient g P hPT
    (by simp [degree_tensor, hP0, g0]) hQT (by simp [degree_tensor, hQ0, g0])).2

/-- Both factors are strictly stable at a least counterexample rank sum. The
second assertion uses the actual integral Hilbert tensor flip. -/
theorem isStable_factors_of_minimal_rank_sum
    (h : HermitianMetric K M) (g : HermitianMetric K N)
    (h0 : h.degree = 0) (g0 : g.degree = 0)
    (hs : h.IsSemistable) (gs : g.IsSemistable)
    (hrM : 0 < Module.finrank K (K ⊗[𝓞 K] M))
    (hrN : 0 < Module.finrank K (K ⊗[𝓞 K] N))
    (hbad : ¬ (h.tensor g).IsSemistable)
    (hmin : ∀ a' b' : ℕ, 0 < a' → 0 < b' →
      a' + b' < Module.finrank K (K ⊗[𝓞 K] M) + Module.finrank K (K ⊗[𝓞 K] N) →
      ∀ d ∈ Compactness.tensorMaxDegreeValues.{u} K a' b', d ≤ 0) :
    h.IsStable ∧ g.IsStable := by
  refine ⟨isStable_left_of_minimal_rank_sum h g h0 g0 hs gs hrN hbad hmin, ?_⟩
  apply isStable_left_of_minimal_rank_sum g h g0 h0 gs hs hrM
  · intro hgh
    exact hbad ((isSemistable_iff_of_equiv _ _ (TensorProduct.comm (𝓞 K) M N)
      (tensor_comm_inner h g)).mpr hgh)
  · simpa only [Nat.add_comm] using hmin

end HermitianMetric

end BostConjecture.Arithmetic
