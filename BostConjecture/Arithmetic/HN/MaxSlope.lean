/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.HN.Semistable
public import BostConjecture.Arithmetic.Compactness.Maximum.Degree
public import BostConjecture.Slope.DedekindCut

/-!
# Maximal Hermitian slope from the subspace payoff

The definition takes the real value of the payoff's `max ⊤`. The ambient slope
bounds this cut below, and arithmetic degree finiteness bounds it above by
`maxDegree`. Neither the definition nor these bounds use a Hermitian HN flag.
Attainment by the first HN term is proved separately in `HN/Filtration.lean`.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct HarderNarasimhan

namespace BostConjecture.Arithmetic.HermitianMetric

variable {K : Type*} [Field K] [NumberField K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]
variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
variable [Nontrivial (K ⊗[𝓞 K] M)]

/-- Maximal Hermitian slope, as the real value of the subspace payoff's supremum. -/
def maxSlope (h : HermitianMetric (K := K) M) : ℝ :=
  ((BostConjecture.Subspace.slope h.subspaceDegree).max ⊤).toReal

/-- Arithmetic degree finiteness bounds the slope supremum, without an HN filtration. -/
theorem subspaceSlope_max_le_maxDegree (h : HermitianMetric (K := K) M) :
    (BostConjecture.Subspace.slope h.subspaceDegree).max ⊤ ≤
      DedekindCut.principal h.maxDegree := by
  apply PayoffFunction.max_le
  intro X hX
  change BostConjecture.Subspace.slope h.subspaceDegree ⟨⊥, X, hX.1⟩ ≤ _
  rw [h.subspaceSlope_apply_bot, DedekindCut.principal_le_principal,
    ← subspaceDegree_div_finrank]
  have hr : 0 < Module.finrank K X := by
    simpa using Submodule.finrank_strictMono hX.1
  apply (div_le_iff₀ (by exact_mod_cast hr)).mpr
  exact (h.degree_le_maxDegree (integralPart X)).trans
    (le_mul_of_one_le_right h.maxDegree_nonneg (by exact_mod_cast hr))

/-- The real maximal slope represents exactly the cut supplied by the payoff API. -/
theorem subspaceSlope_max_eq (h : HermitianMetric (K := K) M) :
    (BostConjecture.Subspace.slope h.subspaceDegree).max ⊤ =
      DedekindCut.principal h.maxSlope := by
  apply (DedekindCut.principal_toReal_of_bounds (a := h.slope)
    ?_ h.subspaceSlope_max_le_maxDegree).symm
  rw [← h.subspaceSlope_top]
  exact PayoffFunction.apply_le_max

/-- The supremum of initial slopes bounds the degree of every generic subspace. -/
theorem subspaceDegree_le_maxSlope (h : HermitianMetric (K := K) M)
    (X : Submodule K (K ⊗[𝓞 K] M)) :
    h.subspaceDegree X ≤ h.maxSlope * Module.finrank K X := by
  by_cases hX : X = ⊥
  · subst X
    simp
  have ht : ⊥ < X := bot_lt_iff_ne_bot.mpr hX
  have hs := PayoffFunction.le_max (μ := BostConjecture.Subspace.slope h.subspaceDegree)
    (I := ⊤) (u := X) ⟨ht, le_top⟩
  change BostConjecture.Subspace.slope h.subspaceDegree ⟨⊥, X, ht⟩ ≤ _ at hs
  rw [h.subspaceSlope_apply_bot, h.subspaceSlope_max_eq,
    DedekindCut.principal_le_principal, ← subspaceDegree_div_finrank] at hs
  have hr : 0 < Module.finrank K X := by
    simpa using Submodule.finrank_strictMono ht
  exact (div_le_iff₀ (by exact_mod_cast hr)).mp hs

/-- Every positive-rank integral submodule has slope at most the supremum. -/
theorem slope_submodule_le_maxSlope (h : HermitianMetric (K := K) M)
    (P : Submodule (𝓞 K) M) (hP : 0 < Module.finrank K (K ⊗[𝓞 K] P)) :
    (h.submodule P).slope ≤ h.maxSlope := by
  apply (h.slope_le_saturation P).trans
  rw [← subspaceDegree_div_finrank]
  have hr : 0 < Module.finrank K (P.baseChange K) :=
    (Submodule.toBaseChange.toLinearEquiv K P).finrank_eq ▸ hP
  exact (div_le_iff₀ (by exact_mod_cast hr)).mpr (h.subspaceDegree_le_maxSlope _)

/-- The ambient slope is bounded by the supremum of submodule slopes. -/
lemma slope_le_maxSlope (h : HermitianMetric (K := K) M) : h.slope ≤ h.maxSlope := by
  apply DedekindCut.principal_le_principal.mp
  rw [← h.subspaceSlope_top, ← h.subspaceSlope_max_eq]
  exact PayoffFunction.apply_le_max

/-- Intrinsic semistability is equality of average and maximal slopes. -/
theorem isSemistable_iff_maxSlope_eq (h : HermitianMetric (K := K) M) :
    h.IsSemistable ↔ h.maxSlope = h.slope := by
  constructor
  · intro hs
    apply le_antisymm ?_ h.slope_le_maxSlope
    apply DedekindCut.principal_le_principal.mp
    rw [← h.subspaceSlope_max_eq]
    apply PayoffFunction.max_le
    intro X hX
    change BostConjecture.Subspace.slope h.subspaceDegree ⟨⊥, X, hX.1⟩ ≤ _
    rw [h.subspaceSlope_apply_bot, DedekindCut.principal_le_principal]
    exact (h.isSemistable_iff_subspaces.mp hs) X hX.1
  · intro he P hP
    exact (h.slope_submodule_le_maxSlope P hP).trans_eq he

end BostConjecture.Arithmetic.HermitianMetric
