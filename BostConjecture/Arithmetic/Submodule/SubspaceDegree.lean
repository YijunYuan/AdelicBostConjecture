/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Submodule.IntegralSubspace
public import BostConjecture.Arithmetic.Degree.Normalization
public import BostConjecture.Slope.Subspace
public import BostConjecture.Arithmetic.Submodule.Metric

/-!
# Intrinsic degree on the generic subspace lattice

The degree of a generic subspace is the proved determinant degree of its
actual saturated integral part with the induced metric. The payoff from the
abstract subspace API therefore has the actual Hermitian slope on intervals
starting at zero. Later modules prove its supermodularity and construct its
HN interval flag. Arithmetic degree finiteness is a separate result; none of
these conclusions is an assumption hidden in this definition.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace BostConjecture.Arithmetic.HermitianMetric

variable {K : Type*} [Field K] [NumberField K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]
variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]

/-- Intrinsic determinant degree of the actual integral part of a generic subspace. -/
def subspaceDegree (h : HermitianMetric K M)
    (X : Submodule K (K ⊗[𝓞 K] M)) : ℝ := (h.submodule (integralPart X)).degree

@[simp]
lemma subspaceDegree_bot (h : HermitianMetric K M) :
    h.subspaceDegree ⊥ = 0 := by
  apply degree_eq_zero_of_rank_zero
  rw [integralPart_generic_finrank]
  simp

omit [Module.Projective (𝓞 K) M] in
/-- The generic rank in this degree's denominator is the actual subspace dimension. -/
lemma subspaceDegree_div_finrank (h : HermitianMetric K M)
    (X : Submodule K (K ⊗[𝓞 K] M)) :
    h.subspaceDegree X / Module.finrank K X = (h.submodule (integralPart X)).slope := by
  rw [slope, integralPart_generic_finrank]
  rfl

/-- The actual arithmetic degree specializes the slope payoff to the Hermitian
slope of the saturated integral submodule on every interval from zero. -/
lemma subspaceSlope_apply_bot (h : HermitianMetric K M)
    (X : Submodule K (K ⊗[𝓞 K] M)) (hX : ⊥ < X) :
    BostConjecture.Subspace.slope h.subspaceDegree ⟨⊥, X, hX⟩ =
      DedekindCut.principal (h.submodule (integralPart X)).slope := by
  rw [BostConjecture.Subspace.slope_apply]
  simp [BostConjecture.Subspace.intervalRank, subspaceDegree_div_finrank]

end BostConjecture.Arithmetic.HermitianMetric
