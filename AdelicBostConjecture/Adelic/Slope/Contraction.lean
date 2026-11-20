/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Hermitian.Semistability
public import ArakelovGeometry.AdelicVectorBundle.Slope.LinearMap
public import ArakelovGeometry.AdelicVectorBundle.Degree.Supermodular

/-!
# Comparing semistable slopes by a completed contraction

The nonzero-map slope inequality and the nonpositive height of a completed
contraction compare actual mean slopes. Only the source needs to be Hermitian.
-/

@[expose] public section

namespace ArakelovGeometry.AdelicVectorBundle

universe u v w w'

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K} [S.IsProper]

/-- A nonzero completed contraction between mean-slope semistable adelic
bundles compares their actual real slopes. Hermitianity is needed only for
the source's minimal-slope characterization of semistability. -/
theorem slope_le_of_nonzero_completed_contraction
    (V : AdelicVectorBundle S) (W : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    [hV : V.IsHermitian]
    [hVS : V.IsMeanSlopeSemistable] [hWS : W.IsMeanSlopeSemistable]
    (f : V →ₗ[K] W) (hf : f ≠ 0)
    (hcontract : ∀ ω x, W.norm ω (f.baseChange (S.ϕ ω).Completion x) ≤ V.norm ω x) :
    V.slope ≤ W.slope := by
  have hmin := (V.isMeanSlopeSemistable_iff_minimalSlope_eq_slope_of_isHermitian
       hVS.1).mp hVS
  have hmax := (W.isMeanSlopeSemistable_iff_maximalSlope_eq_slope hWS.1).mp hWS
  have hmap := V.minimalSlope_le_maximalSlope_add_mapHeight_of_ne_zero W f hf
  have hheight := V.mapHeight_le_zero_of_completed_contraction W f hcontract
  rw [hmin, hmax] at hmap
  apply EReal.coe_le_coe_iff.mp
  calc
    (V.slope : EReal) ≤ (W.slope : EReal) + V.mapHeight W f := hmap
    _ ≤ (W.slope : EReal) + 0 := add_le_add le_rfl hheight
    _ = (W.slope : EReal) := add_zero _

end ArakelovGeometry.AdelicVectorBundle
