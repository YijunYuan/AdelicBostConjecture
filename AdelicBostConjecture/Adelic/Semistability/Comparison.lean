/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Supermodular
public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.General.Semistability
public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Hermitian.Semistability
public import ArakelovGeometry.AdelicVectorBundle.Subquotient.EquivalencePullback

/-!
# Hermitian semistability in arbitrary carrier universes

The source HN predicate agrees with mean-slope semistability. We transport the
modified-degree identity through a completed isometry to apply the upstream
Hermitian comparison without restricting the carrier universe.
-/

@[expose] public section

noncomputable section

namespace ArakelovGeometry.AdelicVectorBundle

universe u

variable {K : Type u} [Field K] {S : AdelicStructure K} [S.IsProper]
  [S.NormMeasurabilityHypotheses] [S.IsArchimedeanNormalized]

/-- Completed isometries preserve the modified mean slope across carrier universes. -/
theorem hnMeanSlope_eq_of_completed_isometry (V : AdelicVectorBundle S)
    (W : AdelicVectorBundle S) (e : V ≃ₗ[K] W)
    (he : ∀ ω x, W.norm ω (e.toLinearMap.baseChange (S.ϕ ω).Completion x) = V.norm ω x) :
    V.hnMeanSlope = W.hnMeanSlope := by
  have hinv (ω : S.Ω) (x) :
      V.norm ω (e.symm.toLinearMap.baseChange (S.ϕ ω).Completion x) = W.norm ω x := by
    let eω := e.baseChange K (S.ϕ ω).Completion V W
    have h := he ω (eω.symm x)
    change W.norm ω (eω (eω.symm x)) = V.norm ω (eω.symm x) at h
    rw [LinearEquiv.apply_symm_apply] at h
    dsimp only [eω] at h
    simpa only [← LinearEquiv.coe_baseChange, LinearEquiv.coe_coe,
      LinearEquiv.baseChange_symm] using h.symm
  have hforward := V.hnDegree_le_of_bijective_of_mapHeight_le W e.toLinearMap e.bijective 0
    (V.mapHeight_le_zero_of_completed_contraction W e.toLinearMap (fun ω x ↦ (he ω x).le))
  have hbackward := W.hnDegree_le_of_bijective_of_mapHeight_le V e.symm.toLinearMap
    e.symm.bijective 0
    (W.mapHeight_le_zero_of_completed_contraction V e.symm.toLinearMap
      (fun ω x ↦ (hinv ω x).le))
  have hd : V.hnDegree = W.hnDegree := by
    apply le_antisymm
    · simpa only [mul_zero, add_zero] using hforward
    · simpa only [mul_zero, add_zero] using hbackward
  simp only [hnMeanSlope, hd, e.finrank_eq]

/-- Hermitian source semistability is mean-slope semistability in every carrier universe. -/
theorem isSemistable_iff_isMeanSlopeSemistable (V : AdelicVectorBundle S)
    [V.IsHermitian] : V.IsSemistable ↔ V.IsMeanSlopeSemistable := by
  let e : ULift.{u} V ≃ₗ[K] V := ULift.moduleEquiv
  let W := V.pullbackEquiv e
  have hm := hnMeanSlope_eq_of_completed_isometry W V e (fun _ _ ↦ rfl)
  have hs := slope_eq_of_completed_isometry W V e (fun _ _ ↦ rfl)
  have he : V.hnMeanSlope = V.slope :=
    hm.symm.trans (W.hnMeanSlope_eq_slope_of_isHermitian.trans hs)
  by_cases hr : 0 < Module.finrank K V
  · rw [V.isSemistable_iff_hnMeanSlope_eq_minimalSlope hr, he,
      V.isMeanSlopeSemistable_iff_minimalSlope_eq_slope_of_isHermitian hr]
    exact eq_comm
  · exact ⟨fun h ↦ (hr h.rank_pos).elim, fun h ↦ (hr h.rank_pos).elim⟩

end ArakelovGeometry.AdelicVectorBundle
