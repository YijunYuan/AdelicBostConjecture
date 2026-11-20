/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Supermodular
public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Hermitian.Truncations
public import ArakelovGeometry.AdelicVectorBundle.Slope.LinearMap
public import ArakelovGeometry.AdelicVectorBundle.Slope.Subquotient

/-!
# HN contraction consequences for the pinned AG interfaces

The contraction specialization of [Chen–Moriwaki, Proposition 4.3.49][cm] is needed for source
and target carriers in independent universes. The proof adapts AG's
`map_hermitianHNFiltration_le_of_mapHeight_le` at revision
`aa45299acf0f320a3584c0b135b2e5c54623f8bc`, using the actual restricted and
quotient norms directly. These local consequences do not modify AG.
-/

@[expose] public section

namespace ArakelovGeometry.AdelicVectorBundle

universe u v w w'

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K} [S.IsProper]
  (V : AdelicVectorBundle S) (W : AdelicVectorBundle S)
  [hS : S.NormMeasurabilityHypotheses]
  [hN : S.IsArchimedeanNormalized]
  [hV : V.IsHermitian] [hW : W.IsHermitian]

/-- This paper, Section 2.5 and the proofs of Lemmas 7.1–7.2. This is the contraction case of
[Chen–Moriwaki, Proposition 4.3.49][cm].

Completed contractions preserve every HN threshold, including for the zero map. -/
theorem map_hermitianHNFiltration_le_of_completed_contraction
    (f : V →ₗ[K] W)
    (hf : ∀ ω x, W.norm ω (f.baseChange (S.ϕ ω).Completion x) ≤ V.norm ω x)
    (t : ℝ) :
    (V.hermitianHNFiltration t).map f ≤
      W.hermitianHNFiltration t := by
  let U := V.hermitianHNFiltration t
  let T := W.hermitianHNFiltration t
  let g := T.mkQ.comp (f.comp U.subtype)
  have hg : g = 0 := by
    by_contra hg
    have hm := minimalSlope_sub_mapHeight_le_maximalSlope_of_ne_zero
      (V.restrictOfNormMeasurability U) (W.quotientOfNormMeasurability T) g hg
    have hh : (V.restrictOfNormMeasurability U).mapHeight
        (W.quotientOfNormMeasurability T) g ≤ 0 := by
      apply mapHeight_le_zero_of_completed_contraction
      intro ω z
      simp only [g, LinearMap.baseChange_comp, LinearMap.comp_apply]
      exact (W.toNormFamily.quotient_norm_mk_le T ω _).trans (hf ω _)
    have hlo := V.le_minimalSlope_restrict_hermitianHNFiltration t
    have hhi := W.maximalSlope_quotient_hermitianHNFiltration_lt t
    have hb : (t : EReal) ≤ (V.restrictOfNormMeasurability U).minimalSlope -
        (V.restrictOfNormMeasurability U).mapHeight (W.quotientOfNormMeasurability T) g := by
      exact hlo.trans (by simpa using EReal.sub_le_sub (le_refl
        ((V.restrictOfNormMeasurability U).minimalSlope)) hh)
    exact (not_le_of_gt hhi) (hb.trans hm)
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
  exact (Submodule.Quotient.mk_eq_zero T).mp (DFunLike.congr_fun hg (⟨x, hx⟩ : U))

/-- A full HN threshold bounds the minimal slope of the original bundle. -/
theorem le_minimalSlope_of_hermitianHNFiltration_eq_top (t : ℝ)
    (ht : V.hermitianHNFiltration t = ⊤) :
    (t : EReal) ≤ V.minimalSlope := by
  have h := V.le_minimalSlope_restrict_hermitianHNFiltration t
  rwa [ht, V.minimalSlope_restrict_top] at h

/-- The minimal-slope threshold criterion for an arbitrary carrier universe. -/
theorem hermitianHNFiltration_eq_top_of_minimalSlope_ge (t : ℝ)
    (ht : (t : EReal) ≤ V.minimalSlope) :
    V.hermitianHNFiltration t = ⊤ := by
  let T := V.hermitianHNFiltration t
  let Q := V.quotientOfNormMeasurability T
  have hm : T.mkQ = 0 := by
    by_contra hm
    have hmap := V.minimalSlope_sub_mapHeight_le_maximalSlope_of_ne_zero Q T.mkQ hm
    have hheight : V.mapHeight Q T.mkQ ≤ 0 := by
      apply mapHeight_le_zero_of_completed_contraction
      intro ω z
      exact V.toNormFamily.quotient_norm_mk_le T ω z
    have hlo : (t : EReal) ≤ V.minimalSlope - V.mapHeight Q T.mkQ := by
      exact ht.trans (by
        simpa using EReal.sub_le_sub (le_refl (V.minimalSlope)) hheight)
    exact (not_le_of_gt
      (V.maximalSlope_quotient_hermitianHNFiltration_lt t)) (hlo.trans hmap)
  apply top_unique
  intro x _
  exact (Submodule.Quotient.mk_eq_zero T).mp (DFunLike.congr_fun hm x)

end ArakelovGeometry.AdelicVectorBundle
