/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Hermitian.Truncations
public import ArakelovGeometry.AdelicVectorBundle.Slope.Subquotient
public import ArakelovGeometry.AdelicVectorBundle.Slope.LinearMap
public import ArakelovGeometry.AdelicVectorBundle.Degree.Supermodular

/-!
# HN contraction consequences for the pinned AG interfaces

The contraction specialization of CM Proposition 4.3.49 is needed for source
and target carriers in independent universes. The proof adapts AG's
`map_hermitianHNFiltration_le_of_mapHeight_le` at revision
`0a608c4f219c4de669be8b6b1a1bc47f996d8d72`, using the actual restricted and
quotient norms directly. These local consequences do not modify AG.
-/

@[expose] public section

namespace ArakelovGeometry.AdelicVectorBundle

universe u v w w'

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K} [S.IsProper]
  {E : Type w} {F : Type w'} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]
  (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F)
  (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
  (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
  (hV : V.IsHermitian hN) (hW : W.IsHermitian hN)

/-- Completed contractions preserve every HN threshold, including for the zero map. -/
theorem map_hermitianHNFiltration_le_of_completed_contraction
    (f : E →ₗ[K] F)
    (hf : ∀ ω x, W.norm ω (f.baseChange (S.ϕ ω).Completion x) ≤ V.norm ω x)
    (t : ℝ) :
    (V.hermitianHNFiltration hS hN hV t).map f ≤
      W.hermitianHNFiltration hS hN hW t := by
  let U := V.hermitianHNFiltration hS hN hV t
  let T := W.hermitianHNFiltration hS hN hW t
  let g := T.mkQ.comp (f.comp U.subtype)
  have hg : g = 0 := by
    by_contra hg
    have hm := minimalSlope_sub_mapHeight_le_maximalSlope_of_ne_zero
      (V.restrictOfMeasurableBase U hS) (W.quotientOfMeasurableBase T hS) hS hN g hg
    have hh : (V.restrictOfMeasurableBase U hS).mapHeight
        (W.quotientOfMeasurableBase T hS) g ≤ 0 := by
      apply mapHeight_le_zero_of_completed_contraction
      intro ω z
      simp only [g, LinearMap.baseChange_comp, LinearMap.comp_apply]
      exact (W.toNormFamily.quotient_norm_mk_le T ω _).trans (hf ω _)
    have hlo := V.le_minimalSlope_restrict_hermitianHNFiltration hS hN hV t
    have hhi := W.maximalSlope_quotient_hermitianHNFiltration_lt hS hN hW t
    have hb : (t : EReal) ≤ (V.restrictOfMeasurableBase U hS).minimalSlope hS hN -
        (V.restrictOfMeasurableBase U hS).mapHeight (W.quotientOfMeasurableBase T hS) g := by
      exact hlo.trans (by simpa using EReal.sub_le_sub (le_refl
        ((V.restrictOfMeasurableBase U hS).minimalSlope hS hN)) hh)
    exact (not_le_of_gt hhi) (hb.trans hm)
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
  exact (Submodule.Quotient.mk_eq_zero T).mp (DFunLike.congr_fun hg (⟨x, hx⟩ : U))

/-- A full HN threshold bounds the minimal slope of the original bundle. -/
theorem le_minimalSlope_of_hermitianHNFiltration_eq_top (t : ℝ)
    (ht : V.hermitianHNFiltration hS hN hV t = ⊤) :
    (t : EReal) ≤ V.minimalSlope hS hN := by
  have h := V.le_minimalSlope_restrict_hermitianHNFiltration hS hN hV t
  rwa [ht, V.minimalSlope_restrict_top hS hN] at h

/-- The minimal-slope threshold criterion for an arbitrary carrier universe. -/
theorem hermitianHNFiltration_eq_top_of_minimalSlope_ge (t : ℝ)
    (ht : (t : EReal) ≤ V.minimalSlope hS hN) :
    V.hermitianHNFiltration hS hN hV t = ⊤ := by
  let T := V.hermitianHNFiltration hS hN hV t
  let Q := V.quotientOfMeasurableBase T hS
  have hm : T.mkQ = 0 := by
    by_contra hm
    have hmap := V.minimalSlope_sub_mapHeight_le_maximalSlope_of_ne_zero Q hS hN T.mkQ hm
    have hheight : V.mapHeight Q T.mkQ ≤ 0 := by
      apply mapHeight_le_zero_of_completed_contraction
      intro ω z
      exact V.toNormFamily.quotient_norm_mk_le T ω z
    have hlo : (t : EReal) ≤ V.minimalSlope hS hN - V.mapHeight Q T.mkQ := by
      exact ht.trans (by
        simpa using EReal.sub_le_sub (le_refl (V.minimalSlope hS hN)) hheight)
    exact (not_le_of_gt
      (V.maximalSlope_quotient_hermitianHNFiltration_lt hS hN hV t)) (hlo.trans hmap)
  apply top_unique
  intro x _
  exact (Submodule.Quotient.mk_eq_zero T).mp (DFunLike.congr_fun hm x)

end ArakelovGeometry.AdelicVectorBundle
