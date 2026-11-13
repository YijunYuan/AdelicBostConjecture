/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Adelic.Induction.TensorHN

/-!
# Extracting the maximal slope from tensor HN compatibility

Every weight in an adapted basis is bounded by the first HN slope. Applying
this to the tensor basis bounds the first tensor slope by the sum of the first
factor slopes. The reverse inequality is the existing subspace tensor bound.
The hypothesis is the actual filtration identity supplied by rank induction.
-/

@[expose] public section

open Module Submodule
open scoped TensorProduct

namespace ArakelovGeometry.AdelicVectorBundle

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K} [S.IsProper]

/-- Each weight of an HN-adapted basis is bounded by the first actual HN slope. -/
theorem weight_le_first_hermitianHNOrderedSlope
    (V : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    [hV : V.IsHermitian] (hr : 0 < finrank K V)
    {ι : Type*} (b : Basis ι K V) (w : ι → ℝ)
    (hb : ∀ t, V.hermitianHNFiltration t = span K (b '' {i | t ≤ w i}))
    (i : ι) : w i ≤ V.hermitianHNOrderedSlope ⟨0, hr⟩ := by
  have hm : b i ∈ V.hermitianHNFiltration (w i) := by
    rw [hb]
    exact subset_span ⟨i, show w i ≤ w i from le_rfl, rfl⟩
  apply (V.le_hermitianHNOrderedSlope_iff_lt_filtration_finrank (w i)
    ⟨0, hr⟩).mpr
  change 0 < finrank K (V.hermitianHNFiltration (w i))
  by_contra hn
  have : Subsingleton (V.hermitianHNFiltration (w i)) :=
    (finrank_eq_zero_iff_of_free K _).mp (Nat.eq_zero_of_not_pos hn)
  exact b.ne_zero i (congrArg Subtype.val
    (Subsingleton.elim (⟨b i, hm⟩ : V.hermitianHNFiltration (w i)) 0))

/-- The actual tensor HN identity implies maximal-slope additivity in positive rank. -/
theorem maximalSlope_orthogonalTensorPair_of_hnFiltration_eq
    (V : AdelicVectorBundle S) (W : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    [hV : V.IsHermitian] [hW : W.IsHermitian]
    (hE : 0 < finrank K V) (hF : 0 < finrank K W)
    (hHN : (V ⊗ʰ W).hermitianHNFiltration =
      tensorFiltration (V.hermitianHNFiltration)
        (W.hermitianHNFiltration)) :
    (V ⊗ʰ W).maximalSlope =
      V.maximalSlope + W.maximalSlope := by
  let T := V ⊗ʰ W
  have hT := orthogonalTensorPair_isHermitian V W
  have hpos : 0 < finrank K (V ⊗[K] W) := by
    rw [finrank_tensorProduct]
    exact Nat.mul_pos hE hF
  let a := V.hermitianHNOrderedSlope ⟨0, hE⟩
  let b := W.hermitianHNOrderedSlope ⟨0, hF⟩
  let c := T.hermitianHNOrderedSlope ⟨0, hpos⟩
  obtain ⟨e, w, he⟩ := V.exists_weighted_basis_hermitianHNFiltration
  obtain ⟨f, z, hf⟩ := W.exists_weighted_basis_hermitianHNFiltration
  have hw (i) : w i ≤ a := V.weight_le_first_hermitianHNOrderedSlope hE e w he i
  have hz (j) : z j ≤ b := W.weight_le_first_hermitianHNOrderedSlope hF f z hf j
  have hbound : c ≤ a + b := by
    by_contra hn
    have hempty : {p : Fin (finrank K V) × Fin (finrank K W) | c ≤ w p.1 + z p.2} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact hn (hp.trans (add_le_add (hw p.1) (hz p.2)))
    have hzero : T.hermitianHNFiltration c = ⊥ := by
      rw [hHN, tensorFiltration_eq_span_tensorProduct e f w z he hf, hempty]
      simp
    have hr := (T.le_hermitianHNOrderedSlope_iff_lt_filtration_finrank
        c ⟨0, hpos⟩).mp le_rfl
    rw [hzero, finrank_bot] at hr
    exact Nat.lt_irrefl 0 hr
  apply le_antisymm _ (V.maximalSlope_add_maximalSlope_le_maximalSlope_orthogonalTensorPair
    W)
  rw [← V.hermitianHNOrderedSlope_zero_eq_maximalSlope hE,
    ← W.hermitianHNOrderedSlope_zero_eq_maximalSlope hF,
    ← T.hermitianHNOrderedSlope_zero_eq_maximalSlope hpos, ← EReal.coe_add]
  exact EReal.coe_le_coe_iff.mpr hbound

end ArakelovGeometry.AdelicVectorBundle
