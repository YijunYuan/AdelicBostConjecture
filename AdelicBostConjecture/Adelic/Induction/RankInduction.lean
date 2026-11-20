/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import AdelicBostConjecture.Adelic.Induction.TensorHN
public import AdelicBostConjecture.Adelic.Induction.HNVariation

/-!
# Strong rank induction, conditional on the geometric quotient inequality

This paper, Section 7.3. The induction simultaneously proves tensor HN
compatibility for arbitrary bundles and tensor semistability for semistable
bundles. The unstable branch uses the actual smaller-rank HN statements
produced by strong induction, including zero grades.

The Section 6 geometric quotient inequality is an explicit hypothesis below.
This module does not supply it and does not assert an unconditional Bost theorem.
-/

@[expose] public section

open Module Submodule ArakelovGeometry.InvariantTheory
open scoped TensorProduct

namespace ArakelovGeometry.AdelicVectorBundle

universe u v wV wW

variable {K : Type u} [Field K] [CharZero K]
  {S : AdelicStructure.{u, v} K} [S.IsProper]
  [hS : S.NormMeasurabilityHypotheses]
  [hN : S.IsArchimedeanNormalized]

variable (hgeom : ∀ (Q : Type (max wV wW))
      [AddCommGroup Q] [Module K Q] [FiniteDimensional K Q] [Nontrivial Q]
      (V : AdelicVectorBundle.{wV} S) (W : AdelicVectorBundle.{wW} S)
      [Nontrivial V] [Nontrivial W]
      [V.IsHermitian] [W.IsHermitian]
      [V.IsMeanSlopeSemistable] [W.IsMeanSlopeSemistable]
      (q : V ⊗[K] W →ₗ[K] Q) (hq : Function.Surjective q),
      0 < finrank K Q →
      IsGeometricallySemistableTensorQuotient (LiftedBoolTensorFactors V W)
        (q.comp (boolTensorPairEquiv K V W).toLinearMap) →
      let T := V ⊗ʰ W
      V.slope + W.slope ≤
        (T.pushforward q hq).slope)

include hgeom

/-- Semistability from the geometric quotient bound and smaller-rank HN identities. -/
private theorem tensor_semistable_of_smaller_hn
    (V : AdelicVectorBundle.{wV} S) (W : AdelicVectorBundle.{wW} S)
    [V.IsHermitian] [W.IsHermitian]
    [hsV : V.IsMeanSlopeSemistable] [hsW : W.IsMeanSlopeSemistable]
    (hsmall : ∀ (P : ℝ → Submodule K V) (R : ℝ → Submodule K W) (t u : ℝ),
      finrank K (FiltrationGraded P t) + finrank K (FiltrationGraded R u) <
        finrank K V + finrank K W →
      ((V.filtrationGraded P t) ⊗ʰ (W.filtrationGraded R u)).hermitianHNFiltration =
        tensorFiltration (V.filtrationGraded P t).hermitianHNFiltration
          (W.filtrationGraded R u).hermitianHNFiltration) :
    (V ⊗ʰ W).IsMeanSlopeSemistable := by
  let T := V ⊗ʰ W
  have hT := orthogonalTensorPair_isHermitian V W
  have : Nontrivial V := Module.nontrivial_of_finrank_pos hsV.1
  have : Nontrivial W := Module.nontrivial_of_finrank_pos hsW.1
  have hpos : 0 < finrank K (V ⊗[K] W) := by
    rw [finrank_tensorProduct]
    exact Nat.mul_pos hsV.1 hsW.1
  apply (T.isMeanSlopeSemistable_iff_slope_le_quotient_of_isHermitian
       hpos).mpr
  intro U hU
  have : Nontrivial ((V ⊗[K] W) ⧸ U) := Module.nontrivial_of_finrank_pos hU
  change T.slope ≤ (T.quotientOfNormMeasurability U).slope
  rw [V.slope_orthogonalTensorPair W hsV.1 hsW.1]
  by_cases hg : IsGeometricallySemistableTensorQuotient (LiftedBoolTensorFactors V W)
      (U.mkQ.comp (boolTensorPairEquiv K V W).toLinearMap)
  · exact hgeom _ V W U.mkQ U.mkQ_surjective hU hg
  · apply AdelicBostConjecture.Adelic.slope_sum_le_tensor_quotient_of_not_geometricallySemistable
      V W U.mkQ U.mkQ_surjective hU ?_ hg
    exact hsmall

/-- Strong induction removes the smaller-rank hypothesis in the unstable
quotient theorem. The sole additional mathematical assumption is the displayed
Section 6 inequality for geometrically semistable quotients with their original
pushforward norms. The result includes zero-rank tensor HN identities. -/
theorem tensorHN_and_semistable_of_geometric_quotient_bound
    (V : AdelicVectorBundle.{wV} S) (W : AdelicVectorBundle.{wW} S)
    [hV : V.IsHermitian] [hW : W.IsHermitian] :
    (V ⊗ʰ W).hermitianHNFiltration =
      tensorFiltration (V.hermitianHNFiltration)
        (W.hermitianHNFiltration) ∧
    (V.IsMeanSlopeSemistable → W.IsMeanSlopeSemistable →
      (V ⊗ʰ W).IsMeanSlopeSemistable) := by
  classical
  have main : ∀ n : ℕ, ∀
      (V : AdelicVectorBundle.{wV} S) (W : AdelicVectorBundle.{wW} S)
      [V.IsHermitian] [W.IsHermitian],
      finrank K V + finrank K W ≤ n →
      (V ⊗ʰ W).hermitianHNFiltration =
        tensorFiltration (V.hermitianHNFiltration)
          (W.hermitianHNFiltration) ∧
      (V.IsMeanSlopeSemistable → W.IsMeanSlopeSemistable →
        (V ⊗ʰ W).IsMeanSlopeSemistable) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      have semistable
          (V : AdelicVectorBundle.{wV} S) (W : AdelicVectorBundle.{wW} S)
          [hV : V.IsHermitian] [hW : W.IsHermitian]
          (hrank : finrank K V + finrank K W ≤ n)
          [hsV : V.IsMeanSlopeSemistable]
          [hsW : W.IsMeanSlopeSemistable] :
          (V ⊗ʰ W).IsMeanSlopeSemistable := by
        apply tensor_semistable_of_smaller_hn hgeom V W
        intro P R t u hsmall
        exact (ih (finrank K (FiltrationGraded P t) + finrank K (FiltrationGraded R u))
          (hsmall.trans_le hrank)
          (V.filtrationGraded P t) (W.filtrationGraded R u) le_rfl).1
      intro V W hV hW hrank
      refine ⟨?_, fun _ _ ↦ semistable V W hrank⟩
      apply hermitianHNFiltration_orthogonalTensorPair_of_semistable_grades
        V W
      intro t u ht hu
      have hsV := (filtrationGraded_hermitianHN_zero_or_semistable V t).resolve_left
        (Nat.ne_of_gt ht)
      have hsW := (filtrationGraded_hermitianHN_zero_or_semistable W u).resolve_left
        (Nat.ne_of_gt hu)
      have := hsV.1
      have := hsW.1
      obtain ⟨b, w, hb⟩ := V.exists_weighted_basis_hermitianHNFiltration
      obtain ⟨c, z, hc⟩ := W.exists_weighted_basis_hermitianHNFiltration
      exact semistable (V.filtrationGraded _ t) (W.filtrationGraded _ u)
        ((Nat.add_le_add (finrank_filtrationGraded_le_of_basis b w hb t)
          (finrank_filtrationGraded_le_of_basis c z hc u)).trans hrank)
  exact main (finrank K V + finrank K W) V W le_rfl

end ArakelovGeometry.AdelicVectorBundle
