/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Adelic.Induction.TensorHN
public import ArakelovGeometry.AdelicVectorBundle.Tensor.Graded.HNVariation

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

universe u v

variable {K : Type u} [Field K] [CharZero K]
  {S : AdelicStructure.{u, v} K} [S.IsProper]
  (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
  (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)

/-- Strong induction removes the smaller-rank hypothesis in the unstable
quotient theorem. The sole additional mathematical assumption is the displayed
Section 6 inequality for geometrically semistable quotients with their original
pushforward norms. The result includes zero-rank tensor HN identities. -/
theorem tensorHN_and_semistable_of_geometric_quotient_bound
    (hgeom : ∀ (E F Q : Type u)
      [AddCommGroup E] [Module K E] [FiniteDimensional K E] [Nontrivial E]
      [AddCommGroup F] [Module K F] [FiniteDimensional K F] [Nontrivial F]
      [AddCommGroup Q] [Module K Q] [FiniteDimensional K Q] [Nontrivial Q]
      (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F)
      (hV : V.toNormFamily.IsHermitian hN) (hW : W.toNormFamily.IsHermitian hN),
      V.IsMeanSlopeSemistable hS hN → W.IsMeanSlopeSemistable hS hN →
      ∀ (q : E ⊗[K] F →ₗ[K] Q) (hq : Function.Surjective q),
      0 < finrank K Q →
      IsGeometricallySemistableTensorQuotient (BoolTensorFactors E F)
        (q.comp (boolTensorEquiv K (BoolTensorFactors E F)).toLinearMap) →
      let T := V.orthogonalTensorPair W hS hN hV hW
      V.slope hS hN + W.slope hS hN ≤
        (T.pushforward q hq
          (T.isMeasurable.pushforward_of_discrete_or_countable hS q hq)).slope hS hN)
    (E F : Type u)
    [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    [AddCommGroup F] [Module K F] [FiniteDimensional K F]
    (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F)
    (hV : V.toNormFamily.IsHermitian hN) (hW : W.toNormFamily.IsHermitian hN) :
    (V.orthogonalTensorPair W hS hN hV hW).hermitianHNFiltration hS hN
        (orthogonalTensorPair_isHermitian V W hS hN hV hW) =
      tensorFiltration (V.hermitianHNFiltration hS hN hV)
        (W.hermitianHNFiltration hS hN hW) ∧
    (V.IsMeanSlopeSemistable hS hN → W.IsMeanSlopeSemistable hS hN →
      (V.orthogonalTensorPair W hS hN hV hW).IsMeanSlopeSemistable hS hN) := by
  classical
  have main : ∀ n : ℕ, ∀ (E F : Type u)
      [AddCommGroup E] [Module K E] [FiniteDimensional K E]
      [AddCommGroup F] [Module K F] [FiniteDimensional K F]
      (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F)
      (hV : V.toNormFamily.IsHermitian hN) (hW : W.toNormFamily.IsHermitian hN),
      finrank K E + finrank K F ≤ n →
      (V.orthogonalTensorPair W hS hN hV hW).hermitianHNFiltration hS hN
          (orthogonalTensorPair_isHermitian V W hS hN hV hW) =
        tensorFiltration (V.hermitianHNFiltration hS hN hV)
          (W.hermitianHNFiltration hS hN hW) ∧
      (V.IsMeanSlopeSemistable hS hN → W.IsMeanSlopeSemistable hS hN →
        (V.orthogonalTensorPair W hS hN hV hW).IsMeanSlopeSemistable hS hN) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      have semistable (E F : Type u)
          [AddCommGroup E] [Module K E] [FiniteDimensional K E]
          [AddCommGroup F] [Module K F] [FiniteDimensional K F]
          (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F)
          (hV : V.toNormFamily.IsHermitian hN) (hW : W.toNormFamily.IsHermitian hN)
          (hrank : finrank K E + finrank K F ≤ n)
          (hsV : V.IsMeanSlopeSemistable hS hN)
          (hsW : W.IsMeanSlopeSemistable hS hN) :
          (V.orthogonalTensorPair W hS hN hV hW).IsMeanSlopeSemistable hS hN := by
        let T := V.orthogonalTensorPair W hS hN hV hW
        have hT := orthogonalTensorPair_isHermitian V W hS hN hV hW
        have : Nontrivial E := Module.nontrivial_of_finrank_pos hsV.1
        have : Nontrivial F := Module.nontrivial_of_finrank_pos hsW.1
        have hpos : 0 < finrank K (E ⊗[K] F) := by
          rw [finrank_tensorProduct]
          exact Nat.mul_pos hsV.1 hsW.1
        apply (T.isMeanSlopeSemistable_iff_slope_le_quotient_of_isHermitian
          hS hN hT hpos).mpr
        intro U hU
        have : Nontrivial ((E ⊗[K] F) ⧸ U) := Module.nontrivial_of_finrank_pos hU
        change T.slope hS hN ≤ (T.quotientOfMeasurableBase U hS).slope hS hN
        rw [V.slope_orthogonalTensorPair W hS hN hV hW hsV.1 hsW.1]
        by_cases hg : IsGeometricallySemistableTensorQuotient (BoolTensorFactors E F)
            (U.mkQ.comp (boolTensorEquiv K (BoolTensorFactors E F)).toLinearMap)
        · exact hgeom E F _ V W hV hW hsV hsW U.mkQ U.mkQ_surjective hU hg
        · apply slope_sum_le_tensor_quotient_of_not_geometricallySemistable
            V W hS hN hV hW hsV hsW U.mkQ U.mkQ_surjective hU ?_ hg
          intro P R t u hsmall
          exact (ih (finrank K (FiltrationGraded P t) + finrank K (FiltrationGraded R u))
            (hsmall.trans_le hrank) (FiltrationGraded P t) (FiltrationGraded R u)
            (V.filtrationGraded P t hS) (W.filtrationGraded R u hS)
            (hV.filtrationGraded P t) (hW.filtrationGraded R u) le_rfl).1
      intro E F _ _ _ _ _ _ V W hV hW hrank
      refine ⟨?_, semistable E F V W hV hW hrank⟩
      apply hermitianHNFiltration_orthogonalTensorPair_of_semistable_grades
        V W hS hN hV hW
      intro t u ht hu
      have hsV := (filtrationGraded_hermitianHN_zero_or_semistable V hS hN hV t).resolve_left
        (Nat.ne_of_gt ht)
      have hsW := (filtrationGraded_hermitianHN_zero_or_semistable W hS hN hW u).resolve_left
        (Nat.ne_of_gt hu)
      obtain ⟨b, w, hb⟩ := V.exists_weighted_basis_hermitianHNFiltration hS hN hV
      obtain ⟨c, z, hc⟩ := W.exists_weighted_basis_hermitianHNFiltration hS hN hW
      exact semistable _ _ (V.filtrationGraded _ t hS) (W.filtrationGraded _ u hS)
        (hV.filtrationGraded _ t) (hW.filtrationGraded _ u)
        ((Nat.add_le_add (finrank_filtrationGraded_le_of_basis b w hb t)
          (finrank_filtrationGraded_le_of_basis c z hc u)).trans hrank) hsV.1 hsW.1
  exact main (finrank K E + finrank K F) E F V W hV hW le_rfl

end ArakelovGeometry.AdelicVectorBundle
