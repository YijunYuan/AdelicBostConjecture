/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Filtration.Optimal.Geometric
public import ArakelovGeometry.LinearAlgebra.Filtration.RankDrop
public import AdelicBostConjecture.Adelic.Induction.GradedVariation

/-!
# Bost's HN variation in the unstable case

This paper, Section 7.3. Geometric instability supplies a negative candidate
for the binary optimizer theorem. Its grade-HN lifts and common adapted
bases are used in both the variation upper bound and the finite quadratic
lower bound. Strict rank-sum drop permits the smaller-rank tensor-HN
hypothesis to be applied to all source grades, including zero grades.

The quotient retains the pushforward of the original orthogonal tensor norm.
The subsequent rank induction and the geometric semistable branch complete
the proof of Theorem 1.2 in the other modules of this project.
-/

@[expose] public section

open ArakelovGeometry ArakelovGeometry.AdelicVectorBundle Submodule

open Module
open scoped TensorProduct

namespace AdelicBostConjecture.Adelic

universe u

section Conditional

variable {K : Type*} [Field K] {Q : Type*}
  [AddCommGroup Q] [Module K Q] [FiniteDimensional K Q]
  {S : AdelicStructure K} [S.IsProper]
  (V : AdelicVectorBundle S) (W : AdelicVectorBundle S)
  [hS : S.NormMeasurabilityHypotheses]
  [hN : S.IsArchimedeanNormalized]
  [hV : V.IsHermitian] [hW : W.IsHermitian]

/-- The Bost pp.31–32 quotient slope bound from an ACTUAL negative pair. The optimizer,
HN lifts and common bases are constructed, and the strict rank-sum drop is derived.
The only arithmetic induction boundary is tensor-HN compatibility on all smaller-rank
actual grades of the fixed factors, quantified before choosing the optimizer. A6's
one-sided upper bound on the same data suffices; full [Chen–Moriwaki, equation (5.13)][cm] is not
asserted.
The original quotient norm is retained. Geometric production of the candidate is separate. -/
theorem slope_sum_le_tensor_quotient_of_negative_candidate
    [hsemiV : V.IsMeanSlopeSemistable] [hsemiW : W.IsMeanSlopeSemistable]
    (q : V ⊗[K] W →ₗ[K] Q) (hq : Function.Surjective q) (hQ : 0 < finrank K Q)
    (hInd : ∀ (P : ℝ → Submodule K V) (R : ℝ → Submodule K W) (t u : ℝ),
      finrank K (FiltrationGraded P t) + finrank K (FiltrationGraded R u) <
        finrank K V + finrank K W →
      (tensorFiltrationGradedSource V W P R t u).hermitianHNFiltration =
      tensorFiltration
        ((V.filtrationGraded P t).hermitianHNFiltration)
        ((W.filtrationGraded R u).hermitianHNFiltration))
    (P₀ : ℝ → Submodule K V) (R₀ : ℝ → Submodule K W)
    [hP₀ : IsCenteredFiltration P₀] [hR₀ : IsCenteredFiltration R₀]
    (hneg₀ : filtrationExpectation (fun t ↦ (tensorFiltration P₀ R₀ t).map q) < 0) :
    let T := V ⊗ʰ W
    let B := T.pushforward q hq
    V.slope + W.slope ≤ B.slope := by
  obtain ⟨P, R, hP, hR, hunit, _, _, L, M, b, c, a, r, d, s,
      hPb, hL, hRc, hM, hlower⟩ :=
    exists_bost_hn_variation_bound V W q hq hQ
      P₀ R₀ hneg₀
  have hsmall (t u : ℝ) :
      finrank K (FiltrationGraded P t) + finrank K (FiltrationGraded R u) <
        finrank K V + finrank K W :=
    finrank_filtrationGraded_add_lt_of_centered b c a d hPb hRc
      hP.expectation_eq_zero hR.expectation_eq_zero (by rw [hunit]; exact one_ne_zero) t u
  obtain hupper := tensorFiltrationQuotient_eventual_hn_upper V W
    q hq hP.antitone hR.antitone b c a d hPb hRc L M r s hL hM
      (fun t u ↦ hInd P R t u (hsmall t u))
  exact hlower _ hupper

end Conditional

section Geometric

open ArakelovGeometry.InvariantTheory

variable {K : Type u} {Q : Type*} [Field K] [CharZero K]
  [AddCommGroup Q] [Module K Q] [FiniteDimensional K Q] [Nontrivial Q]
  {S : AdelicStructure K} [S.IsProper]
  (V : AdelicVectorBundle S) (W : AdelicVectorBundle S)
  [Nontrivial V] [Nontrivial W]
  [hS : S.NormMeasurabilityHypotheses]
  [hN : S.IsArchimedeanNormalized]
  [hV : V.IsHermitian] [hW : W.IsHermitian]

/-- This paper, proof of Theorem 1.2, equation (7.3), unstable case. The negative optimizer comes
from [Chen–Moriwaki, Theorem 5.4.3][cm].

The actual geometric unstable case of this paper, Section 7.3, equation (7.3), with the
genuine smaller-rank tensor-HN induction hypothesis still explicit. A2 geometric
nonsemistability produces an original-field unit negative global optimizer; its
actual candidate enters the proved optimizer/HN-lift arithmetic assembly. There
is no assumed numerical inequality or rank-drop certificate. The original tensor
pushforward quotient norm, proper adelic and discrete-or-countable setting are
retained, including trivial valuations. Only the binary HN variation is needed;
full [Chen–Moriwaki, equation (5.13)][cm], the full HN induction, Section 6 and Bost Theorem 1.2
are not asserted. -/
theorem slope_sum_le_tensor_quotient_of_not_geometricallySemistable
    [hsemiV : V.IsMeanSlopeSemistable] [hsemiW : W.IsMeanSlopeSemistable]
    (q : V ⊗[K] W →ₗ[K] Q) (hq : Function.Surjective q) (hQ : 0 < finrank K Q)
    (hInd : ∀ (P : ℝ → Submodule K V) (R : ℝ → Submodule K W) (t u : ℝ),
      finrank K (FiltrationGraded P t) + finrank K (FiltrationGraded R u) <
        finrank K V + finrank K W →
      (tensorFiltrationGradedSource V W P R t u).hermitianHNFiltration =
      tensorFiltration
        ((V.filtrationGraded P t).hermitianHNFiltration)
        ((W.filtrationGraded R u).hermitianHNFiltration))
    (hns : ¬ IsGeometricallySemistableTensorQuotient (LiftedBoolTensorFactors V W)
      (q.comp (boolTensorPairEquiv K V W).toLinearMap)) :
    let T := V ⊗ʰ W
    let B := T.pushforward q hq
    V.slope + W.slope ≤ B.slope := by
  obtain ⟨P₀, R₀, hP₀, hR₀, _, hneg₀, _⟩ :=
    exists_normalized_tensor_quotient_optimizer_of_not_geometricallySemistable q hq hQ hns
  let : IsCenteredFiltration P₀ := (isCenteredFiltration_iff P₀).mpr hP₀
  let : IsCenteredFiltration R₀ := (isCenteredFiltration_iff R₀).mpr hR₀
  exact slope_sum_le_tensor_quotient_of_negative_candidate V W
      q hq hQ hInd P₀ R₀ hneg₀

end Geometric

end AdelicBostConjecture.Adelic
