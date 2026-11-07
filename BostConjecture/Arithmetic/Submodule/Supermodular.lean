/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Submodule.SubmoduleDegree
public import BostConjecture.Arithmetic.Submodule.SubspaceDegree

/-!
# Supermodularity of intrinsic Hermitian subspace degree

The sum/intersection degree inequality and actual saturation give the
supermodular function needed by the HN slope bridge. Exact determinant
additivity identifies its interval slopes with actual quotient bundles.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace BostConjecture.Arithmetic

variable {K : Type*} [Field K] [NumberField K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]

/-- Generic scalar extension preserves sums of integral submodules. -/
lemma baseChange_sup (U V : Submodule (𝓞 K) M) :
    (U ⊔ V).baseChange K = U.baseChange K ⊔ V.baseChange K := by
  simp only [baseChange_eq_localized]
  exact (Submodule.localized'gi K (nonZeroDivisors (𝓞 K))
    (TensorProduct.mk (𝓞 K) K M 1)).gc.l_sup

namespace HermitianMetric

variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]

/-- Actual arithmetic degree on generic subspaces is supermodular. -/
theorem subspaceDegree_supermodular (h : HermitianMetric K M)
    (X Y : Submodule K (K ⊗[𝓞 K] M)) :
    h.subspaceDegree X + h.subspaceDegree Y ≤
      h.subspaceDegree (X ⊓ Y) + h.subspaceDegree (X ⊔ Y) := by
  have hd := h.degree_submodule_sup (integralPart X) (integralPart Y)
  have hs := h.degree_le_saturation (integralPart X ⊔ integralPart Y)
  rw [baseChange_sup, baseChange_integralPart, baseChange_integralPart] at hs
  change (h.submodule (integralPart X)).degree + (h.submodule (integralPart Y)).degree ≤
    (h.submodule (integralPart (X ⊓ Y))).degree + (h.submodule (integralPart (X ⊔ Y))).degree
  rw [integralPart_inf]
  exact hd.trans (add_le_add le_rfl hs)

/-- The concrete Hermitian subspace payoff satisfies the HN convexity axiom. -/
instance subspaceSlope_isConvex (h : HermitianMetric K M) :
    (BostConjecture.Subspace.slope h.subspaceDegree).IsConvex :=
  BostConjecture.Subspace.slope_isConvex h.subspaceDegree h.subspaceDegree_supermodular

/-- Degree differences on nested subspaces are the degree of the actual quotient. -/
lemma subspaceDegree_sub_eq_quotient (h : HermitianMetric K M)
    {X Y : Submodule K (K ⊗[𝓞 K] M)} (hXY : X ≤ Y) :
    h.subspaceDegree Y - h.subspaceDegree X =
      ((h.submodule (integralPart Y)).quotient
        ((integralPart X).comap (integralPart Y).subtype)).degree := by
  let P := integralPart X
  let T := integralPart Y
  have hPT : P ≤ T := integralPart_mono hXY
  have he := (h.submodule T).degree_exact (Submodule.inclusion hPT) (P.comap T.subtype).mkQ
    (exact_inclusion_quotient hPT) (Submodule.inclusion_injective hPT)
    (P.comap T.subtype).mkQ_surjective
  rw [pullback_submodule_inclusion] at he
  change (h.submodule T).degree - (h.submodule P).degree = _
  change (h.submodule T).degree = (h.submodule P).degree +
    ((h.submodule T).quotient (P.comap T.subtype)).degree at he
  linarith

omit [Module.Projective (𝓞 K) M] in
/-- The quotient in a strict subspace interval has the interval's dimension. -/
lemma subspaceQuotient_finrank {X Y : Submodule K (K ⊗[𝓞 K] M)} (hXY : X ≤ Y) :
    Module.finrank K (K ⊗[𝓞 K]
      (integralPart Y ⧸ (integralPart X).comap (integralPart Y).subtype)) =
        Module.finrank K Y - Module.finrank K X := by
  have hPT := integralPart_mono hXY
  have hr := generic_finrank_exact (Submodule.inclusion hPT)
    ((integralPart X).comap (integralPart Y).subtype).mkQ (exact_inclusion_quotient hPT)
    (Submodule.inclusion_injective hPT)
    ((integralPart X).comap (integralPart Y).subtype).mkQ_surjective
  rw [integralPart_generic_finrank, integralPart_generic_finrank] at hr
  omega

/-- The HN interval payoff is the slope of the intrinsic induced quotient metric. -/
lemma subspaceSlope_eq_quotient (h : HermitianMetric K M)
    {X Y : Submodule K (K ⊗[𝓞 K] M)} (hXY : X < Y) :
    BostConjecture.Subspace.slope h.subspaceDegree ⟨X, Y, hXY⟩ =
      DedekindCut.principal (((h.submodule (integralPart Y)).quotient
        ((integralPart X).comap (integralPart Y).subtype)).slope) := by
  rw [BostConjecture.Subspace.slope_apply, subspaceDegree_sub_eq_quotient h hXY.le]
  simp only [slope, subspaceQuotient_finrank hXY.le, BostConjecture.Subspace.intervalRank,
    NNReal.coe_natCast]

end HermitianMetric
end BostConjecture.Arithmetic
