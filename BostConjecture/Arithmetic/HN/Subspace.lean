/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Submodule.Supermodular
public import BostConjecture.Slope.FiniteLength

/-!
# The HN interval flag of intrinsic Hermitian subspace degree

The flag is constructed from the actual supermodular degree. Its interval
payoffs are actual induced quotient slopes, and game semistability becomes
ordinary inequalities on all intermediate generic subspaces. The separate
arithmetic degree-finiteness theorem is not assumed by this construction.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct HarderNarasimhan

namespace BostConjecture.Arithmetic.HermitianMetric

variable {K : Type*} [Field K] [NumberField K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]
variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
variable [Nontrivial (K ⊗[𝓞 K] M)]

/-- The canonical HN flag constructed from the proved intrinsic subspace degree. -/
def hnFlag (h : HermitianMetric (K := K) M) :
    (BostConjecture.Subspace.slope h.subspaceDegree).HarderNarasimhanFiltration :=
  (BostConjecture.Subspace.slope h.subspaceDegree).hnFiltration

/-- The actual saturated integral terms of the canonical generic flag. -/
def hnSubmodule (h : HermitianMetric (K := K) M) (n : ℕ) : Submodule (𝓞 K) M :=
  integralPart (h.hnFlag n)

@[simp]
lemma hnSubmodule_zero (h : HermitianMetric (K := K) M) : h.hnSubmodule 0 = ⊥ := by
  change integralPart (h.hnFlag.toFun 0) = ⊥
  rw [h.hnFlag.head_eq_bot, integralPart_bot]

@[simp]
lemma hnSubmodule_length (h : HermitianMetric (K := K) M) :
    h.hnSubmodule h.hnFlag.length = ⊤ := by
  change integralPart (h.hnFlag.toFun h.hnFlag.length) = ⊤
  rw [h.hnFlag.length_eq_top, integralPart_top]

lemma hnSubmodule_monotone (h : HermitianMetric (K := K) M) : Monotone h.hnSubmodule :=
  fun _ _ hij => integralPart_mono (h.hnFlag.monotone hij)

/-- Consecutive generic steps remain strict after taking actual integral parts. -/
lemma hnSubmodule_lt_succ (h : HermitianMetric (K := K) M) (i : ℕ) (hi : i < h.hnFlag.length) :
    h.hnSubmodule i < h.hnSubmodule (i + 1) := by
  refine lt_of_le_of_ne (h.hnSubmodule_monotone (Nat.le_succ i)) ?_
  intro he
  have hg := congrArg (fun P : Submodule (𝓞 K) M => P.baseChange K) he
  simp only [hnSubmodule, baseChange_integralPart] at hg
  exact (h.hnFlag.strictMonoOn hi.le hi (Nat.lt_succ_self i)).ne hg

/-- The strict interval at a step of the actual degree's HN flag. -/
def hnStep (h : HermitianMetric (K := K) M) (i : Fin h.hnFlag.length) :
    StrictIntvl (Submodule K (K ⊗[𝓞 K] M)) :=
  ⟨h.hnFlag i, h.hnFlag (i + 1), h.hnFlag.strictMonoOn i.isLt.le i.isLt (Nat.lt_succ_self i)⟩

/-- The slope of the actual induced Hermitian quotient at a flag step. -/
def hnSlope (h : HermitianMetric (K := K) M) (i : Fin h.hnFlag.length) : ℝ :=
  ((h.submodule (h.hnSubmodule (i + 1))).quotient
    ((h.hnSubmodule i).comap (h.hnSubmodule (i + 1)).subtype)).slope

lemma hnStep_payoff (h : HermitianMetric (K := K) M) (i : Fin h.hnFlag.length) :
    BostConjecture.Subspace.slope h.subspaceDegree (h.hnStep i) =
      DedekindCut.principal (h.hnSlope i) :=
  h.subspaceSlope_eq_quotient (h.hnStep i).lt

/-- Semistability of a flag interval bounds every actual intermediate quotient slope. -/
theorem hnStep_quotient_slope_le (h : HermitianMetric (K := K) M)
    (i : Fin h.hnFlag.length) (X : Submodule K (K ⊗[𝓞 K] M))
    (hiX : h.hnFlag i < X) (hXi : X ≤ h.hnFlag (i + 1)) :
    ((h.submodule (integralPart X)).quotient
      ((h.hnSubmodule i).comap (integralPart X).subtype)).slope ≤ h.hnSlope i := by
  have hs := (BostConjecture.Slope.isSemistable_restrict_iff
    (BostConjecture.Subspace.slope h.subspaceDegree) (h.hnStep i)).mp
      (h.hnFlag.piecewise_isSemistable i i.isLt) X hiX hXi
  change BostConjecture.Subspace.slope h.subspaceDegree ⟨h.hnFlag i, X, hiX⟩ ≤
    BostConjecture.Subspace.slope h.subspaceDegree (h.hnStep i) at hs
  rw [h.subspaceSlope_eq_quotient hiX, h.hnStep_payoff] at hs
  exact DedekindCut.principal_le_principal.mp hs

/-- Successive slopes of the actual Hermitian quotients strictly decrease. -/
theorem hnSlope_succ_lt (h : HermitianMetric (K := K) M)
    (i : ℕ) (hi : i + 1 < h.hnFlag.length) :
    h.hnSlope ⟨i + 1, hi⟩ < h.hnSlope ⟨i, Nat.lt_of_succ_lt hi⟩ := by
  have hs := h.hnFlag.not_A_le_succ i hi
  have he (j : Fin h.hnFlag.length) :
      (BostConjecture.Subspace.slope h.subspaceDegree).A (h.hnStep j) =
        DedekindCut.principal (h.hnSlope j) :=
    (BostConjecture.Slope.A_eq_of_isSemistable _ (h.hnStep j)
      (h.hnFlag.piecewise_isSemistable j j.isLt)).trans (h.hnStep_payoff j)
  change ¬ (BostConjecture.Subspace.slope h.subspaceDegree).A
    (h.hnStep ⟨i, Nat.lt_of_succ_lt hi⟩) ≤
      (BostConjecture.Subspace.slope h.subspaceDegree).A (h.hnStep ⟨i + 1, hi⟩) at hs
  rw [he, he, DedekindCut.principal_le_principal] at hs
  exact lt_of_not_ge hs

end BostConjecture.Arithmetic.HermitianMetric
