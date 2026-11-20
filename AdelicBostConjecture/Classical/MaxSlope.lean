/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import HarderNarasimhan.PayoffFunction.Slope
public import AdelicBostConjecture.Classical.Adelic.Degree
public import ArakelovGeometry.AdelicVectorBundle.Slope.Finite

/-!
# The original maximal slope and its adelic comparison

The Dedekind-cut definition and arithmetic subspace degrees are unchanged from
`81cf08a874039fde5d23c0fbf3970f7d28c3beca`. Adelization multiplies maximal
slopes by `[K : ℚ]`, matching the standard adelic curve's unnormalized masses.
-/

@[expose] public section
noncomputable section

attribute [local instance 2000] Algebra.toModule Algebra.toSMul

namespace DedekindCut

/-- The real supremum of a cut's left set. Bounds are required to recover the cut. -/
noncomputable def toReal (c : DedekindCut ℝ) : ℝ := sSup c.left

/-- Between principal real bounds, taking the real value preserves the cut. -/
theorem principal_toReal_of_bounds {c : DedekindCut ℝ} {a b : ℝ}
    (ha : principal a ≤ c) (hb : c ≤ principal b) : principal c.toReal = c := by
  have hne : c.left.Nonempty := ⟨a, principal_le_iff.mp ha⟩
  have hbd : BddAbove c.left := ⟨b, left_subset_left_iff.mpr hb⟩
  apply ext'
  rw [right_principal, ← upperBounds_left]
  ext r
  exact csSup_le_iff hbd hne

end DedekindCut

section SubspaceSlope

open HarderNarasimhan
open scoped NNReal

namespace AdelicBostConjecture.Subspace

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- Dimension of a strict subspace interval as a nonnegative real. -/
noncomputable def intervalRank (I : StrictIntvl (Submodule K V)) : ℝ≥0 :=
  (Module.finrank K I.right - Module.finrank K I.left : ℕ)

lemma intervalRank_pos (I : StrictIntvl (Submodule K V)) : 0 < intervalRank I := by
  change (0 : ℝ≥0) < (Module.finrank K I.right - Module.finrank K I.left : ℕ)
  exact_mod_cast Nat.sub_pos_of_lt (Submodule.finrank_strictMono I.lt)

/-- The slope payoff of a degree on subspaces, valued in the complete ordered
space of real cuts. -/
noncomputable def slope (degree : Submodule K V → ℝ) :
    PayoffFunction (Submodule K V) (DedekindCut ℝ) :=
  PayoffFunction.slope intervalRank (fun I => degree I.right - degree I.left)

/-- Explicit evaluation of a slope; every strict subspace interval has positive rank. -/
lemma slope_apply (degree : Submodule K V → ℝ) (I : StrictIntvl (Submodule K V)) :
    slope degree I = DedekindCut.principal
      ((degree I.right - degree I.left) / (intervalRank I : ℝ)) := by
  simp [slope, PayoffFunction.slope, intervalRank_pos, div_eq_inv_mul, NNReal.smul_def]

end AdelicBostConjecture.Subspace

end SubspaceSlope

section HermitianSlopes

open NumberField TensorProduct HarderNarasimhan

namespace AdelicBostConjecture.Arithmetic.HermitianMetric

variable {K : Type*} [Field K] [NumberField K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]
variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]

/-- Intrinsic determinant degree of the actual integral part of a generic subspace. -/
def subspaceDegree (h : HermitianMetric K M)
    (X : Submodule K (K ⊗[𝓞 K] M)) : ℝ := (h.submodule (integralPart X)).degree

omit [Module.Projective (𝓞 K) M] in
/-- The generic rank in this degree's denominator is the actual subspace dimension. -/
lemma subspaceDegree_div_finrank (h : HermitianMetric K M)
    (X : Submodule K (K ⊗[𝓞 K] M)) :
    h.subspaceDegree X / Module.finrank K X = (h.submodule (integralPart X)).slope := by
  rw [slope, integralPart_generic_finrank]
  rfl

variable [Nontrivial (K ⊗[𝓞 K] M)] in
/-- Maximal Hermitian slope, as the real value of the subspace payoff's supremum. -/
def maxSlope (h : HermitianMetric K M) : ℝ :=
  ((AdelicBostConjecture.Subspace.slope h.subspaceDegree).max ⊤).toReal

open ArakelovGeometry

/-- All original integral subspace degrees are the adelic restriction degrees. -/
theorem degree_toAdelicBundle_subspace (h : HermitianMetric K M)
    (X : Submodule K (K ⊗[𝓞 K] M)) :
    (h.toAdelicBundle.restrictOfNormMeasurability X).degree =
      (Module.finrank ℚ K : ℝ) * h.subspaceDegree X := by
  rw [h.degree_toAdelicBundle_restrict X]
  exact (h.submodule (integralPart X)).degree_toAdelicBundle

/-- The original zero-subspace degree vanishes by the adelic rank-zero theorem. -/
@[simp]
lemma subspaceDegree_bot (h : HermitianMetric K M) : h.subspaceDegree ⊥ = 0 := by
  have he := h.degree_toAdelicBundle_subspace ⊥
  rw [AdelicVectorBundle.degree_eq_zero_of_finrank_eq_zero _ (by simp)] at he
  have hd : (Module.finrank ℚ K : ℝ) ≠ 0 :=
    (Nat.cast_pos.mpr (Module.finrank_pos (R := ℚ) (M := K)) :
      (0 : ℝ) < Module.finrank ℚ K).ne'
  exact (mul_eq_zero.mp he.symm).resolve_left hd

/-- The actual arithmetic degree specializes the slope payoff to the Hermitian
slope of the saturated integral submodule on every interval from zero. -/
lemma subspaceSlope_apply_bot (h : HermitianMetric K M)
    (X : Submodule K (K ⊗[𝓞 K] M)) (hX : ⊥ < X) :
    AdelicBostConjecture.Subspace.slope h.subspaceDegree ⟨⊥, X, hX⟩ =
      DedekindCut.principal (h.submodule (integralPart X)).slope := by
  rw [AdelicBostConjecture.Subspace.slope_apply]
  simp [AdelicBostConjecture.Subspace.intervalRank, subspaceDegree_div_finrank]

variable [Nontrivial (K ⊗[𝓞 K] M)]

/-- A finite real least upper bound computes the original Dedekind-cut definition. -/
theorem maxSlope_eq_of_isLUB (h : HermitianMetric K M) (s : ℝ)
    (hs : IsLUB {a : ℝ | ∃ X : Submodule K (K ⊗[𝓞 K] M),
      ⊥ < X ∧ a = (h.submodule (integralPart X)).slope} s) : h.maxSlope = s := by
  let c := (AdelicBostConjecture.Subspace.slope h.subspaceDegree).max ⊤
  have hu : c ≤ DedekindCut.principal s := by
    apply PayoffFunction.max_le
    intro X hX
    change AdelicBostConjecture.Subspace.slope h.subspaceDegree ⟨⊥, X, hX.1⟩ ≤ _
    rw [h.subspaceSlope_apply_bot, DedekindCut.principal_le_principal]
    exact hs.1 ⟨X, hX.1, rfl⟩
  have hl : DedekindCut.principal (h.submodule
      (integralPart (⊤ : Submodule K (K ⊗[𝓞 K] M)))).slope ≤ c := by
    have ht := PayoffFunction.le_max
      (μ := AdelicBostConjecture.Subspace.slope h.subspaceDegree)
      (I := (⊤ : StrictIntvl (Submodule K (K ⊗[𝓞 K] M))))
      (u := ⊤) ⟨bot_lt_top, le_top⟩
    change AdelicBostConjecture.Subspace.slope h.subspaceDegree ⟨⊥, ⊤, bot_lt_top⟩ ≤ c at ht
    rwa [h.subspaceSlope_apply_bot] at ht
  have hc : DedekindCut.principal h.maxSlope = c :=
    DedekindCut.principal_toReal_of_bounds hl hu
  apply le_antisymm
  · exact DedekindCut.principal_le_principal.mp (hc ▸ hu)
  · apply hs.2
    rintro a ⟨X, hX, rfl⟩
    apply DedekindCut.principal_le_principal.mp
    rw [hc]
    have hx := PayoffFunction.le_max
      (μ := AdelicBostConjecture.Subspace.slope h.subspaceDegree)
      (I := (⊤ : StrictIntvl (Submodule K (K ⊗[𝓞 K] M))))
      (u := X) ⟨hX, le_top⟩
    change AdelicBostConjecture.Subspace.slope h.subspaceDegree ⟨⊥, X, hX⟩ ≤ c at hx
    rwa [h.subspaceSlope_apply_bot] at hx

/-- Adelization preserves the original maximal slope with its normalization.
The standard curve uses unnormalized masses, hence the factor `[K : ℚ]`. -/
theorem maximalSlope_toAdelicBundle (h : HermitianMetric K M) :
    h.toAdelicBundle.maximalSlope =
      (((Module.finrank ℚ K : ℝ) * h.maxSlope : ℝ) : EReal) := by
  let d : ℝ := Module.finrank ℚ K
  have hd : 0 < d := Nat.cast_pos.mpr (Module.finrank_pos (R := ℚ) (M := K))
  obtain ⟨s, hs⟩ := h.toAdelicBundle.exists_maximalSlope_eq_coe
    (Module.finrank_pos (R := K) (M := K ⊗[𝓞 K] M))
  have hsl (X : Submodule K (K ⊗[𝓞 K] M)) :
      (h.toAdelicBundle.restrictOfNormMeasurability X).slope =
        d * (h.submodule (integralPart X)).slope := by
    rw [AdelicVectorBundle.slope, h.degree_toAdelicBundle_subspace, mul_div_assoc,
      subspaceDegree_div_finrank]
  have hm : h.maxSlope = s / d := by
    apply h.maxSlope_eq_of_isLUB
    constructor
    · rintro a ⟨X, hX, rfl⟩
      have hr : 0 < Module.finrank K X := by
        simpa using Submodule.finrank_strictMono hX
      have hx := h.toAdelicBundle.slope_restrict_le_maximalSlope X hr
      rw [hs, hsl, EReal.coe_le_coe_iff] at hx
      exact (le_div_iff₀ hd).mpr (by simpa only [mul_comm] using hx)
    · intro b hb
      have hu : h.toAdelicBundle.maximalSlope ≤ ((d * b : ℝ) : EReal) := by
        apply h.toAdelicBundle.maximalSlope_le
        intro X hX
        rw [hsl, EReal.coe_le_coe_iff]
        apply mul_le_mul_of_nonneg_left _ hd.le
        have hX' : ⊥ < X := bot_lt_iff_ne_bot.mpr (by
          intro he
          subst X
          simp at hX)
        exact hb ⟨X, hX', rfl⟩
      rw [hs, EReal.coe_le_coe_iff] at hu
      exact (div_le_iff₀ hd).mpr (by simpa only [mul_comm] using hu)
  rw [hm, mul_div_cancel₀ _ hd.ne']
  exact hs

end AdelicBostConjecture.Arithmetic.HermitianMetric

end HermitianSlopes
