/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.HN.Filtration

/-!
# The slope bound for an actual saturated filtration

Generic subspaces represent their saturated integral parts. Semistability
and an upper slope bound on the actual quotient metrics imply the same bound
on every integral submodule, including nonsaturated submodules. The proof
uses the proved supermodular degree inequality and exact quotient degrees.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace BostConjecture.Arithmetic.HermitianMetric

variable {K : Type*} [Field K] [NumberField K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]
variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]

/-- Semistability of an actual quotient bounds every intermediate degree
increment by the corresponding rank increment. -/
lemma interval_degree_le_of_quotient_semistable
    (h : HermitianMetric (K := K) M)
    {X Y : Submodule K (K ⊗[𝓞 K] M)} (hXY : X < Y) {c : ℝ}
    (hss : ((h.submodule (integralPart Y)).quotient
      ((integralPart X).comap (integralPart Y).subtype)).IsSemistable)
    (hc : ((h.submodule (integralPart Y)).quotient
      ((integralPart X).comap (integralPart Y).subtype)).slope ≤ c)
    {Z : Submodule K (K ⊗[𝓞 K] M)} (hXZ : X < Z) (hZY : Z ≤ Y) :
    h.subspaceDegree Z - h.subspaceDegree X ≤
      c * ((Module.finrank K Z : ℝ) - Module.finrank K X) := by
  have hs := ((h.quotient_isSemistable_iff_interval hXY).mp hss Z hXZ hZY).trans hc
  rw [slope, ← subspaceDegree_sub_eq_quotient h hXZ.le,
    subspaceQuotient_finrank hXZ.le] at hs
  have hr := Submodule.finrank_strictMono hXZ
  rw [Nat.cast_sub hr.le] at hs
  exact (div_le_iff₀ (sub_pos.mpr (by exact_mod_cast hr))).mp hs

/-- A finite saturated filtration with semistable bounded-slope grades bounds
the degree of every generic subspace. Repeated filtration steps are allowed. -/
theorem subspaceDegree_le_of_filtration (h : HermitianMetric (K := K) M)
    (A : ℕ → Submodule K (K ⊗[𝓞 K] M)) (hA : Monotone A)
    (h0 : A 0 = ⊥) (n : ℕ) (hn : A n = ⊤) (c : ℝ)
    (hss : ∀ i < n, ((h.submodule (integralPart (A (i + 1)))).quotient
      ((integralPart (A i)).comap (integralPart (A (i + 1))).subtype)).IsSemistable)
    (hc : ∀ i < n, ((h.submodule (integralPart (A (i + 1)))).quotient
      ((integralPart (A i)).comap (integralPart (A (i + 1))).subtype)).slope ≤ c)
    (X : Submodule K (K ⊗[𝓞 K] M)) :
    h.subspaceDegree X ≤ c * Module.finrank K X := by
  have hb : ∀ i, i ≤ n → ∀ Y : Submodule K (K ⊗[𝓞 K] M), Y ≤ A i →
      h.subspaceDegree Y ≤ c * Module.finrank K Y := by
    intro i
    induction i with
    | zero =>
      intro _ Y hY
      rw [h0] at hY
      rw [le_bot_iff.mp hY, subspaceDegree_bot]
      simp
    | succ i ih =>
      intro hi Y hY
      by_cases hYi : Y ≤ A i
      · exact ih (Nat.le_of_succ_le hi) Y hYi
      have hinf := ih (Nat.le_of_succ_le hi) (Y ⊓ A i) inf_le_right
      have hs := h.interval_degree_le_of_quotient_semistable
        ((right_lt_sup.mpr hYi).trans_le (sup_le hY (hA (Nat.le_succ i))))
        (hss i hi) (hc i hi) (right_lt_sup.mpr hYi)
        (sup_le hY (hA (Nat.le_succ i)))
      have hd := h.subspaceDegree_supermodular Y (A i)
      have hr : (Module.finrank K ↥(Y ⊔ A i) : ℝ) + Module.finrank K ↥(Y ⊓ A i) =
          Module.finrank K Y + Module.finrank K (A i) := by
        exact_mod_cast Submodule.finrank_sup_add_finrank_inf_eq Y (A i)
      have hrm := congrArg (c * ·) hr
      nlinarith only [hinf, hs, hd, hrm]
  exact hb n le_rfl X (by rw [hn]; exact le_top)

/-- The filtration slope bound applies to all actual integral submodules,
including nonsaturated ones. -/
theorem slope_submodule_le_of_filtration (h : HermitianMetric (K := K) M)
    (A : ℕ → Submodule K (K ⊗[𝓞 K] M)) (hA : Monotone A)
    (h0 : A 0 = ⊥) (n : ℕ) (hn : A n = ⊤) (c : ℝ)
    (hss : ∀ i < n, ((h.submodule (integralPart (A (i + 1)))).quotient
      ((integralPart (A i)).comap (integralPart (A (i + 1))).subtype)).IsSemistable)
    (hc : ∀ i < n, ((h.submodule (integralPart (A (i + 1)))).quotient
      ((integralPart (A i)).comap (integralPart (A (i + 1))).subtype)).slope ≤ c)
    (P : Submodule (𝓞 K) M) (hP : 0 < Module.finrank K (K ⊗[𝓞 K] P)) :
    (h.submodule P).slope ≤ c := by
  apply (h.slope_le_saturation P).trans
  rw [← subspaceDegree_div_finrank]
  have hr : 0 < Module.finrank K (P.baseChange K) :=
    (Submodule.toBaseChange.toLinearEquiv K P).finrank_eq ▸ hP
  exact (div_le_iff₀ (by exact_mod_cast hr)).mpr
    (h.subspaceDegree_le_of_filtration A hA h0 n hn c hss hc _)

/-- A bound on actual semistable filtration grades bounds the attained maximum. -/
theorem maxSlope_le_of_filtration [Nontrivial (K ⊗[𝓞 K] M)]
    (h : HermitianMetric (K := K) M)
    (A : ℕ → Submodule K (K ⊗[𝓞 K] M)) (hA : Monotone A)
    (h0 : A 0 = ⊥) (n : ℕ) (hn : A n = ⊤) (c : ℝ)
    (hss : ∀ i < n, ((h.submodule (integralPart (A (i + 1)))).quotient
      ((integralPart (A i)).comap (integralPart (A (i + 1))).subtype)).IsSemistable)
    (hc : ∀ i < n, ((h.submodule (integralPart (A (i + 1)))).quotient
      ((integralPart (A i)).comap (integralPart (A (i + 1))).subtype)).slope ≤ c) :
    h.maxSlope ≤ c :=
  h.slope_submodule_le_of_filtration A hA h0 n hn c hss hc
    (h.hnSubmodule 1) h.hnSubmodule_one_rank_pos

/-- The same filtration bound for actual saturated integral terms. Passing to
the generic fiber recovers each term exactly, including its quotient metric. -/
theorem maxSlope_le_of_integral_filtration [Nontrivial (K ⊗[𝓞 K] M)]
    (h : HermitianMetric (K := K) M)
    (A : ℕ → Submodule (𝓞 K) M)
    [∀ i, Module.IsTorsionFree (𝓞 K) (M ⧸ A i)] (hA : Monotone A)
    (h0 : A 0 = ⊥) (n : ℕ) (hn : A n = ⊤) (c : ℝ)
    (hss : ∀ i < n, ((h.submodule (A (i + 1))).quotient
      ((A i).comap (A (i + 1)).subtype)).IsSemistable)
    (hc : ∀ i < n, ((h.submodule (A (i + 1))).quotient
      ((A i).comap (A (i + 1)).subtype)).slope ≤ c) :
    h.maxSlope ≤ c := by
  apply h.maxSlope_le_of_filtration (fun i => (A i).baseChange K)
    (fun _ _ hij => Submodule.baseChange_mono K (hA hij))
    (by simp [h0]) n (by simp [hn]) c
  · intro i hi
    rw [integralPart_baseChange (A i), integralPart_baseChange (A (i + 1))]
    exact hss i hi
  · intro i hi
    rw [integralPart_baseChange (A i), integralPart_baseChange (A (i + 1))]
    exact hc i hi

end BostConjecture.Arithmetic.HermitianMetric
