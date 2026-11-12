/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.Flag.ImageHN
public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Hermitian.Uniqueness
public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Hermitian.Semistability

/-!
# Equality in the graded degree bound

The equality step of this paper, Lemma 7.1: if the lower bounds on the degrees
of the grades sum to the ambient degree, every bound is an equality. Together
with lower bounds for all actual quotient slopes this identifies the HN filtration.
All grades carry the restriction and quotient norms of the original bundle.
-/

@[expose] public section

open Module Submodule
open scoped BigOperators

namespace ArakelovGeometry.AdelicVectorBundle

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E] {S : AdelicStructure K} [S.IsProper]
  (V : AdelicVectorBundle S E)
  [hS : S.HasMeasurableBase]
  [hN : S.IsArchimedeanNormalized]
  [hV : V.IsHermitian]

include hV

/-- Equality of the total degree forces equality in every graded lower bound,
including the grades of rank zero. -/
theorem filtrationGraded_degree_eq_of_lower_bounds
    (P : ℝ → Submodule K E) (hP : Antitone P)
    (hbot : ∃ t, P t = ⊥) (htop : ∃ t, P t = ⊤)
    (hleft : ∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → P s = P t)
    (hlower : ∀ t, t * (finrank K (FiltrationGraded P t) : ℝ) ≤
      (V.filtrationGraded P t).degree)
    (htotal : (∑ᶠ t : ℝ, t * (finrank K (FiltrationGraded P t) : ℝ)) =
      V.degree) (t : ℝ) :
    (V.filtrationGraded P t).degree =
      t * (finrank K (FiltrationGraded P t) : ℝ) := by
  classical
  obtain ⟨n, U, a, hU, hz, ht, _, ha, _, hlevel, hright, hrec⟩ :=
    exists_strictMono_flag_and_jumps_of_antitone hP hbot htop hleft
  have hdegree (i : Fin n) :
      (V.filtrationGraded P (a i)).degree =
        (V.flagQuotientOfMeasurableBase U i).degree := by
    have hp : (P (a i), filtrationRightLimit P (a i)) =
        (U i.succ, U i.castSucc) := Prod.ext (hlevel i) (hright i)
    have he := congrArg (fun p : Submodule K E × Submodule K E ↦
      ((V.restrictOfMeasurableBase p.1).quotientOfMeasurableBase
        (p.2.comap p.1.subtype)).degree) hp
    exact he
  have hrank (i : Fin n) : finrank K (FiltrationGraded P (a i)) =
      finrank K ((U i.succ) ⧸ (U i.castSucc).comap (U i.succ).subtype) := by
    unfold FiltrationGraded filtrationRightLimit
    rw [hlevel i, hright i]
  have hle (i : Fin n) : a i * (finrank K
      ((U i.succ) ⧸ (U i.castSucc).comap (U i.succ).subtype) : ℝ) ≤
        (V.flagQuotientOfMeasurableBase U i).degree := by
    simpa only [hdegree i, hrank i] using hlower (a i)
  have heq : (∑ i : Fin n, a i * (finrank K
      ((U i.succ) ⧸ (U i.castSucc).comap (U i.succ).subtype) : ℝ)) =
        ∑ i : Fin n, (V.flagQuotientOfMeasurableBase U i).degree := by
    rw [← finsum_weight_mul_finrank_filtrationGraded_eq_flag U a ha.injective
      hlevel hright hrec, htotal,
      V.sum_flagQuotient_degree_eq_of_isHermitian U hU.monotone hz ht]
  by_cases ht : t ∈ Set.range a
  · obtain ⟨i, rfl⟩ := ht
    rw [hdegree i, hrank i]
    exact ((Finset.sum_eq_sum_iff_of_le (fun i _ ↦ hle i)).mp heq i
      (Finset.mem_univ i)).symm
  · have hr := finrank_filtrationGraded_eq_zero_of_flag U a hlevel hrec ht
    rw [hr, Nat.cast_zero, mul_zero,
      (V.filtrationGraded P t).degree_eq_zero_of_finrank_eq_zero hr]

/-- A finite filtration with sharp total graded degree and quotient slope lower
bounds on each grade is the actual HN filtration. No semistability is assumed. -/
theorem hermitianHNFiltration_eq_of_graded_quotient_bounds
    (P : ℝ → Submodule K E) (hP : Antitone P)
    (hbot : ∃ t, P t = ⊥) (htop : ∃ t, P t = ⊤)
    (hleft : ∀ t, ∃ ε > 0, ∀ s, t - ε < s → s ≤ t → P s = P t)
    (hlower : ∀ t, t * (finrank K (FiltrationGraded P t) : ℝ) ≤
      (V.filtrationGraded P t).degree)
    (htotal : (∑ᶠ t : ℝ, t * (finrank K (FiltrationGraded P t) : ℝ)) =
      V.degree)
    (hquot : ∀ t (U : Submodule K (FiltrationGraded P t)),
      0 < finrank K (FiltrationGraded P t ⧸ U) →
      t ≤ ((V.filtrationGraded P t).quotientOfMeasurableBase U).slope) :
    V.hermitianHNFiltration = P := by
  symm
  apply V.hermitianHNFiltration_unique P hP hbot htop hleft
  intro t
  change finrank K (FiltrationGraded P t) = 0 ∨
    (V.filtrationGraded P t).IsMeanSlopeSemistable ∧
      (V.filtrationGraded P t).slope = t
  by_cases hr : finrank K (FiltrationGraded P t) = 0
  · exact Or.inl hr
  · have hp : 0 < finrank K (FiltrationGraded P t) := Nat.pos_of_ne_zero hr
    have hs : (V.filtrationGraded P t).slope = t := by
      rw [slope, V.filtrationGraded_degree_eq_of_lower_bounds
        P hP hbot htop hleft hlower htotal t]
      exact mul_div_cancel_right₀ t (Nat.cast_ne_zero.mpr hr)
    refine Or.inr ⟨?_, hs⟩
    apply ((V.filtrationGraded P t).isMeanSlopeSemistable_iff_slope_le_quotient_of_isHermitian
           hp).mpr
    simpa only [hs] using hquot t

end ArakelovGeometry.AdelicVectorBundle
