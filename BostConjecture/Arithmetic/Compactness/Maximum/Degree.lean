/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Degree.Finiteness

/-!
# Attainment of the maximum saturated degree

The finite superlevel sets of the intrinsic degree give a maximum over all
saturated integral submodules, including zero. No freeness over the ring of
integers is required.

Reference: this paper, pages 11–12.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace BostConjecture.Arithmetic.HermitianMetric

variable {K : Type*} [Field K] [NumberField K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]
variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]

@[simp]
lemma degree_submodule_bot (h : HermitianMetric (K := K) M) :
    (h.submodule ⊥).degree = 0 := by
  apply degree_eq_zero_of_rank_zero
  simp

/-- The largest saturated degree is attained by an actual integral submodule. -/
theorem exists_max_degree_submodule (h : HermitianMetric (K := K) M) :
    ∃ P : Submodule (𝓞 K) M, Module.IsTorsionFree (𝓞 K) (M ⧸ P) ∧
      ∀ Q : Submodule (𝓞 K) M, Module.IsTorsionFree (𝓞 K) (M ⧸ Q) →
        (h.submodule Q).degree ≤ (h.submodule P).degree := by
  classical
  let S := {P : Submodule (𝓞 K) M | Module.IsTorsionFree (𝓞 K) (M ⧸ P) ∧
    0 ≤ (h.submodule P).degree}
  have hS : S.Finite := h.finite_saturated_submodules_degree_ge 0
  have hbot : integralPart (⊥ : Submodule K (K ⊗[𝓞 K] M)) ∈ S :=
    ⟨inferInstance, (h.subspaceDegree_bot).ge⟩
  obtain ⟨P, hP, hmax⟩ := hS.toFinset.exists_max_image
    (fun P => (h.submodule P).degree) ⟨_, hS.mem_toFinset.mpr hbot⟩
  have hPS : P ∈ S := hS.mem_toFinset.mp hP
  refine ⟨P, hPS.1, fun Q hQ => ?_⟩
  by_cases hQ0 : 0 ≤ (h.submodule Q).degree
  · exact hmax Q (hS.mem_toFinset.mpr ⟨hQ, hQ0⟩)
  · exact (le_of_lt (lt_of_not_ge hQ0)).trans hPS.2

/-- The supremum of the intrinsic degrees of saturated integral submodules.
`exists_max_degree_submodule` proves that this is an attained maximum. -/
def maxDegree (h : HermitianMetric (K := K) M) : ℝ :=
  sSup {d : ℝ | ∃ P : Submodule (𝓞 K) M,
    Module.IsTorsionFree (𝓞 K) (M ⧸ P) ∧ (h.submodule P).degree = d}

omit [Module.Projective (𝓞 K) M] in
/-- A maximizing submodule computes the maximum degree. -/
theorem maxDegree_eq_of_max (h : HermitianMetric (K := K) M)
    (P : Submodule (𝓞 K) M) (hP : Module.IsTorsionFree (𝓞 K) (M ⧸ P))
    (hmax : ∀ Q : Submodule (𝓞 K) M, Module.IsTorsionFree (𝓞 K) (M ⧸ Q) →
      (h.submodule Q).degree ≤ (h.submodule P).degree) :
    h.maxDegree = (h.submodule P).degree := by
  unfold maxDegree
  apply le_antisymm
  · exact csSup_le ⟨_, P, hP, rfl⟩ (by rintro d ⟨Q, hQ, rfl⟩; exact hmax Q hQ)
  · apply le_csSup
    · exact ⟨(h.submodule P).degree, by rintro d ⟨Q, hQ, rfl⟩; exact hmax Q hQ⟩
    · exact ⟨P, hP, rfl⟩

/-- An actual saturated submodule realizes `maxDegree`. -/
theorem exists_degree_eq_maxDegree (h : HermitianMetric (K := K) M) :
    ∃ P : Submodule (𝓞 K) M, Module.IsTorsionFree (𝓞 K) (M ⧸ P) ∧
      (h.submodule P).degree = h.maxDegree := by
  obtain ⟨P, hP, hmax⟩ := h.exists_max_degree_submodule
  exact ⟨P, hP, (h.maxDegree_eq_of_max P hP hmax).symm⟩

/-- Every saturated induced degree lies below the attained maximum. -/
theorem degree_le_maxDegree (h : HermitianMetric (K := K) M)
    (P : Submodule (𝓞 K) M) [Module.IsTorsionFree (𝓞 K) (M ⧸ P)] :
    (h.submodule P).degree ≤ h.maxDegree := by
  obtain ⟨Q, hQ, hmax⟩ := h.exists_max_degree_submodule
  rw [h.maxDegree_eq_of_max Q hQ hmax]
  exact hmax P inferInstance

theorem maxDegree_nonneg (h : HermitianMetric (K := K) M) : 0 ≤ h.maxDegree := by
  exact (h.subspaceDegree_bot).ge.trans (h.degree_le_maxDegree (integralPart ⊥))

end BostConjecture.Arithmetic.HermitianMetric
