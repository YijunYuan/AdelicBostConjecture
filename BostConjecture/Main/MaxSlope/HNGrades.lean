/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Main.MaxSlope.TensorGrades

/-!
# Hilbert grades of the actual flattened HN tensor flag

Block transitions use the full-factor endpoint; every consecutive integral
quotient is canonically isometric to the tensor of the two actual HN grades.
-/

@[expose] public section
noncomputable section
open NumberField TensorProduct

namespace BostConjecture.Arithmetic.HermitianMetric

universe u
variable {K : Type*} [Field K] [NumberField K]
variable {M N : Type u} [AddCommGroup M] [Module (𝓞 K) M]
    [AddCommGroup N] [Module (𝓞 K) N]
    [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
    [Module.Finite (𝓞 K) N] [Module.Projective (𝓞 K) N]
    [Nontrivial (K ⊗[𝓞 K] M)] [Nontrivial (K ⊗[𝓞 K] N)]

omit [Module.Finite (𝓞 K) N] [Module.Projective (𝓞 K) N]
    [Nontrivial (K ⊗[𝓞 K] N)] in
/-- The actual saturated HN terms have projective ambient quotients. -/
instance hnSubmoduleQuotientProjective (h : HermitianMetric (K := K) M) (i : ℕ) :
    Module.Projective (𝓞 K) (M ⧸ h.hnSubmodule i) := by
  unfold hnSubmodule
  infer_instance

/-- Incrementing the flattened index includes the transition at each block end. -/
lemma hnTensorFlag_succ (h : HermitianMetric (K := K) M)
    (g : HermitianMetric (K := K) N) (k : ℕ) :
    h.hnTensorFlag g (k + 1) =
      h.hnTensorStep g (k / g.hnFlag.length) (k % g.hnFlag.length + 1) := by
  have hr := Nat.mod_lt k g.hnFlag_length_pos
  have hm : (k + 1) % g.hnFlag.length = (k % g.hnFlag.length + 1) % g.hnFlag.length :=
    (Nat.mod_add_mod k g.hnFlag.length 1).symm
  by_cases hb : k % g.hnFlag.length + 1 = g.hnFlag.length
  · have hz : (k + 1) % g.hnFlag.length = 0 := by rw [hm, hb, Nat.mod_self]
    simp only [hnTensorFlag, Nat.succ_div_of_mod_eq_zero hz, hz, hnTensorStep_zero,
      hb, hnTensorStep_length]
  · have ht : k % g.hnFlag.length + 1 < g.hnFlag.length := by omega
    have hm' : (k + 1) % g.hnFlag.length = k % g.hnFlag.length + 1 := by
      rw [hm, Nat.mod_eq_of_lt ht]
    have hz : (k + 1) % g.hnFlag.length ≠ 0 := by omega
    simp only [hnTensorFlag, Nat.succ_div_of_mod_ne_zero hz, hm']

/-- The consecutive actual integral HN tensor grade is isometric to the tensor
of the actual factor grades, including transitions between blocks. -/
theorem exists_hnTensorGrade_isometry (h : HermitianMetric (K := K) M)
    (g : HermitianMetric (K := K) N) (k : ℕ) :
    ∃ e : (h.hnTensorFlag g (k + 1) ⧸
          (h.hnTensorFlag g k).comap (h.hnTensorFlag g (k + 1)).subtype) ≃ₗ[𝓞 K]
      ((h.hnSubmodule (k / g.hnFlag.length + 1) ⧸
          (h.hnSubmodule (k / g.hnFlag.length)).comap
            (h.hnSubmodule (k / g.hnFlag.length + 1)).subtype) ⊗[𝓞 K]
        (g.hnSubmodule (k % g.hnFlag.length + 1) ⧸
          (g.hnSubmodule (k % g.hnFlag.length)).comap
            (g.hnSubmodule (k % g.hnFlag.length + 1)).subtype)),
      ∀ (σ : K →+* ℂ)
        (x y : ComplexFiber (h.hnTensorFlag g (k + 1) ⧸
          (h.hnTensorFlag g k).comap (h.hnTensorFlag g (k + 1)).subtype) σ),
        ((((h.submodule (h.hnSubmodule (k / g.hnFlag.length + 1))).quotient
            ((h.hnSubmodule (k / g.hnFlag.length)).comap
              (h.hnSubmodule (k / g.hnFlag.length + 1)).subtype)).tensor
          ((g.submodule (g.hnSubmodule (k % g.hnFlag.length + 1))).quotient
            ((g.hnSubmodule (k % g.hnFlag.length)).comap
              (g.hnSubmodule (k % g.hnFlag.length + 1)).subtype))).fiber σ).inner
          (fiberMap e.toLinearMap σ x) (fiberMap e.toLinearMap σ y) =
        ((((h.tensor g).submodule (h.hnTensorFlag g (k + 1))).quotient
          ((h.hnTensorFlag g k).comap (h.hnTensorFlag g (k + 1)).subtype)).fiber σ).inner x y := by
  rw [h.hnTensorFlag_succ g k]
  dsimp only [hnTensorFlag, hnTensorStep]
  -- Keep the grade indices in `+ 1` form so the quotient metric instances match directly.
  have hP : h.hnSubmodule (k / g.hnFlag.length) ≤
      h.hnSubmodule (k / g.hnFlag.length + 1) :=
    h.hnSubmodule_monotone (Nat.le_succ (k / g.hnFlag.length))
  have hQ : g.hnSubmodule (k % g.hnFlag.length) ≤
      g.hnSubmodule (k % g.hnFlag.length + 1) :=
    g.hnSubmodule_monotone (Nat.le_succ (k % g.hnFlag.length))
  refine ⟨tensorGradeEquiv hP _ _, ?_⟩
  intro σ x y
  exact tensorGradeEquiv_inner h g hP hQ σ x y

omit [Module.Finite (𝓞 K) N] [Module.Projective (𝓞 K) N]
    [Nontrivial (K ⊗[𝓞 K] N)] in
/-- Every actual HN grade has positive generic rank. -/
lemma hnGrade_rank_pos (h : HermitianMetric (K := K) M) (i : Fin h.hnFlag.length) :
    0 < Module.finrank K (K ⊗[𝓞 K]
      (h.hnSubmodule (i + 1) ⧸ (h.hnSubmodule i).comap
        (h.hnSubmodule (i + 1)).subtype)) := by
  change 0 < Module.finrank K (K ⊗[𝓞 K] (integralPart (h.hnStep i).right ⧸
    (integralPart (h.hnStep i).left).comap (integralPart (h.hnStep i).right).subtype))
  rw [subspaceQuotient_finrank (h.hnStep i).lt.le]
  exact Nat.sub_pos_of_lt (Submodule.finrank_strictMono (h.hnStep i).lt)

/-- The actual HN tensor grade has the sum of its two factor slopes. -/
theorem hnTensorGrade_slope (h : HermitianMetric (K := K) M)
    (g : HermitianMetric (K := K) N) (k : ℕ)
    (hk : k < h.hnFlag.length * g.hnFlag.length) :
    (((h.tensor g).submodule (h.hnTensorFlag g (k + 1))).quotient
      ((h.hnTensorFlag g k).comap (h.hnTensorFlag g (k + 1)).subtype)).slope =
      h.hnSlope ⟨k / g.hnFlag.length, (Nat.div_lt_iff_lt_mul g.hnFlag_length_pos).mpr hk⟩ +
      g.hnSlope ⟨k % g.hnFlag.length, Nat.mod_lt k g.hnFlag_length_pos⟩ := by
  obtain ⟨e, he⟩ := h.exists_hnTensorGrade_isometry g k
  have hd := degree_eq_of_equiv _ _ e he
  have hr := (e.baseChange (𝓞 K) K _ _).finrank_eq
  change _ = _ + _
  rw [slope, hd, hr]
  exact slope_tensor _ _ (h.hnGrade_rank_pos
    ⟨k / g.hnFlag.length, (Nat.div_lt_iff_lt_mul g.hnFlag_length_pos).mpr hk⟩)
    (g.hnGrade_rank_pos ⟨k % g.hnFlag.length, Nat.mod_lt k g.hnFlag_length_pos⟩)

/-- Every actual grade is bounded by the sum of maximal slopes, independently
of tensor semistability. -/
theorem hnTensorGrade_slope_le (h : HermitianMetric (K := K) M)
    (g : HermitianMetric (K := K) N) (k : ℕ)
    (hk : k < h.hnFlag.length * g.hnFlag.length) :
    (((h.tensor g).submodule (h.hnTensorFlag g (k + 1))).quotient
      ((h.hnTensorFlag g k).comap (h.hnTensorFlag g (k + 1)).subtype)).slope ≤
      h.maxSlope + g.maxSlope := by
  rw [h.hnTensorGrade_slope g k hk]
  exact add_le_add (h.hnSlope_le_maxSlope _) (g.hnSlope_le_maxSlope _)

end BostConjecture.Arithmetic.HermitianMetric
