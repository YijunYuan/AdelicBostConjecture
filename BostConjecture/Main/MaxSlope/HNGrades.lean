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
      ∀ σ x y,
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
  simp only [hnTensorFlag, hnTensorStep]
  let : Module.Flat (𝓞 K) (h.hnSubmodule (k / g.hnFlag.length + 1) ⧸
      (h.hnSubmodule (k / g.hnFlag.length)).comap
        (h.hnSubmodule (k / g.hnFlag.length + 1)).subtype) := by
    unfold hnSubmodule
    infer_instance
  let : Module.Flat (𝓞 K) (g.hnSubmodule (k % g.hnFlag.length + 1) ⧸
      (g.hnSubmodule (k % g.hnFlag.length)).comap
        (g.hnSubmodule (k % g.hnFlag.length + 1)).subtype) := by
    unfold hnSubmodule
    infer_instance
  refine ⟨tensorGradeEquiv
    (h.hnSubmodule_monotone (Nat.le_succ (k / g.hnFlag.length)))
    (g.hnSubmodule (k % g.hnFlag.length))
    (g.hnSubmodule (k % g.hnFlag.length + 1)), ?_⟩
  intro σ x y
  exact tensorGradeEquiv_inner h g
    (h.hnSubmodule_monotone (Nat.le_succ (k / g.hnFlag.length)))
    (g.hnSubmodule_monotone (Nat.le_succ (k % g.hnFlag.length))) σ x y

end BostConjecture.Arithmetic.HermitianMetric
