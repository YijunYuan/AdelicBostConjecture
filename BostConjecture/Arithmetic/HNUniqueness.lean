module

public import BostConjecture.Arithmetic.HermitianHN
public import HarderNarasimhan.Filtration.Unique

/-!
# Uniqueness of the intrinsic Hermitian HN filtration

A generic flag with semistable actual induced quotient bundles and strictly
decreasing slopes is the canonical flag. The proof uses the checked equivalence
between quotient and interval semistability and the pinned HN uniqueness theorem.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct HarderNarasimhan

namespace BostConjecture.Arithmetic.HermitianMetric

variable {K : Type*} [Field K] [NumberField K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]
variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
variable [Nontrivial (K ⊗[𝓞 K] M)]

/-- Any flag of actual semistable quotient bundles with decreasing slopes is canonical. -/
theorem hnFlag_unique (h : HermitianMetric (K := K) M)
    (F : ℕ → Submodule K (K ⊗[𝓞 K] M)) (n : ℕ)
    (hmono : Monotone F) (hzero : F 0 = ⊥) (htop : F n = ⊤)
    (hstrict : StrictMonoOn F (Set.Iic n))
    (hss : ∀ i < n, ((h.submodule (integralPart (F (i + 1)))).quotient
      ((integralPart (F i)).comap (integralPart (F (i + 1))).subtype)).IsSemistable)
    (hdec : ∀ i, i + 1 < n →
      ((h.submodule (integralPart (F (i + 2)))).quotient
        ((integralPart (F (i + 1))).comap (integralPart (F (i + 2))).subtype)).slope <
      ((h.submodule (integralPart (F (i + 1)))).quotient
        ((integralPart (F i)).comap (integralPart (F (i + 1))).subtype)).slope) :
    F = h.hnFlag := by
  let μ := BostConjecture.Subspace.slope h.subspaceDegree
  have hlt (i : ℕ) (hi : i < n) : F i < F (i + 1) :=
    hstrict hi.le hi (Nat.lt_succ_self i)
  have hs (i : ℕ) (hi : i < n) : (μ.restrict ⟨F i, F (i + 1), hlt i hi⟩).IsSemistable :=
    (h.quotient_isSemistable_iff_game (hlt i hi)).mp (hss i hi)
  let G : μ.HarderNarasimhanFiltration :=
    { toFun := F
      length := n
      monotone := hmono
      head_eq_bot := hzero
      length_eq_top := htop
      strictMonoOn := hstrict
      piecewise_isSemistable := hs
      not_A_le_succ := by
        intro i hi
        rw [BostConjecture.Slope.A_eq_of_isSemistable μ _ (hs i (Nat.lt_of_succ_lt hi)),
          BostConjecture.Slope.A_eq_of_isSemistable μ _ (hs (i + 1) hi)]
        change ¬ BostConjecture.Subspace.slope h.subspaceDegree _ ≤
          BostConjecture.Subspace.slope h.subspaceDegree _
        rw [h.subspaceSlope_eq_quotient, h.subspaceSlope_eq_quotient,
          DedekindCut.principal_le_principal]
        exact (hdec i hi).not_ge }
  have he : G = h.hnFlag := Subsingleton.elim _ _
  exact congrArg (fun f : μ.HarderNarasimhanFiltration => f.toFun) he

end BostConjecture.Arithmetic.HermitianMetric
