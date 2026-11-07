/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.HN.Filtration
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
theorem hnFlag_unique (h : HermitianMetric K M)
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

/-- Uniqueness for actual saturated integral flags, with their actual induced quotient metrics. -/
theorem hnSubmodule_unique (h : HermitianMetric K M)
    (F : ℕ → Submodule (𝓞 K) M) [∀ i, Module.IsTorsionFree (𝓞 K) (M ⧸ F i)]
    (n : ℕ) (hmono : Monotone F) (hzero : F 0 = ⊥) (htop : F n = ⊤)
    (hstrict : StrictMonoOn F (Set.Iic n))
    (hss : ∀ i < n, ((h.submodule (F (i + 1))).quotient
      ((F i).comap (F (i + 1)).subtype)).IsSemistable)
    (hdec : ∀ i, i + 1 < n →
      ((h.submodule (F (i + 2))).quotient
        ((F (i + 1)).comap (F (i + 2)).subtype)).slope <
      ((h.submodule (F (i + 1))).quotient
        ((F i).comap (F (i + 1)).subtype)).slope) : F = h.hnSubmodule := by
  let X (i : ℕ) := (F i).baseChange K
  have hsat (i : ℕ) : integralPart (X i) = F i := integralPart_baseChange (F i)
  have hxmono : Monotone X := fun _ _ hij => Submodule.baseChange_mono K (hmono hij)
  have hxzero : X 0 = ⊥ := by simp [X, hzero]
  have hxtop : X n = ⊤ := by simp [X, htop]
  have hxstrict : StrictMonoOn X (Set.Iic n) := by
    intro i hi j hj hij
    apply lt_of_le_of_ne (hxmono hij.le)
    intro he
    exact (hstrict hi hj hij).ne ((hsat i).symm.trans ((congrArg integralPart he).trans (hsat j)))
  have hxss : ∀ i < n, ((h.submodule (integralPart (X (i + 1)))).quotient
      ((integralPart (X i)).comap (integralPart (X (i + 1))).subtype)).IsSemistable := by
    intro i hi
    have transfer (A B : Submodule (𝓞 K) M)
        [Module.IsTorsionFree (𝓞 K) (M ⧸ A)]
        (ha : integralPart (X i) = A) (hb : integralPart (X (i + 1)) = B)
        (hh : ((h.submodule B).quotient (A.comap B.subtype)).IsSemistable) :
        ((h.submodule (integralPart (X (i + 1)))).quotient
          ((integralPart (X i)).comap (integralPart (X (i + 1))).subtype)).IsSemistable := by
      subst A B
      exact hh
    exact transfer (F i) (F (i + 1)) (hsat i) (hsat (i + 1)) (hss i hi)
  have hxdec : ∀ i, i + 1 < n →
      ((h.submodule (integralPart (X (i + 2)))).quotient
        ((integralPart (X (i + 1))).comap (integralPart (X (i + 2))).subtype)).slope <
      ((h.submodule (integralPart (X (i + 1)))).quotient
        ((integralPart (X i)).comap (integralPart (X (i + 1))).subtype)).slope := by
    intro i hi
    have transfer (A B C : Submodule (𝓞 K) M)
        [Module.IsTorsionFree (𝓞 K) (M ⧸ A)] [Module.IsTorsionFree (𝓞 K) (M ⧸ B)]
        (ha : integralPart (X i) = A) (hb : integralPart (X (i + 1)) = B)
        (hc : integralPart (X (i + 2)) = C)
        (hh : ((h.submodule C).quotient (B.comap C.subtype)).slope <
          ((h.submodule B).quotient (A.comap B.subtype)).slope) :
        ((h.submodule (integralPart (X (i + 2)))).quotient
          ((integralPart (X (i + 1))).comap (integralPart (X (i + 2))).subtype)).slope <
        ((h.submodule (integralPart (X (i + 1)))).quotient
          ((integralPart (X i)).comap (integralPart (X (i + 1))).subtype)).slope := by
      subst A B C
      exact hh
    exact transfer (F i) (F (i + 1)) (F (i + 2)) (hsat i) (hsat (i + 1))
      (hsat (i + 2)) (hdec i hi)
  have he := h.hnFlag_unique X n hxmono hxzero hxtop hxstrict hxss hxdec
  funext i
  exact (hsat i).symm.trans (congrArg integralPart (congrFun he i))

end BostConjecture.Arithmetic.HermitianMetric
