/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Main.MaxSlope.FilteredBound
public import BostConjecture.Main.MaxSlope.HNGrades
public import BostConjecture.Main.TensorSemistability.TensorSemistability

/-!
# Maximal-slope additivity for the Hilbert tensor product

The actual saturated HN tensor flag has semistable Hermitian grades. Its
filtered upper bound and the attained-submodule lower bound give equality.
All modules are finite projective over the ring of integers of a number field.
-/

@[expose] public section
noncomputable section
open NumberField TensorProduct

namespace BostConjecture.Arithmetic.HermitianMetric

universe u
variable {K M N : Type u} [Field K] [NumberField K]
    [AddCommGroup M] [Module (𝓞 K) M]
    [AddCommGroup N] [Module (𝓞 K) N]
    [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
    [Module.Finite (𝓞 K) N] [Module.Projective (𝓞 K) N]
    [Nontrivial (K ⊗[𝓞 K] M)] [Nontrivial (K ⊗[𝓞 K] N)]

/-- Every actual Hermitian grade in the flattened HN tensor flag is semistable. -/
theorem hnTensorGrade_isSemistable (h : HermitianMetric (K := K) M)
    (g : HermitianMetric (K := K) N) (k : ℕ)
    (hk : k < h.hnFlag.length * g.hnFlag.length) :
    (((h.tensor g).submodule (h.hnTensorFlag g (k + 1))).quotient
      ((h.hnTensorFlag g k).comap (h.hnTensorFlag g (k + 1)).subtype)).IsSemistable := by
  let i : Fin h.hnFlag.length :=
    ⟨k / g.hnFlag.length, (Nat.div_lt_iff_lt_mul g.hnFlag_length_pos).mpr hk⟩
  let j : Fin g.hnFlag.length := ⟨k % g.hnFlag.length, Nat.mod_lt k g.hnFlag_length_pos⟩
  have hs := IsSemistable.tensor (h.hn_quotient_isSemistable i) (g.hn_quotient_isSemistable j)
    (h.hnGrade_rank_pos i) (g.hnGrade_rank_pos j)
  obtain ⟨e, he⟩ := h.exists_hnTensorGrade_isometry g k
  exact (isSemistable_iff_of_equiv _ _ e he).mpr hs

/-- The actual HN tensor filtration gives the maximal-slope upper bound. -/
theorem maxSlope_tensor_le (h : HermitianMetric (K := K) M)
    (g : HermitianMetric (K := K) N) :
    (h.tensor g).maxSlope ≤ h.maxSlope + g.maxSlope := by
  exact (h.tensor g).maxSlope_le_of_integral_filtration (h.hnTensorFlag g)
    (h.hnTensorFlag_monotone g) (h.hnTensorFlag_zero g)
    (h.hnFlag.length * g.hnFlag.length) (h.hnTensorFlag_length g)
    (h.maxSlope + g.maxSlope) (h.hnTensorGrade_isSemistable g)
    (h.hnTensorGrade_slope_le g)

/-- Manuscript Theorem 1.1: maximal slope is additive for actual Hilbert tensor
products over every number field, including nonfree finite projective modules. -/
theorem maxSlope_tensor (h : HermitianMetric (K := K) M)
    (g : HermitianMetric (K := K) N) :
    (h.tensor g).maxSlope = h.maxSlope + g.maxSlope :=
  le_antisymm (h.maxSlope_tensor_le g) (h.maxSlope_add_le_tensor g)

end BostConjecture.Arithmetic.HermitianMetric
