/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Main.MaxSlope.Tensor
public import BostConjecture.Main.MaxSlope.PiLowerBound

/-!
# Maximal-slope additivity and semistability for finite Hilbert tensor products

The binary maximal-slope identity extends to a finite family using tensor
regrouping. The resulting equality and semistability consequence complete
Theorem 1.1 of this paper; the empty family has degree and maximal slope zero.
-/

@[expose] public section
noncomputable section
open NumberField TensorProduct PiTensorProduct

namespace BostConjecture.Arithmetic.HermitianMetric

universe u
variable {K : Type u} [Field K] [NumberField K]

/-- The finite-family maximal-slope identity for the actual Hilbert tensor
metric, including the empty tensor unit. -/
theorem maxSlope_piTensor {ι : Type} [Fintype ι] (M : ι → Type u)
    [∀ i, AddCommGroup (M i)] [∀ i, Module (𝓞 K) (M i)]
    [∀ i, Module.Finite (𝓞 K) (M i)] [∀ i, Module.Projective (𝓞 K) (M i)]
    [∀ i, Nontrivial (K ⊗[𝓞 K] M i)]
    (h : ∀ i, HermitianMetric (K := K) (M i)) :
    (piTensor h).maxSlope = ∑ i, (h i).maxSlope := by
  classical
  apply le_antisymm ?_ (sum_maxSlope_le_piTensor M h)
  revert M
  refine Fintype.induction_empty_option (P := fun ι _ =>
    ∀ (M : ι → Type u) [∀ i, AddCommGroup (M i)] [∀ i, Module (𝓞 K) (M i)]
      [∀ i, Module.Finite (𝓞 K) (M i)] [∀ i, Module.Projective (𝓞 K) (M i)]
      [∀ i, Nontrivial (K ⊗[𝓞 K] M i)]
      (h : ∀ i, HermitianMetric (K := K) (M i)),
      (piTensor h).maxSlope ≤ ∑ i, (h i).maxSlope) ?_ ?_ ?_ ι
  · intro α β _ e ih M _ _ _ _ _ h
    let : Fintype α := Fintype.ofEquiv β e.symm
    have hm := maxSlope_eq_of_equiv (piTensor h)
      (piTensor (fun i => h (e i))) (reindex (𝓞 K) M e.symm)
      (Specht.piTensor_reindex_inner M h e)
    rw [hm, ← Equiv.sum_comp e (fun i => (h i).maxSlope)]
    exact ih (fun i => M (e i)) (fun i => h (e i))
  · intro M _ _ _ _ _ h
    simp [maxSlope_piTensor_empty]
  · intro α _ ih M _ _ _ _ _ h
    have hm := maxSlope_eq_of_equiv (piTensor h)
      ((piTensor (fun i => h (some i))).tensor (h none)) (Tensor.optionEquiv (𝓞 K) M)
      (Specht.piTensor_option_inner M h)
    rw [hm, maxSlope_tensor, Fintype.sum_option]
    linarith only [ih (fun i => M (some i)) (fun i => h (some i))]

/-- Every finite Hilbert tensor product of positive-rank semistable Hermitian
bundles is semistable, over any number field and without integral freeness. -/
theorem isSemistable_piTensor {ι : Type} [Fintype ι] (M : ι → Type u)
    [∀ i, AddCommGroup (M i)] [∀ i, Module (𝓞 K) (M i)]
    [∀ i, Module.Finite (𝓞 K) (M i)] [∀ i, Module.Projective (𝓞 K) (M i)]
    [∀ i, Nontrivial (K ⊗[𝓞 K] M i)]
    (h : ∀ i, HermitianMetric (K := K) (M i))
    (hs : ∀ i, (h i).IsSemistable) : (piTensor h).IsSemistable := by
  apply (piTensor h).isSemistable_iff_maxSlope_eq.mpr
  rw [maxSlope_piTensor, Specht.slope_piTensor M h (fun _ => Module.finrank_pos)]
  exact Finset.sum_congr rfl (fun i _ => (h i).isSemistable_iff_maxSlope_eq.mp (hs i))

end BostConjecture.Arithmetic.HermitianMetric
