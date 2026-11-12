/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Adelic.Induction.FiniteNorms
public import ArakelovGeometry.AdelicVectorBundle.Degree.LineVector
import Mathlib.Data.Fintype.Option

/-!
# Mean slopes of finite orthogonal tensor products

The mean slope is additive for any finite family of positive-rank
Hermitian bundles. This uses only the tensor degree identity, without Bost's
maximal-slope identity or the Section 6 geometric quotient estimate.
-/

@[expose] public section

noncomputable section

open Module
open scoped TensorProduct

namespace ArakelovGeometry.AdelicVectorBundle

universe u v w wι

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K} [S.IsProper]
  [hS : S.HasMeasurableBase]
  [hN : S.IsArchimedeanNormalized]

/-- The actual finite orthogonal tensor has mean slope equal to the sum of
the positive-rank factor slopes. No maximal-slope hypothesis is used. -/
theorem slope_orthogonalTensorOfMeasurableBase
    {ι : Type wι} [Fintype ι] {E : ι → Type w}
    [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]
    [∀ i, FiniteDimensional K (E i)] (V : ∀ i, AdelicVectorBundle S (E i))
    (hV : ∀ i, (V i).IsHermitian) (hr : ∀ i, 0 < finrank K (E i)) :
    (orthogonalTensorOfMeasurableBase V).slope =
      ∑ i, (V i).slope := by
  classical
  have main : ∀ (ι : Type wι) [Fintype ι], ∀ (E : ι → Type w)
      [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]
      [∀ i, FiniteDimensional K (E i)] (V : ∀ i, AdelicVectorBundle S (E i))
      (hV : ∀ i, (V i).IsHermitian), (∀ i, 0 < finrank K (E i)) →
      (orthogonalTensorOfMeasurableBase V).slope =
        ∑ i, (V i).slope := by
    apply Fintype.induction_empty_option
    · intro α β _ e ih E _ _ _ V hV hr
      let := Fintype.ofEquiv β e.symm
      rw [(slopes_orthogonalTensor_reindex V hV e.symm).1]
      exact (ih (fun i => E (e i)) (fun i => V (e i)) (fun i => hV (e i))
        (fun i => hr (e i))).trans (e.sum_comp (fun i => (V i).slope))
    · intro E _ _ _ V hV hr
      have hline : ∀ i, (V i).IsLine := fun i ↦ isEmptyElim i
      have he : orthogonalTensorOfMeasurableBase V =
          orthogonalTensorLines V := rfl
      rw [he, slope_eq_degree_of_finrank_one _
        (orthogonalTensorLines_isLine V).rank_eq_one,
        degree_eq_lineDegree,
        lineDegree_orthogonalTensorLines]
      simp
    · intro α _ ih E _ _ _ V hV hr
      let e := Equiv.optionEquivSumPUnit α
      rw [(slopes_orthogonalTensor_reindex V hV e).1,
        ← (slopes_orthogonalTensor_sum (fun j => V (e.symm j))
          (fun j => hV (e.symm j))).1]
      let A := orthogonalTensorOfMeasurableBase (fun i => V (e.symm (.inl i)))
      let B := orthogonalTensorOfMeasurableBase (fun j => V (e.symm (.inr j)))
      rw [slope_orthogonalTensorPair A B
        (finrank_piTensorProduct_pos (fun i => hr (e.symm (.inl i))))
        (finrank_piTensorProduct_pos (fun j => hr (e.symm (.inr j))))]
      rw [(slopes_orthogonalTensor_subsingleton
        (fun j => V (e.symm (.inr j))) (fun j => hV (e.symm (.inr j))) PUnit.unit).1]
      rw [ih (fun i => E (e.symm (.inl i))) (fun i => V (e.symm (.inl i)))
        (fun i => hV (e.symm (.inl i))) (fun i => hr (e.symm (.inl i)))]
      simp [e, Fintype.sum_option, add_comm]
  exact main ι E V hV hr

end ArakelovGeometry.AdelicVectorBundle
