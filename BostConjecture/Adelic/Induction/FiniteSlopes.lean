/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Adelic.Induction.FiniteNorms
import Mathlib.Data.Fintype.Option

/-!
# Mean slopes of finite orthogonal tensor products

The mean slope is additive for a nonempty finite family of positive-rank
Hermitian bundles. This uses only the tensor degree identity, without Bost's
maximal-slope identity or the Section 6 geometric quotient estimate.
-/

@[expose] public section

noncomputable section

open Module
open scoped TensorProduct

namespace ArakelovGeometry.AdelicVectorBundle

universe u v

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K} [S.IsProper]
  (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
  (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)

/-- The actual finite orthogonal tensor has mean slope equal to the sum of
the positive-rank factor slopes. No maximal-slope hypothesis is used. -/
theorem slope_orthogonalTensorOfMeasurableBase
    {ι : Type u} [Fintype ι] [Nonempty ι] {E : ι → Type u}
    [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]
    [∀ i, FiniteDimensional K (E i)] (V : ∀ i, AdelicVectorBundle S (E i))
    (hV : ∀ i, (V i).IsHermitian hN) (hr : ∀ i, 0 < finrank K (E i)) :
    (orthogonalTensorOfMeasurableBase V hS hN hV).slope hS hN =
      ∑ i, (V i).slope hS hN := by
  classical
  have main : ∀ (ι : Type u) [Fintype ι], ∀ [Nonempty ι] (E : ι → Type u)
      [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]
      [∀ i, FiniteDimensional K (E i)] (V : ∀ i, AdelicVectorBundle S (E i))
      (hV : ∀ i, (V i).IsHermitian hN), (∀ i, 0 < finrank K (E i)) →
      (orthogonalTensorOfMeasurableBase V hS hN hV).slope hS hN =
        ∑ i, (V i).slope hS hN := by
    apply Fintype.induction_empty_option
    · intro α β _ e ih _ E _ _ _ V hV hr
      let := Fintype.ofEquiv β e.symm
      have : Nonempty α := ⟨e.symm (Classical.arbitrary β)⟩
      rw [(slopes_orthogonalTensor_reindex hS hN V hV e.symm).1]
      exact (ih (fun i => E (e i)) (fun i => V (e i)) (fun i => hV (e i))
        (fun i => hr (e i))).trans (e.sum_comp (fun i => (V i).slope hS hN))
    · intro h
      exact (not_nonempty_pempty h).elim
    · intro α _ ih _ E _ _ _ V hV hr
      cases isEmpty_or_nonempty α with
      | inl hα =>
        have := hα
        let : Unique (Option α) := ⟨⟨none⟩, fun x => by cases x with
          | none => rfl
          | some a => exact isEmptyElim a⟩
        rw [Fintype.sum_eq_single none (fun i hi => (hi (Subsingleton.elim i none)).elim)]
        exact (slopes_orthogonalTensor_subsingleton hS hN V hV none).1
      | inr hα =>
        have := hα
        let e := Equiv.optionEquivSumPUnit α
        rw [(slopes_orthogonalTensor_reindex hS hN V hV e).1,
          ← (slopes_orthogonalTensor_sum hS hN (fun j => V (e.symm j))
            (fun j => hV (e.symm j))).1]
        let A := orthogonalTensorOfMeasurableBase (fun i => V (e.symm (.inl i))) hS hN
          (fun i => hV (e.symm (.inl i)))
        let B := orthogonalTensorOfMeasurableBase (fun j => V (e.symm (.inr j))) hS hN
          (fun j => hV (e.symm (.inr j)))
        rw [slope_orthogonalTensorPair A B hS hN _ _
          (finrank_piTensorProduct_pos (fun i => hr (e.symm (.inl i))))
          (finrank_piTensorProduct_pos (fun j => hr (e.symm (.inr j))))]
        rw [(slopes_orthogonalTensor_subsingleton hS hN
          (fun j => V (e.symm (.inr j))) (fun j => hV (e.symm (.inr j))) PUnit.unit).1]
        rw [ih (fun i => E (e.symm (.inl i))) (fun i => V (e.symm (.inl i)))
          (fun i => hV (e.symm (.inl i))) (fun i => hr (e.symm (.inl i)))]
        simp [e, Fintype.sum_option, add_comm]
  exact main ι E V hV hr

end ArakelovGeometry.AdelicVectorBundle
