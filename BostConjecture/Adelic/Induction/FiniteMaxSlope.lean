/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Adelic.Induction.FiniteSlopes
public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Destabilizing
import Mathlib.Data.Fintype.Option

/-!
# Finite-family Bost consequences, conditional on binary additivity

Binary maximal-slope additivity is an explicit hypothesis. Induction over finite
index types identifies the actual finite tensor bundle using completed norm
isometries. The unconditional mean-slope formula then gives semistability.
No Section 6 geometric inequality or unconditional Bost theorem is asserted here.
-/

@[expose] public section

noncomputable section

open Module
open scoped TensorProduct

namespace ArakelovGeometry.AdelicVectorBundle

universe u v w wι

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K} [S.IsProper]
  (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
  (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
  (hBinaryAdditivity : ∀ (A B : Type (max u w wι))
    [AddCommGroup A] [Module K A] [FiniteDimensional K A]
    [AddCommGroup B] [Module K B] [FiniteDimensional K B]
    (V : AdelicVectorBundle S A) (W : AdelicVectorBundle S B)
    (hV : V.IsHermitian hN) (hW : W.IsHermitian hN),
    0 < finrank K A → 0 < finrank K B →
    (V.orthogonalTensorPair W hS hN hV hW).maximalSlope hS hN =
      V.maximalSlope hS hN + W.maximalSlope hS hN)

include hBinaryAdditivity

/-- Binary maximal-slope additivity implies its finite-family form on the
actual orthogonal tensor bundle, including the empty index type. -/
theorem maximalSlope_orthogonalTensorOfMeasurableBase_of_binary_additivity
    {ι : Type wι} [Fintype ι] {E : ι → Type w}
    [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]
    [∀ i, FiniteDimensional K (E i)] (V : ∀ i, AdelicVectorBundle S (E i))
    (hV : ∀ i, (V i).IsHermitian hN) (hr : ∀ i, 0 < finrank K (E i)) :
    (orthogonalTensorOfMeasurableBase V hS hN hV).maximalSlope hS hN =
      ∑ i, (V i).maximalSlope hS hN := by
  classical
  have main : ∀ (ι : Type wι) [Fintype ι], ∀ (E : ι → Type w)
      [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]
      [∀ i, FiniteDimensional K (E i)] (V : ∀ i, AdelicVectorBundle S (E i))
      (hV : ∀ i, (V i).IsHermitian hN), (∀ i, 0 < finrank K (E i)) →
      (orthogonalTensorOfMeasurableBase V hS hN hV).maximalSlope hS hN =
        ∑ i, (V i).maximalSlope hS hN := by
    apply Fintype.induction_empty_option
    · intro α β _ e ih E _ _ _ V hV hr
      let := Fintype.ofEquiv β e.symm
      rw [(slopes_orthogonalTensor_reindex hS hN V hV e.symm).2]
      exact (ih (fun i => E (e i)) (fun i => V (e i)) (fun i => hV (e i))
        (fun i => hr (e i))).trans (e.sum_comp (fun i => (V i).maximalSlope hS hN))
    · intro E _ _ _ V hV hr
      have hline : finrank K (⨂[K] i, E i) = 1 := by
        simp [finrank_piTensorProduct_eq_prod]
      have hsemi := isMeanSlopeSemistable_of_finrank_eq_one
        (orthogonalTensorOfMeasurableBase V hS hN hV) hS hN hline
      rw [(isMeanSlopeSemistable_iff_maximalSlope_eq_slope _ hS hN hsemi.1).mp hsemi,
        slope_orthogonalTensorOfMeasurableBase hS hN V hV hr]
      simp
    · intro α _ ih E _ _ _ V hV hr
      let e := Equiv.optionEquivSumPUnit α
      rw [(slopes_orthogonalTensor_reindex hS hN V hV e).2,
        ← (slopes_orthogonalTensor_sum hS hN (fun j => V (e.symm j))
          (fun j => hV (e.symm j))).2]
      let A := orthogonalTensorOfMeasurableBase (fun i => V (e.symm (.inl i))) hS hN
        (fun i => hV (e.symm (.inl i)))
      let B := orthogonalTensorOfMeasurableBase (fun j => V (e.symm (.inr j))) hS hN
        (fun j => hV (e.symm (.inr j)))
      rw [hBinaryAdditivity _ _ A B _ _
        (finrank_piTensorProduct_pos (fun i => hr (e.symm (.inl i))))
        (finrank_piTensorProduct_pos (fun j => hr (e.symm (.inr j))))]
      rw [(slopes_orthogonalTensor_subsingleton hS hN
        (fun j => V (e.symm (.inr j))) (fun j => hV (e.symm (.inr j))) PUnit.unit).2]
      rw [ih (fun i => E (e.symm (.inl i))) (fun i => V (e.symm (.inl i)))
        (fun i => hV (e.symm (.inl i))) (fun i => hr (e.symm (.inl i)))]
      simp [e, Fintype.sum_option, add_comm]
  exact main ι E V hV hr

/-- Binary maximal-slope additivity implies semistability of every
finite orthogonal tensor of semistable Hermitian bundles, including the empty family. -/
theorem isMeanSlopeSemistable_orthogonalTensorOfMeasurableBase_of_binary_additivity
    {ι : Type wι} [Fintype ι] {E : ι → Type w}
    [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]
    [∀ i, FiniteDimensional K (E i)] (V : ∀ i, AdelicVectorBundle S (E i))
    (hV : ∀ i, (V i).IsHermitian hN)
    (hsemi : ∀ i, (V i).IsMeanSlopeSemistable hS hN) :
    (orthogonalTensorOfMeasurableBase V hS hN hV).IsMeanSlopeSemistable hS hN := by
  have hr (i) := (hsemi i).1
  apply (isMeanSlopeSemistable_iff_maximalSlope_eq_slope _ hS hN
    (finrank_piTensorProduct_pos hr)).mpr
  rw [maximalSlope_orthogonalTensorOfMeasurableBase_of_binary_additivity
    hS hN hBinaryAdditivity V hV hr, slope_orthogonalTensorOfMeasurableBase hS hN V hV hr]
  have he (i) := ((V i).isMeanSlopeSemistable_iff_maximalSlope_eq_slope hS hN (hr i)).mp
    (hsemi i)
  simp only [he]
  exact (map_sum Real.toERealAddHom (fun i => (V i).slope hS hN) Finset.univ).symm

end ArakelovGeometry.AdelicVectorBundle
