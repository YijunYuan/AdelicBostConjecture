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
  [hS : S.HasMeasurableBase]
  [hN : S.IsArchimedeanNormalized]
  (hBinaryAdditivity : ∀ (A B : Type (max u w wι))
    [AddCommGroup A] [Module K A] [FiniteDimensional K A]
    [AddCommGroup B] [Module K B] [FiniteDimensional K B]
    (V : AdelicVectorBundle S A) (W : AdelicVectorBundle S B)
    [V.IsHermitian] [W.IsHermitian],
    0 < finrank K A → 0 < finrank K B →
    (V ⊗ʰ W).maximalSlope =
      V.maximalSlope + W.maximalSlope)

include hBinaryAdditivity

/-- Binary maximal-slope additivity implies its finite-family form on the
actual orthogonal tensor bundle, including the empty index type. -/
theorem maximalSlope_orthogonalTensorOfMeasurableBase_of_binary_additivity
    {ι : Type wι} [Fintype ι] {E : ι → Type w}
    [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]
    [∀ i, FiniteDimensional K (E i)] (V : ∀ i, AdelicVectorBundle S (E i))
    [hV : ∀ i, (V i).IsHermitian] (hr : ∀ i, 0 < finrank K (E i)) :
    (orthogonalTensorOfMeasurableBase V).maximalSlope =
      ∑ i, (V i).maximalSlope := by
  classical
  have main : ∀ (ι : Type wι) [Fintype ι], ∀ (E : ι → Type w)
      [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]
      [∀ i, FiniteDimensional K (E i)] (V : ∀ i, AdelicVectorBundle S (E i))
      [hV : ∀ i, (V i).IsHermitian], (∀ i, 0 < finrank K (E i)) →
      (orthogonalTensorOfMeasurableBase V).maximalSlope =
        ∑ i, (V i).maximalSlope := by
    apply Fintype.induction_empty_option
    · intro α β _ e ih E _ _ _ V hV hr
      let := Fintype.ofEquiv β e.symm
      rw [(slopes_orthogonalTensor_reindex V e.symm).2]
      exact (ih (fun i => E (e i)) (fun i => V (e i))
        (fun i => hr (e i))).trans (e.sum_comp (fun i => (V i).maximalSlope))
    · intro E _ _ _ V hV hr
      have hline : finrank K (⨂[K] i, E i) = 1 := by
        simp [finrank_piTensorProduct_eq_prod]
      have hsemi := isMeanSlopeSemistable_of_finrank_eq_one
        (orthogonalTensorOfMeasurableBase V) hline
      rw [(isMeanSlopeSemistable_iff_maximalSlope_eq_slope _ hsemi.1).mp hsemi,
        slope_orthogonalTensorOfMeasurableBase V hr]
      simp
    · intro α _ ih E _ _ _ V hV hr
      let e := Equiv.optionEquivSumPUnit α
      rw [(slopes_orthogonalTensor_reindex V e).2,
        ← (slopes_orthogonalTensor_sum (fun j => V (e.symm j))).2]
      let A := orthogonalTensorOfMeasurableBase (fun i => V (e.symm (.inl i)))
      let B := orthogonalTensorOfMeasurableBase (fun j => V (e.symm (.inr j)))
      rw [hBinaryAdditivity _ _ A B
        (finrank_piTensorProduct_pos (fun i => hr (e.symm (.inl i))))
        (finrank_piTensorProduct_pos (fun j => hr (e.symm (.inr j))))]
      rw [(slopes_orthogonalTensor_subsingleton
        (fun j => V (e.symm (.inr j))) PUnit.unit).2]
      rw [ih (fun i => E (e.symm (.inl i))) (fun i => V (e.symm (.inl i)))
        (fun i => hr (e.symm (.inl i)))]
      simp [e, Fintype.sum_option, add_comm]
  exact main ι E V hr

/-- Binary maximal-slope additivity implies semistability of every
finite orthogonal tensor of semistable Hermitian bundles, including the empty family. -/
theorem isMeanSlopeSemistable_orthogonalTensorOfMeasurableBase_of_binary_additivity
    {ι : Type wι} [Fintype ι] {E : ι → Type w}
    [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]
    [∀ i, FiniteDimensional K (E i)] (V : ∀ i, AdelicVectorBundle S (E i))
    [hV : ∀ i, (V i).IsHermitian]
    [hsemi : ∀ i, (V i).IsMeanSlopeSemistable] :
    (orthogonalTensorOfMeasurableBase V).IsMeanSlopeSemistable := by
  have hr (i) := (hsemi i).1
  apply (isMeanSlopeSemistable_iff_maximalSlope_eq_slope _
    (finrank_piTensorProduct_pos hr)).mpr
  rw [maximalSlope_orthogonalTensorOfMeasurableBase_of_binary_additivity
      hBinaryAdditivity V hr, slope_orthogonalTensorOfMeasurableBase V hr]
  have he (i) := ((V i).isMeanSlopeSemistable_iff_maximalSlope_eq_slope (hr i)).mp
    (hsemi i)
  simp only [he]
  exact (map_sum Real.toERealAddHom (fun i => (V i).slope) Finset.univ).symm

end ArakelovGeometry.AdelicVectorBundle
