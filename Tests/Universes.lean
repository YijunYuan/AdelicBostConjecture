/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture

/-! Regression checks: field, places, factors and finite indices have independent universes. -/

public section

open ArakelovGeometry ArakelovGeometry.AdelicVectorBundle Module Submodule
open scoped TensorProduct

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option warningAsError true

universe uK uS uV uW uι uκ

variable {K : Type uK} [Field K] [CharZero K] [Countable K]
  {S : AdelicStructure.{uK, uS} K} [S.IsProper] [S.IsArchimedeanNormalized]
  (V : AdelicVectorBundle.{uV} S) (W : AdelicVectorBundle.{uW} S)
  [V.IsHermitian] [W.IsHermitian]

example [V.IsSemistable] [W.IsSemistable] : (V ⊗ʰ W).IsSemistable := inferInstance

example :
    (V ⊗ʰ W).hermitianHNFiltration = tensorFiltration V.hermitianHNFiltration
      W.hermitianHNFiltration ∧
    (V.IsSemistable → W.IsSemistable → (V ⊗ʰ W).IsSemistable) :=
  tensorHN_and_semistable V W

example : (V ⊗ʰ W).hermitianHNFiltration =
    tensorFiltration V.hermitianHNFiltration W.hermitianHNFiltration :=
  hermitianHNFiltration_orthogonalTensorPair V W

example [Nontrivial V] [Nontrivial W] :
    (V ⊗ʰ W).maximalSlope = V.maximalSlope + W.maximalSlope :=
  maximalSlope_orthogonalTensorPair V W

example : V.IsSemistable ↔ V.IsMeanSlopeSemistable :=
  isSemistable_iff_isMeanSlopeSemistable V

variable {ι : Type uι} [Fintype ι] (A : ι → AdelicVectorBundle.{uV} S)
  [∀ i, (A i).IsHermitian]

example [∀ i, (A i).IsSemistable] :
    (orthogonalTensorOfNormMeasurability A).IsSemistable := inferInstance

example [∀ i, Nontrivial (A i)] :
    (orthogonalTensorOfNormMeasurability A).maximalSlope = ∑ i, (A i).maximalSlope :=
  maximalSlope_orthogonalTensorOfNormMeasurability A

example {κ : Type uκ} [Fintype κ] (e : ι ≃ κ) :
    (orthogonalTensorOfNormMeasurability A).maximalSlope =
      (orthogonalTensorOfNormMeasurability (fun j ↦ A (e.symm j))).maximalSlope :=
  (slopes_orthogonalTensor_reindex A e).2

example {κ : Type uκ} [Fintype κ] (B : ι ⊕ κ → AdelicVectorBundle.{uV} S)
    [∀ i, (B i).IsHermitian] :
    ((orthogonalTensorOfNormMeasurability (fun i ↦ B (.inl i))) ⊗ʰ
      (orthogonalTensorOfNormMeasurability (fun j ↦ B (.inr j)))).maximalSlope =
        (orthogonalTensorOfNormMeasurability B).maximalSlope :=
  (slopes_orthogonalTensor_sum B).2

/-- info: 'ArakelovGeometry.AdelicVectorBundle.tensorHN_and_semistable' depends on axioms:
    [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tensorHN_and_semistable
/-- info: 'ArakelovGeometry.AdelicVectorBundle.maximalSlope_orthogonalTensorPair' depends on axioms:
    [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms maximalSlope_orthogonalTensorPair
/-- info: 'ArakelovGeometry.AdelicVectorBundle.maximalSlope_orthogonalTensorOfNormMeasurability' depends on axioms:
    [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms maximalSlope_orthogonalTensorOfNormMeasurability
/-- info: 'ArakelovGeometry.AdelicVectorBundle.isSemistable_orthogonalTensorPair' depends on axioms:
    [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isSemistable_orthogonalTensorPair
/-- info: 'ArakelovGeometry.AdelicVectorBundle.isSemistable_orthogonalTensorOfNormMeasurability' depends on axioms:
    [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isSemistable_orthogonalTensorOfNormMeasurability
/-- info: 'ArakelovGeometry.AdelicVectorBundle.hermitianHNFiltration_orthogonalTensorPair' depends on axioms:
    [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hermitianHNFiltration_orthogonalTensorPair
