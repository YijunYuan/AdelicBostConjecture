/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Adelic.Basic
public import BostConjecture.Adelic.Slope.GeometricSubspace
public import BostConjecture.Adelic.Slope.DualQuotient
public import BostConjecture.Adelic.Slope.BoolTensor
public import BostConjecture.Adelic.Geometry.Quotient
public import ArakelovGeometry.AdelicVectorBundle.Construction.Tensor.Countable
public import ArakelovGeometry.AdelicVectorBundle.Slope.Quotient
public import ArakelovGeometry.AdelicVectorBundle.Slope.DualUpper

/-!
# The geometric quotient bound with the original pushforward norms

The geometric subspace inequality applied to the dual quotient is transported
through the actual tensor-duality and Bool-to-binary norm identifications.
-/

@[expose] public section

noncomputable section

open Module ArakelovGeometry ArakelovGeometry.AdelicVectorBundle
open ArakelovGeometry.InvariantTheory
open scoped TensorProduct

namespace BostConjecture.Adelic

universe u v w

private theorem dualDistribEquivOfProjective_eq {K : Type u} [Field K]
    {ι : Type w} [Finite ι] (E : ι → Type u)
    [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]
    [∀ i, FiniteDimensional K (E i)] :
    PiTensorProduct.dualDistribEquivOfProjective K E =
      PiTensorProduct.dualDistribEquiv (R := K) (M := E) := by
  let := Fintype.ofFinite ι
  apply LinearEquiv.toLinearMap_injective
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro f
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  simp [PiTensorProduct.dualDistribEquivOfProjective_tprod_tprod,
    PiTensorProduct.dualDistribEquiv, PiTensorProduct.dualDistribEquivOfBasis,
    finprod_eq_prod_of_fintype]

section BinaryNorm

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E F Q : Type u}
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]
  [AddCommGroup Q] [Module K Q] [FiniteDimensional K Q]

private theorem orthogonalTensor_bool_pushforward
    (ξ : NormFamily S E) (η : NormFamily S F)
    [hN : S.IsArchimedeanNormalized]
    [hξ : ξ.IsHermitian] [hη : η.IsHermitian] :
    (NormFamily.orthogonalTensor
      (fun i ↦ NormFamily.tensorPairFactors ξ η (boolEquivUnitSumUnit i))).pushforward
        (boolTensorEquiv K (BoolTensorFactors E F)).toLinearMap
        (boolTensorEquiv K (BoolTensorFactors E F)).surjective =
      (ξ ⊗ʰ η) := by
  ext ω z
  let e := boolTensorEquiv K (BoolTensorFactors E F)
  obtain ⟨x, rfl⟩ := (e.baseChange K (S.ϕ ω).Completion _ _).surjective z
  exact (NormFamily.pushforward_norm_of_injective _ e.toLinearMap e.surjective
    e.injective ω x).trans
      (NormFamily.orthogonalTensor_norm_boolTensorEquiv ξ η ω x).symm

omit [FiniteDimensional K Q] in
private theorem orthogonalTensor_bool_quotient
    (ξ : NormFamily S E) (η : NormFamily S F)
    [hN : S.IsArchimedeanNormalized]
    [hξ : ξ.IsHermitian] [hη : η.IsHermitian]
    (q : E ⊗[K] F →ₗ[K] Q) (hq : Function.Surjective q) :
    (NormFamily.orthogonalTensor
      (fun i ↦ NormFamily.tensorPairFactors ξ η (boolEquivUnitSumUnit i))).pushforward
        (q.comp (boolTensorEquiv K (BoolTensorFactors E F)).toLinearMap)
        (hq.comp (boolTensorEquiv K (BoolTensorFactors E F)).surjective) =
      (ξ ⊗ʰ η).pushforward q hq := by
  exact (NormFamily.pushforward_comp _
    (boolTensorEquiv K (BoolTensorFactors E F)).toLinearMap
    (boolTensorEquiv K (BoolTensorFactors E F)).surjective q hq).symm.trans
      (congrArg (fun ζ ↦ ζ.pushforward q hq)
        (orthogonalTensor_bool_pushforward ξ η))

end BinaryNorm

section FiniteQuotient

variable {K : Type u} [Field K] [CharZero K] {S : AdelicStructure.{u, v} K}
  [S.IsProper] {ι : Type w} [Fintype ι]
  {E : ι → Type u} [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]
  [∀ i, FiniteDimensional K (E i)] [∀ i, Nontrivial (E i)]
  {Q : Type u} [AddCommGroup Q] [Module K Q] [FiniteDimensional K Q] [Nontrivial Q]

/-- Geometric semistability of a finite tensor quotient gives the slope bound
for its actual pushforward bundle, without arithmetic semistability of factors. -/
theorem slope_sum_le_orthogonalTensor_quotient_of_geometricallySemistable
    (V : ∀ i, AdelicVectorBundle S (E i))
    [hN : S.IsArchimedeanNormalized]
    [hcount : S.HasCommonCountableDenseSubfield] [hV : ∀ i, (V i).IsHermitian]
    (q : (⨂[K] i, E i) →ₗ[K] Q) (hq : Function.Surjective q)
    (hg : IsGeometricallySemistableTensorQuotient E q) :
    let T := orthogonalTensorOfMeasurableBase V
    ∑ i, (V i).slope ≤
      (T.pushforward q hq).slope := by
  let T := orthogonalTensorOfMeasurableBase V
  let B := T.pushforward q hq
  let VD := fun i ↦ (V i).dualOfMeasurableBase
  let hVD : ∀ i, (VD i).IsHermitian := fun i ↦ (hV i).dual
  let A := (PiTensorProduct.dualDistribEquivOfProjective K E).symm.toLinearMap.comp q.dualMap
  have hB : B.IsHermitian :=
    (orthogonalTensorOfMeasurableBase_isHermitian V).pushforward
      q hq _
  have hA (ω : S.Ω) (x : (S.ϕ ω).Completion ⊗[K] Dual K Q) :
      (orthogonalTensorOfMeasurableBase VD).norm ω
        (A.baseChange (S.ϕ ω).Completion x) =
      (B.dualOfMeasurableBase).norm ω x := by
    change (NormFamily.orthogonalTensor (fun i ↦ (V i).toNormFamily.dual)).norm ω
        (((PiTensorProduct.dualDistribEquivOfProjective K E).symm.toLinearMap.comp
          q.dualMap).baseChange (S.ϕ ω).Completion x) =
      ((NormFamily.orthogonalTensor (fun i ↦ (V i).toNormFamily)).pushforward
        q hq).dual.norm ω x
    rw [dualDistribEquivOfProjective_eq]
    exact (NormFamily.orthogonalTensor_pushforward_dual_norm E
      (fun i ↦ (V i).toNormFamily) q hq ω x).symm
  have hdual := slope_le_sum_of_geometricallySemistable VD
    (B.dualOfMeasurableBase) A hA
    (Geometry.geometricSemistability_dualTensor_of_quotient E q hg)
  have hBD := slope_add_slope_dual_eq_zero_of_isHermitian B
  have hD (i : ι) : (VD i).slope =
      -(V i).slope := by
    have h := slope_add_slope_dual_eq_zero_of_isHermitian (V i)
    linarith
  simp_rw [hD] at hdual
  rw [Finset.sum_neg_distrib] at hdual
  change ∑ i, (V i).slope ≤ B.slope
  linarith

end FiniteQuotient

end BostConjecture.Adelic

namespace ArakelovGeometry.AdelicVectorBundle

universe u v

variable {K : Type u} [Field K] [CharZero K] [Countable K]
  {S : AdelicStructure.{u, v} K} [S.IsProper]
  {E F Q : Type u}
  [AddCommGroup E] [Module K E] [FiniteDimensional K E] [Nontrivial E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F] [Nontrivial F]
  [AddCommGroup Q] [Module K Q] [FiniteDimensional K Q] [Nontrivial Q]

/-- The geometric branch of the tensor-quotient slope inequality, with the
original binary orthogonal tensor and its actual pushforward quotient norms.
No arithmetic semistability hypothesis on either original factor is required. -/
theorem slope_sum_le_tensor_quotient_of_geometricallySemistable
    (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F)
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized]
    [hV : V.IsHermitian] [hW : W.IsHermitian]
    (q : E ⊗[K] F →ₗ[K] Q) (hq : Function.Surjective q)
    (hg : IsGeometricallySemistableTensorQuotient (BoolTensorFactors E F)
      (q.comp (boolTensorEquiv K (BoolTensorFactors E F)).toLinearMap)) :
    let T := V ⊗ʰ W
    let B := T.pushforward q hq
    V.slope + W.slope ≤ B.slope := by
  let VF : ∀ i, AdelicVectorBundle S (BoolTensorFactors E F i) := fun i ↦
    match i with
    | false => V
    | true => W
  have hVF : ∀ i, (VF i).IsHermitian := by
    intro i
    cases i
    · exact hV
    · exact hW
  let e := boolTensorEquiv K (BoolTensorFactors E F)
  let qB := q.comp e.toLinearMap
  have hqB : Function.Surjective qB := hq.comp e.surjective
  let TF := orthogonalTensorOfMeasurableBase VF
  let BF := TF.pushforward qB hqB
  let T := V ⊗ʰ W
  let B := T.pushforward q hq
  have hnorm : (fun i ↦ (VF i).toNormFamily) =
      (fun i ↦ NormFamily.tensorPairFactors V.toNormFamily W.toNormFamily
        (boolEquivUnitSumUnit i)) := by
    funext i
    cases i <;> rfl
  have hB : BF = B := by
    apply AdelicVectorBundle.ext
    change (NormFamily.orthogonalTensor (fun i ↦ (VF i).toNormFamily)).pushforward
      (q.comp e.toLinearMap) hqB =
      (V.toNormFamily ⊗ʰ W.toNormFamily).pushforward q hq
    simp only [hnorm]
    exact BostConjecture.Adelic.orthogonalTensor_bool_quotient
      V.toNormFamily W.toNormFamily q hq
  have h := BostConjecture.Adelic.slope_sum_le_orthogonalTensor_quotient_of_geometricallySemistable
    VF qB hqB hg
  change ∑ i, (VF i).slope ≤ BF.slope at h
  rw [hB] at h
  simp only [Fintype.sum_bool, VF, add_comm] at h
  exact h

end ArakelovGeometry.AdelicVectorBundle
