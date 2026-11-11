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

set_option backward.isDefEq.respectTransparency false in
private theorem orthogonalTensor_bool_pushforward
    (ξ : NormFamily S E) (η : NormFamily S F)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hξ : ξ.IsHermitian hN) (hη : η.IsHermitian hN) :
    (NormFamily.orthogonalTensor
      (fun i ↦ NormFamily.tensorPairFactors ξ η (boolEquivUnitSumUnit i))
      hN (fun i ↦ hξ.tensorPairFactors hη (boolEquivUnitSumUnit i))).pushforward
        (boolTensorEquiv K (BoolTensorFactors E F)).toLinearMap
        (boolTensorEquiv K (BoolTensorFactors E F)).surjective =
      ξ.orthogonalTensorPair η hN hξ hη := by
  ext ω z
  let e := boolTensorEquiv K (BoolTensorFactors E F)
  obtain ⟨x, rfl⟩ := (e.baseChange K (S.ϕ ω).Completion _ _).surjective z
  exact (NormFamily.pushforward_norm_of_injective _ e.toLinearMap e.surjective
    e.injective ω x).trans
      (NormFamily.orthogonalTensor_norm_boolTensorEquiv ξ η hN hξ hη ω x).symm

omit [FiniteDimensional K Q] in
set_option backward.isDefEq.respectTransparency false in
private theorem orthogonalTensor_bool_quotient
    (ξ : NormFamily S E) (η : NormFamily S F)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hξ : ξ.IsHermitian hN) (hη : η.IsHermitian hN)
    (q : E ⊗[K] F →ₗ[K] Q) (hq : Function.Surjective q) :
    (NormFamily.orthogonalTensor
      (fun i ↦ NormFamily.tensorPairFactors ξ η (boolEquivUnitSumUnit i))
      hN (fun i ↦ hξ.tensorPairFactors hη (boolEquivUnitSumUnit i))).pushforward
        (q.comp (boolTensorEquiv K (BoolTensorFactors E F)).toLinearMap)
        (hq.comp (boolTensorEquiv K (BoolTensorFactors E F)).surjective) =
      (ξ.orthogonalTensorPair η hN hξ hη).pushforward q hq := by
  rw [← NormFamily.pushforward_comp _
    (boolTensorEquiv K (BoolTensorFactors E F)).toLinearMap
    (boolTensorEquiv K (BoolTensorFactors E F)).surjective q hq,
    orthogonalTensor_bool_pushforward]

end BinaryNorm

section FiniteQuotient

variable {K : Type u} [Field K] [CharZero K] {S : AdelicStructure.{u, v} K}
  [S.IsProper] {ι : Type w} [Fintype ι] [Nonempty ι]
  {E : ι → Type u} [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]
  [∀ i, FiniteDimensional K (E i)] [∀ i, Nontrivial (E i)]
  {Q : Type u} [AddCommGroup Q] [Module K Q] [FiniteDimensional K Q] [Nontrivial Q]

set_option backward.isDefEq.respectTransparency false in
/-- Geometric semistability of a finite tensor quotient gives the slope bound
for its actual pushforward bundle, without arithmetic semistability of factors. -/
theorem slope_sum_le_orthogonalTensor_quotient_of_geometricallySemistable
    (V : ∀ i, AdelicVectorBundle S (E i))
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hcount : S.HasCommonCountableDenseSubfield) (hV : ∀ i, (V i).IsHermitian hN)
    (q : (⨂[K] i, E i) →ₗ[K] Q) (hq : Function.Surjective q)
    (hg : IsGeometricallySemistableTensorQuotient E q) :
    let T := orthogonalTensorOfMeasurableBase V (Or.inr hcount) hN hV
    ∑ i, (V i).slope (Or.inr hcount) hN ≤
      (T.pushforward q hq (T.isMeasurable.pushforward_of_discrete_or_countable
        (Or.inr hcount) q hq)).slope (Or.inr hcount) hN := by
  let T := orthogonalTensorOfMeasurableBase V (Or.inr hcount) hN hV
  let B := T.pushforward q hq (T.isMeasurable.pushforward_of_discrete_or_countable
    (Or.inr hcount) q hq)
  let VD := fun i ↦ (V i).dualOfMeasurableBase (Or.inr hcount)
  let hVD : ∀ i, (VD i).IsHermitian hN := fun i ↦ (hV i).dual
  let A := (PiTensorProduct.dualDistribEquivOfProjective K E).symm.toLinearMap.comp q.dualMap
  have hB : B.IsHermitian hN :=
    (orthogonalTensorOfMeasurableBase_isHermitian V (Or.inr hcount) hN hV).pushforward
      q hq _
  have hA (ω : S.Ω) (x : (S.ϕ ω).Completion ⊗[K] Dual K Q) :
      (orthogonalTensorOfMeasurableBase VD (Or.inr hcount) hN hVD).norm ω
        (A.baseChange (S.ϕ ω).Completion x) =
      (B.dualOfMeasurableBase (Or.inr hcount)).norm ω x := by
    change (NormFamily.orthogonalTensor (fun i ↦ (V i).toNormFamily.dual)
      hN (fun i ↦ (hV i).dual)).norm ω
        (((PiTensorProduct.dualDistribEquivOfProjective K E).symm.toLinearMap.comp
          q.dualMap).baseChange (S.ϕ ω).Completion x) =
      ((NormFamily.orthogonalTensor (fun i ↦ (V i).toNormFamily) hN hV).pushforward
        q hq).dual.norm ω x
    rw [dualDistribEquivOfProjective_eq]
    exact (NormFamily.orthogonalTensor_pushforward_dual_norm E
      (fun i ↦ (V i).toNormFamily) hN hV q hq ω x).symm
  have hdual := slope_le_sum_of_geometricallySemistable VD hN hcount hVD
    (B.dualOfMeasurableBase (Or.inr hcount)) hB.dual A hA
    (Geometry.geometricSemistability_dualTensor_of_quotient E q hg)
  have hBD := slope_add_slope_dual_eq_zero_of_isHermitian B (Or.inr hcount) hN hB
  have hD (i : ι) : (VD i).slope (Or.inr hcount) hN =
      -(V i).slope (Or.inr hcount) hN := by
    have h := slope_add_slope_dual_eq_zero_of_isHermitian (V i) (Or.inr hcount) hN (hV i)
    linarith
  simp_rw [hD] at hdual
  rw [Finset.sum_neg_distrib] at hdual
  change ∑ i, (V i).slope (Or.inr hcount) hN ≤ B.slope (Or.inr hcount) hN
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

set_option backward.isDefEq.respectTransparency false in
/-- The geometric branch of the tensor-quotient slope inequality, with the
original binary orthogonal tensor and its actual pushforward quotient norms.
No arithmetic semistability hypothesis on either original factor is required. -/
theorem slope_sum_le_tensor_quotient_of_geometricallySemistable
    (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.IsHermitian hN) (hW : W.IsHermitian hN)
    (q : E ⊗[K] F →ₗ[K] Q) (hq : Function.Surjective q)
    (hg : IsGeometricallySemistableTensorQuotient (BoolTensorFactors E F)
      (q.comp (boolTensorEquiv K (BoolTensorFactors E F)).toLinearMap)) :
    let T := V.orthogonalTensorPair W hS hN hV hW
    let B := T.pushforward q hq (T.isMeasurable.pushforward_of_discrete_or_countable hS q hq)
    V.slope hS hN + W.slope hS hN ≤ B.slope hS hN := by
  let hcount := S.hasCommonCountableDenseSubfield_of_countable
  let VF : ∀ i, AdelicVectorBundle S (BoolTensorFactors E F i) := fun i ↦
    match i with
    | false => V
    | true => W
  have hVF : ∀ i, (VF i).IsHermitian hN := by
    intro i
    cases i
    · exact hV
    · exact hW
  let e := boolTensorEquiv K (BoolTensorFactors E F)
  let qB := q.comp e.toLinearMap
  have hqB : Function.Surjective qB := hq.comp e.surjective
  let TF := orthogonalTensorOfMeasurableBase VF (Or.inr hcount) hN hVF
  let BF := TF.pushforward qB hqB
    (TF.isMeasurable.pushforward_of_discrete_or_countable (Or.inr hcount) qB hqB)
  let T := V.orthogonalTensorPair W hS hN hV hW
  let B := T.pushforward q hq (T.isMeasurable.pushforward_of_discrete_or_countable hS q hq)
  have hnorm : (fun i ↦ (VF i).toNormFamily) =
      (fun i ↦ NormFamily.tensorPairFactors V.toNormFamily W.toNormFamily
        (boolEquivUnitSumUnit i)) := by
    funext i
    cases i <;> rfl
  have hB : BF = B := by
    apply AdelicVectorBundle.ext
    change (NormFamily.orthogonalTensor (fun i ↦ (VF i).toNormFamily) hN hVF).pushforward
      (q.comp e.toLinearMap) hqB =
      (V.toNormFamily.orthogonalTensorPair W.toNormFamily hN hV hW).pushforward q hq
    simp only [hnorm]
    exact BostConjecture.Adelic.orthogonalTensor_bool_quotient
      V.toNormFamily W.toNormFamily hN hV hW q hq
  have h := BostConjecture.Adelic.slope_sum_le_orthogonalTensor_quotient_of_geometricallySemistable
    VF hN hcount hVF qB hqB hg
  change ∑ i, (VF i).slope (Or.inr hcount) hN ≤ BF.slope (Or.inr hcount) hN at h
  rw [hB] at h
  simpa only [Fintype.sum_bool, VF, add_comm] using h

end ArakelovGeometry.AdelicVectorBundle
