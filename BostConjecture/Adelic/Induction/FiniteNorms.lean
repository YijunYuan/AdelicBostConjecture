/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Tensor.Hermitian.Coherence
public import ArakelovGeometry.AdelicVectorBundle.Slope.Tensor
public import ArakelovGeometry.AdelicVectorBundle.Construction.Tensor.Countable

/-!
# Finite orthogonal tensors: singleton norms and slope transport

The canonical finite tensor is used throughout. Reindexing and grouping use
ArakelovGeometry's isometries on all completed vectors, with Hilbert norms at
infinite places and epsilon norms at finite places.
-/

@[expose] public section

noncomputable section

open Module
open scoped TensorProduct

namespace ArakelovGeometry

universe u v w wι

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {ι : Type wι} [Fintype ι] {E : ι → Type w}
  [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]
  [∀ i, FiniteDimensional K (E i)]

namespace NormFamily

/-- The canonical singleton equivalence preserves every completed tensor norm. -/
theorem orthogonalTensor_norm_subsingletonEquiv [Subsingleton ι]
    (ξ : ∀ i, NormFamily S (E i))
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hξ : ∀ i, (ξ i).IsHermitian hN) (i₀ : ι) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] (⨂[K] i, E i)) :
    (ξ i₀).norm ω
      ((PiTensorProduct.subsingletonEquiv (R := K) (s := E) i₀).toLinearMap.baseChange
        (S.ϕ ω).Completion z) = (orthogonalTensor ξ hN hξ).norm ω z := by
  classical
  let L := (S.ϕ ω).Completion
  let X i := L ⊗[K] E i
  let e := PiTensorProduct.subsingletonEquiv (R := K) (s := E) i₀
  let eL := PiTensorProduct.subsingletonEquiv (R := L) (s := X) i₀
  let b := tensorBaseChangeEquiv K L E
  have he : e.toLinearMap.baseChange L = eL.toLinearMap.comp b.toLinearMap := by
    ext f
    simp only [TensorProduct.AlgebraTensorModule.curry_apply, LinearMap.compMultilinearMap_apply,
      TensorProduct.curry_apply, LinearMap.coe_restrictScalars, LinearMap.baseChange_tmul,
      LinearEquiv.coe_coe, LinearEquiv.comp_coe, LinearEquiv.trans_apply]
    rw [tensorBaseChangeEquiv_tmul_tprod]
    simp [e, eL]
  let x := eL (b z)
  let f : ∀ i, X i := Function.update 0 i₀ x
  have hf : PiTensorProduct.tprod L f = b z := by
    exact eL.symm_apply_apply (b z)
  have h := orthogonalTensor_norm_tprod ξ hN hξ ω f
  rw [hf, LinearEquiv.symm_apply_apply] at h
  rw [Fintype.prod_eq_single i₀ (fun i hi => (hi (Subsingleton.elim i i₀)).elim)] at h
  change (ξ i₀).norm ω (e.toLinearMap.baseChange L z) = _
  rw [he]
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, f, Function.update_self] using h.symm

end NormFamily

namespace AdelicVectorBundle

variable [S.IsProper]
  (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
  (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)

/-- The finite tensor rank is the product of the factor ranks, including zero ranks. -/
theorem finrank_piTensorProduct_eq_prod :
    finrank K (⨂[K] i, E i) = ∏ i, finrank K (E i) := by
  classical
  simpa using finrank_eq_card_basis (Basis.piTensorProduct (fun i => finBasis K (E i)))

omit [Fintype ι] in
/-- A finite tensor of positive-rank spaces has positive rank. -/
theorem finrank_piTensorProduct_pos [Finite ι] (hr : ∀ i, 0 < finrank K (E i)) :
    0 < finrank K (⨂[K] i, E i) := by
  let := Fintype.ofFinite ι
  rw [finrank_piTensorProduct_eq_prod]
  exact Finset.prod_pos fun i _ => hr i

/-- Reindexing preserves both slopes of the actual finite orthogonal bundle. -/
theorem slopes_orthogonalTensor_reindex {κ : Type wι} [Fintype κ]
    (V : ∀ i, AdelicVectorBundle S (E i))
    (hV : ∀ i, (V i).IsHermitian hN) (e : ι ≃ κ) :
    (orthogonalTensorOfMeasurableBase V hS hN hV).slope hS hN =
        (orthogonalTensorOfMeasurableBase (fun j => V (e.symm j)) hS hN
          (fun j => hV (e.symm j))).slope hS hN ∧
    (orthogonalTensorOfMeasurableBase V hS hN hV).maximalSlope hS hN =
        (orthogonalTensorOfMeasurableBase (fun j => V (e.symm j)) hS hN
          (fun j => hV (e.symm j))).maximalSlope hS hN := by
  have he := NormFamily.orthogonalTensor_norm_reindex
    (fun i => (V i).toNormFamily) hN hV e
  exact ⟨slope_eq_of_completed_isometry _ _ (PiTensorProduct.reindex K E e) hS hN he,
    maximalSlope_eq_of_completed_isometry _ _ (PiTensorProduct.reindex K E e) hS hN he⟩

/-- The one-factor finite tensor has exactly the slopes of its factor. -/
theorem slopes_orthogonalTensor_subsingleton [Subsingleton ι]
    (V : ∀ i, AdelicVectorBundle S (E i))
    (hV : ∀ i, (V i).IsHermitian hN) (i₀ : ι) :
    (orthogonalTensorOfMeasurableBase V hS hN hV).slope hS hN =
        (V i₀).slope hS hN ∧
    (orthogonalTensorOfMeasurableBase V hS hN hV).maximalSlope hS hN =
        (V i₀).maximalSlope hS hN := by
  have he := NormFamily.orthogonalTensor_norm_subsingletonEquiv
    (fun i => (V i).toNormFamily) hN hV i₀
  exact ⟨slope_eq_of_completed_isometry _ _
      (PiTensorProduct.subsingletonEquiv (R := K) (s := E) i₀) hS hN he,
    maximalSlope_eq_of_completed_isometry _ _
      (PiTensorProduct.subsingletonEquiv (R := K) (s := E) i₀) hS hN he⟩

/-- Canonical grouping preserves the mean and maximal slopes on the actual norms. -/
theorem slopes_orthogonalTensor_sum {κ : Type wι} [Fintype κ]
    {D : ι ⊕ κ → Type w} [∀ i, AddCommGroup (D i)] [∀ i, Module K (D i)]
    [∀ i, FiniteDimensional K (D i)] (V : ∀ i, AdelicVectorBundle S (D i))
    (hV : ∀ i, (V i).IsHermitian hN) :
    let A := orthogonalTensorOfMeasurableBase (fun i => V (.inl i)) hS hN
      (fun i => hV (.inl i))
    let B := orthogonalTensorOfMeasurableBase (fun j => V (.inr j)) hS hN
      (fun j => hV (.inr j))
    let hA := orthogonalTensorOfMeasurableBase_isHermitian _ hS hN (fun i => hV (.inl i))
    let hB := orthogonalTensorOfMeasurableBase_isHermitian _ hS hN (fun j => hV (.inr j))
    (A.orthogonalTensorPair B hS hN hA hB).slope hS hN =
        (orthogonalTensorOfMeasurableBase V hS hN hV).slope hS hN ∧
    (A.orthogonalTensorPair B hS hN hA hB).maximalSlope hS hN =
        (orthogonalTensorOfMeasurableBase V hS hN hV).maximalSlope hS hN := by
  have he := NormFamily.orthogonalTensor_norm_tmulEquivDep
    (fun i => (V i).toNormFamily) hN hV
  exact ⟨slope_eq_of_completed_isometry _ _ (PiTensorProduct.tmulEquivDep K D) hS hN he,
    maximalSlope_eq_of_completed_isometry _ _ (PiTensorProduct.tmulEquivDep K D) hS hN he⟩

end AdelicVectorBundle

end ArakelovGeometry
