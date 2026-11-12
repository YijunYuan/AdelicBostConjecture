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
    [hN : S.IsArchimedeanNormalized]
    (hξ : ∀ i, (ξ i).IsHermitian) (i₀ : ι) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] (⨂[K] i, E i)) :
    (ξ i₀).norm ω
      ((PiTensorProduct.subsingletonEquiv (R := K) (s := E) i₀).toLinearMap.baseChange
        (S.ϕ ω).Completion z) = (orthogonalTensor ξ).norm ω z := by
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
  have h := orthogonalTensor_norm_tprod ξ ω f
  rw [hf, LinearEquiv.symm_apply_apply] at h
  rw [Fintype.prod_eq_single i₀ (fun i hi => (hi (Subsingleton.elim i i₀)).elim)] at h
  change (ξ i₀).norm ω (e.toLinearMap.baseChange L z) = _
  rw [he]
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, f, Function.update_self] using h.symm

end NormFamily

namespace AdelicVectorBundle

variable [S.IsProper]
  [hS : S.HasMeasurableBase]
  [hN : S.IsArchimedeanNormalized]

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
    (hV : ∀ i, (V i).IsHermitian) (e : ι ≃ κ) :
    (orthogonalTensorOfMeasurableBase V).slope =
        (orthogonalTensorOfMeasurableBase (fun j => V (e.symm j))).slope ∧
    (orthogonalTensorOfMeasurableBase V).maximalSlope =
        (orthogonalTensorOfMeasurableBase (fun j => V (e.symm j))).maximalSlope := by
  have he := NormFamily.orthogonalTensor_norm_reindex
    (fun i => (V i).toNormFamily) e
  exact ⟨slope_eq_of_completed_isometry _ _ (PiTensorProduct.reindex K E e) he,
    maximalSlope_eq_of_completed_isometry _ _ (PiTensorProduct.reindex K E e) he⟩

/-- The one-factor finite tensor has exactly the slopes of its factor. -/
theorem slopes_orthogonalTensor_subsingleton [Subsingleton ι]
    (V : ∀ i, AdelicVectorBundle S (E i))
    (hV : ∀ i, (V i).IsHermitian) (i₀ : ι) :
    (orthogonalTensorOfMeasurableBase V).slope =
        (V i₀).slope ∧
    (orthogonalTensorOfMeasurableBase V).maximalSlope =
        (V i₀).maximalSlope := by
  have he := NormFamily.orthogonalTensor_norm_subsingletonEquiv
    (fun i => (V i).toNormFamily) hV i₀
  exact ⟨slope_eq_of_completed_isometry _ _
      (PiTensorProduct.subsingletonEquiv (R := K) (s := E) i₀) he,
    maximalSlope_eq_of_completed_isometry _ _
      (PiTensorProduct.subsingletonEquiv (R := K) (s := E) i₀) he⟩

/-- Canonical grouping preserves the mean and maximal slopes on the actual norms. -/
theorem slopes_orthogonalTensor_sum {κ : Type wι} [Fintype κ]
    {D : ι ⊕ κ → Type w} [∀ i, AddCommGroup (D i)] [∀ i, Module K (D i)]
    [∀ i, FiniteDimensional K (D i)] (V : ∀ i, AdelicVectorBundle S (D i))
    (hV : ∀ i, (V i).IsHermitian) :
    let A := orthogonalTensorOfMeasurableBase (fun i => V (.inl i))
    let B := orthogonalTensorOfMeasurableBase (fun j => V (.inr j))
    (A.orthogonalTensorPair B).slope =
        (orthogonalTensorOfMeasurableBase V).slope ∧
    (A.orthogonalTensorPair B).maximalSlope =
        (orthogonalTensorOfMeasurableBase V).maximalSlope := by
  have he := NormFamily.orthogonalTensor_norm_tmulEquivDep
    (fun i => (V i).toNormFamily)
  exact ⟨slope_eq_of_completed_isometry _ _ (PiTensorProduct.tmulEquivDep K D) he,
    maximalSlope_eq_of_completed_isometry _ _ (PiTensorProduct.tmulEquivDep K D) he⟩

end AdelicVectorBundle

end ArakelovGeometry
