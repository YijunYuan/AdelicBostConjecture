/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import AdelicBostConjecture.Adelic.Induction.TensorTransport
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
    [hξ : ∀ i, (ξ i).IsHermitian] (i₀ : ι) (ω : S.Ω)
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
  [hS : S.NormMeasurabilityHypotheses]
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
theorem slopes_orthogonalTensor_reindex {κ : Type*} [Fintype κ]
    (V : ι → AdelicVectorBundle S)
    [hV : ∀ i, (V i).IsHermitian] (e : ι ≃ κ) :
    (orthogonalTensorOfNormMeasurability V).slope =
        (orthogonalTensorOfNormMeasurability (fun j => V (e.symm j))).slope ∧
    (orthogonalTensorOfNormMeasurability V).maximalSlope =
        (orthogonalTensorOfNormMeasurability (fun j => V (e.symm j))).maximalSlope := by
  have he := NormFamily.orthogonalTensor_norm_reindex
    (fun i => (V i).toNormFamily) e
  let A := orthogonalTensorOfNormMeasurability V
  let B := orthogonalTensorOfNormMeasurability (fun j ↦ V (e.symm j))
  exact ⟨slope_eq_of_completed_isometry A B (PiTensorProduct.reindex K (fun i ↦ V i) e) he,
    maximalSlope_eq_of_completed_isometry A B (PiTensorProduct.reindex K (fun i ↦ V i) e) he⟩

/-- The one-factor finite tensor has exactly the slopes of its factor. -/
theorem slopes_orthogonalTensor_subsingleton [Subsingleton ι]
    (V : ι → AdelicVectorBundle S)
    [hV : ∀ i, (V i).IsHermitian] (i₀ : ι) :
    (orthogonalTensorOfNormMeasurability V).slope =
        (V i₀).slope ∧
    (orthogonalTensorOfNormMeasurability V).maximalSlope =
        (V i₀).maximalSlope := by
  have he := NormFamily.orthogonalTensor_norm_subsingletonEquiv
    (fun i => (V i).toNormFamily) i₀
  let A := orthogonalTensorOfNormMeasurability V
  exact ⟨slope_eq_of_completed_isometry A (V i₀)
      (PiTensorProduct.subsingletonEquiv (R := K) (s := (fun i ↦ V i)) i₀) he,
    maximalSlope_eq_of_completed_isometry A (V i₀)
      (PiTensorProduct.subsingletonEquiv (R := K) (s := (fun i ↦ V i)) i₀) he⟩

/-- The upstream grouping isometry for index types in the same universe. -/
private theorem slopes_orthogonalTensor_sum_same_universe {κ : Type wι} [Fintype κ]
    (V : (ι ⊕ κ) → AdelicVectorBundle S)
    [hV : ∀ i, (V i).IsHermitian] :
    let A := orthogonalTensorOfNormMeasurability (fun i => V (.inl i))
    let B := orthogonalTensorOfNormMeasurability (fun j => V (.inr j))
    (A ⊗ʰ B).slope =
        (orthogonalTensorOfNormMeasurability V).slope ∧
    (A ⊗ʰ B).maximalSlope =
        (orthogonalTensorOfNormMeasurability V).maximalSlope := by
  have he := NormFamily.orthogonalTensor_norm_tmulEquivDep
    (fun i => (V i).toNormFamily)
  let A := orthogonalTensorOfNormMeasurability (fun i ↦ V (.inl i))
  let B := orthogonalTensorOfNormMeasurability (fun j ↦ V (.inr j))
  let C := orthogonalTensorOfNormMeasurability V
  exact ⟨slope_eq_of_completed_isometry (A ⊗ʰ B) C
      (PiTensorProduct.tmulEquivDep K (fun i ↦ V i)) he,
    maximalSlope_eq_of_completed_isometry (A ⊗ʰ B) C
      (PiTensorProduct.tmulEquivDep K (fun i ↦ V i)) he⟩


/-- Canonical grouping preserves both slopes, with independent index universes. -/
theorem slopes_orthogonalTensor_sum {κ : Type*} [Fintype κ]
    (V : (ι ⊕ κ) → AdelicVectorBundle S)
    [hV : ∀ i, (V i).IsHermitian] :
    let A := orthogonalTensorOfNormMeasurability (fun i ↦ V (.inl i))
    let B := orthogonalTensorOfNormMeasurability (fun j ↦ V (.inr j))
    (A ⊗ʰ B).slope = (orthogonalTensorOfNormMeasurability V).slope ∧
    (A ⊗ʰ B).maximalSlope = (orthogonalTensorOfNormMeasurability V).maximalSlope := by
  classical
  let eι := Fintype.equivFin ι
  let eκ := Fintype.equivFin κ
  let e := Equiv.sumCongr eι eκ
  let A := orthogonalTensorOfNormMeasurability (fun i ↦ V (.inl i))
  let B := orthogonalTensorOfNormMeasurability (fun j ↦ V (.inr j))
  let A' := orthogonalTensorOfNormMeasurability (fun i ↦ V (.inl (eι.symm i)))
  let B' := orthogonalTensorOfNormMeasurability (fun j ↦ V (.inr (eκ.symm j)))
  let f := PiTensorProduct.reindex K (fun i ↦ V (.inl i)) eι
  let g := PiTensorProduct.reindex K (fun j ↦ V (.inr j)) eκ
  have hf := NormFamily.orthogonalTensor_norm_reindex
    (fun i ↦ (V (.inl i)).toNormFamily) eι
  have hg := NormFamily.orthogonalTensor_norm_reindex
    (fun j ↦ (V (.inr j)).toNormFamily) eκ
  have ht (ω : S.Ω) (z) : (A' ⊗ʰ B').norm ω
      ((TensorProduct.congr f g).toLinearMap.baseChange (S.ϕ ω).Completion z) =
        (A ⊗ʰ B).norm ω z :=
    NormFamily.orthogonalTensorPair_norm_congr
      A.toNormFamily B.toNormFamily A'.toNormFamily B'.toNormFamily f g ω (hf ω) (hg ω) z
  have hs := slope_eq_of_completed_isometry (A ⊗ʰ B) (A' ⊗ʰ B')
    (TensorProduct.congr f g) ht
  have hm := maximalSlope_eq_of_completed_isometry (A ⊗ʰ B) (A' ⊗ʰ B')
    (TensorProduct.congr f g) ht
  have hgroup := slopes_orthogonalTensor_sum_same_universe (fun j ↦ V (e.symm j))
  have hreindex := slopes_orthogonalTensor_reindex V e
  exact ⟨hs.trans (hgroup.1.trans hreindex.1.symm),
    hm.trans (hgroup.2.trans hreindex.2.symm)⟩

end AdelicVectorBundle

end ArakelovGeometry
