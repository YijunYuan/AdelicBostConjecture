/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Dual.Map
public import ArakelovGeometry.InvariantTheory.Linearization
public import AdelicBostConjecture.Tensor.Dual.RegroupBaseChange

/-!
# Scalar extension of the original tensor-dual inclusion

The two canonical dual base-change maps agree. Together with tensor-duality
naturality this identifies the base change of the original dual inclusion with
the dual of the base-changed quotient, using the full scalar-extension maps.
-/

@[expose] public section

noncomputable section

namespace AdelicBostConjecture.Adelic.Geometry

open Module PiTensorProduct ArakelovGeometry.InvariantTheory
open scoped TensorProduct

variable {K : Type*} [Field K] (L : Type*) [Field L] [Algebra K L]

/-- The finite-projective and finite-dimensional dual base-change equivalences
agree on all vectors, as witnessed by their canonical evaluation formulas. -/
theorem dualBaseChangeEquiv_eq (V : Type*) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] :
    ArakelovGeometry.dualBaseChangeEquiv K L V = Arithmetic.dualBaseChangeEquiv K L V := by
  apply LinearEquiv.toLinearMap_injective
  apply TensorProduct.AlgebraTensorModule.ext
  intro a ℓ
  apply TensorProduct.AlgebraTensorModule.ext
  intro b x
  simp

variable {ι : Type*} [Finite ι] (E : ι → Type*)
  [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]
  [∀ i, FiniteDimensional K (E i)]

/-- Scalar extension preserves the actual dual tensor inclusion of a quotient. -/
theorem dualTensorInclusion_baseChange
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (q : (⨂[K] i, E i) →ₗ[K] V) :
    (PiTensorProduct.congr (fun i ↦ Arithmetic.dualBaseChangeEquiv K L (E i))).toLinearMap ∘ₗ
      (Tensor.baseChangeEquiv K L (fun i ↦ Dual K (E i))).toLinearMap ∘ₗ
      ((dualDistribEquivOfProjective K E).symm.toLinearMap ∘ₗ q.dualMap).baseChange L =
    (dualDistribEquivOfProjective L (fun i ↦ L ⊗[K] E i)).symm.toLinearMap ∘ₗ
      ((q.baseChange L) ∘ₗ (Tensor.baseChangeEquiv K L E).symm.toLinearMap).dualMap ∘ₗ
      (Arithmetic.dualBaseChangeEquiv K L V).toLinearMap := by
  apply LinearMap.ext
  intro z
  apply (dualDistribEquivOfProjective L (fun i ↦ L ⊗[K] E i)).injective
  change dualDistribEquivOfProjective L (fun i ↦ L ⊗[K] E i)
      (map (fun i ↦ (Arithmetic.dualBaseChangeEquiv K L (E i)).toLinearMap)
        (Tensor.baseChangeEquiv K L (fun i ↦ Dual K (E i))
          (((dualDistribEquivOfProjective K E).symm.toLinearMap ∘ₗ q.dualMap).baseChange L z))) =
    dualDistribEquivOfProjective L (fun i ↦ L ⊗[K] E i)
      ((dualDistribEquivOfProjective L (fun i ↦ L ⊗[K] E i)).symm _)
  rw [LinearEquiv.apply_symm_apply, ← Tensor.dualDistrib_baseChange]
  have hz : (dualDistribEquivOfProjective K E).toLinearMap.baseChange L
      (((dualDistribEquivOfProjective K E).symm.toLinearMap ∘ₗ q.dualMap).baseChange L z) =
      q.dualMap.baseChange L z := by
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
    simp
  rw [hz]
  change (Arithmetic.dualBaseChangeEquiv K L (⨂[K] i, E i)
    (q.dualMap.baseChange L z)).comp (Tensor.baseChangeEquiv K L E).symm.toLinearMap = _
  rw [← dualBaseChangeEquiv_eq, ArakelovGeometry.dualBaseChangeEquiv_dualMap,
    dualBaseChangeEquiv_eq]
  rfl

omit [Finite ι] [∀ i, FiniteDimensional K (E i)] in
/-- Factor isomorphisms intertwine the full tensor SL representations, with
the acting groups identified by conjugation in each factor. -/
theorem tensorSLRepresentation_congr
    {D : ι → Type*} [∀ i, AddCommGroup (D i)] [∀ i, Module K (D i)]
    (e : ∀ i, D i ≃ₗ[K] E i) (g : ∀ i, SpecialLinearGroup K (D i)) :
    (PiTensorProduct.congr e).toLinearMap ∘ₗ tensorSLRepresentation D g =
      tensorSLRepresentation E (fun i ↦ SpecialLinearGroup.congr_linearEquiv (e i) (g i)) ∘ₗ
        (PiTensorProduct.congr e).toLinearMap := by
  change map (fun i ↦ (e i).toLinearMap) ∘ₗ map (fun i ↦ (g i : D i →ₗ[K] D i)) =
    map (fun i ↦ (SpecialLinearGroup.congr_linearEquiv (e i) (g i) : E i →ₗ[K] E i)) ∘ₗ
      map (fun i ↦ (e i).toLinearMap)
  rw [← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp]
  congr 1
  funext i
  ext x
  simp

end AdelicBostConjecture.Adelic.Geometry
