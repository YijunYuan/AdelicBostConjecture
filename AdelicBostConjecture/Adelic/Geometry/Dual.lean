/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.InvariantTheory.Plucker
public import AdelicBostConjecture.Geometry.Plucker.Nonvanishing

/-!
# Tensor duality and the full special-linear action

The canonical tensor-duality map intertwines transposes on each factor with
the transpose of the tensor action. Surjectivity of transpose on the special
linear group then identifies quotient Plücker semistability with semistability
of the actual dual inclusion into the tensor product of the dual factors.
-/

@[expose] public section

noncomputable section

namespace AdelicBostConjecture.Adelic.Geometry

open Module PiTensorProduct
open ArakelovGeometry.InvariantTheory
open scoped TensorProduct

variable {K : Type*} [Field K] {ι : Type*} [Finite ι]
  (E : ι → Type*) [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]
  [∀ i, FiniteDimensional K (E i)]

/-- Tensor duality intertwines factor transposes and the transpose tensor action. -/
theorem dualDistrib_tensorSL (g : ∀ i, SpecialLinearGroup K (E i)) :
    (dualDistribEquivOfProjective K E).toLinearMap ∘ₗ
      tensorSLRepresentation (fun i ↦ Dual K (E i)) (fun i ↦ (g i).dualMap) =
    (tensorSLRepresentation E g).dualMap ∘ₗ
      (dualDistribEquivOfProjective K E).toLinearMap := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro f
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  change dualDistribEquivOfProjective K E
      (map (fun i ↦ (g i : E i →ₗ[K] E i).dualMap) (tprod K f)) (tprod K x) =
    dualDistribEquivOfProjective K E (tprod K f)
      (map (fun i ↦ (g i : E i →ₗ[K] E i)) (tprod K x))
  simp only [map_tprod, dualDistribEquivOfProjective_tprod_tprod]
  rfl

/-- Quotient semistability gives semistability of the dual inclusion under the
full product of special linear groups of the dual factors. -/
theorem isPluckerSemistable_dualTensor_of_isQuotientSemistable
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (q : (⨂[K] i, E i) →ₗ[K] V)
    (h : IsQuotientSemistable (tensorSLRepresentation E) q) :
    IsPluckerSemistable (tensorSLRepresentation (fun i ↦ Dual K (E i)))
      ((dualDistribEquivOfProjective K E).symm.toLinearMap ∘ₗ q.dualMap) := by
  classical
  let s := Module.finrank K (Dual K V)
  let e := dualDistribEquivOfProjective K E
  let f := exteriorPower.map s e.toLinearMap
  let ρ := exteriorRepresentation s (tensorSLRepresentation (k := K) E).dual
  let τ := exteriorRepresentation s (tensorSLRepresentation (k := K) (fun i ↦ Dual K (E i)))
  have hf (a : ∀ i, SpecialLinearGroup K (Dual K (E i))) :
      ∃ g : ∀ i, SpecialLinearGroup K (E i), f ∘ₗ τ a = ρ g ∘ₗ f := by
    choose g hg using fun i ↦ AdelicBostConjecture.Geometry.specialLinear_dualMap_surjective (a i)
    refine ⟨fun i ↦ (g i)⁻¹, ?_⟩
    change exteriorPower.map s e.toLinearMap ∘ₗ exteriorPower.map s
      (tensorSLRepresentation (fun i ↦ Dual K (E i)) a) =
      exteriorPower.map s (tensorSLRepresentation E g).dualMap ∘ₗ
        exteriorPower.map s e.toLinearMap
    rw [← exteriorPower.map_comp, ← exteriorPower.map_comp]
    congr 1
    rw [← show (fun i ↦ (g i).dualMap) = a from funext hg]
    exact dualDistrib_tensorSL E g
  obtain ⟨η, hη, d, p, hd, hp, hi, hn⟩ := h
  let b := Module.Free.chooseBasis K (⋀[K]^s (Dual K (⨂[K] i, E i)))
  let c := Module.Free.chooseBasis K (⋀[K]^s (⨂[K] i, Dual K (E i)))
  refine ⟨η, hη, d, polynomialPullback b c f p, hd,
    polynomialPullback_isHomogeneous b c f hp, ?_, ?_⟩
  · intro a x
    obtain ⟨g, hg⟩ := hf a
    rw [eval_polynomialPullback, eval_polynomialPullback]
    change MvPolynomial.eval (b.repr ((f ∘ₗ τ a) x)) p = _
    rw [hg]
    exact hi g (f x)
  · rw [eval_polynomialPullback]
    have hv : f (exteriorPower.map s (e.symm.toLinearMap ∘ₗ q.dualMap) η) =
        exteriorPower.map s q.dualMap η := by
      change (exteriorPower.map s e.toLinearMap)
        (exteriorPower.map s (e.symm.toLinearMap ∘ₗ q.dualMap) η) = _
      rw [← LinearMap.comp_apply, ← exteriorPower.map_comp]
      simp
    change MvPolynomial.eval (b.repr
      (f (exteriorPower.map s (e.symm.toLinearMap ∘ₗ q.dualMap) η))) p ≠ 0
    rw [hv]
    exact hn

end AdelicBostConjecture.Adelic.Geometry
