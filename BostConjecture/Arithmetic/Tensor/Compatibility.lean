/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Tensor.BinaryMetric
public import BostConjecture.Arithmetic.Submodule.QuotientMetric

/-!
# Tensor metrics and induced metrics

The existing binary arithmetic tensor metric is identified on the entire
complex fiber with the canonical binary Hilbert form. Scalar extension and
pullback are compatible with the actual tensor maps.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace BostConjecture.Arithmetic

universe u
variable {K : Type*} [Field K] [NumberField K]
variable {M N P : Type u} [AddCommGroup M] [Module (𝓞 K) M]
    [AddCommGroup N] [Module (𝓞 K) N] [AddCommGroup P] [Module (𝓞 K) P]

omit [NumberField K] in
lemma span_fiberSection (σ : K →+* ℂ) :
    Submodule.span ℂ (Set.range (fiberSection M σ)) = ⊤ := by
  let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  apply top_unique
  intro z hz
  clear hz
  induction z using TensorProduct.inductionOn with
  | tmul c x =>
    have hx : fiberSection M σ x ∈ Submodule.span ℂ (Set.range (fiberSection M σ)) :=
      Submodule.subset_span ⟨x, rfl⟩
    simpa [fiberSection, smul_tmul'] using
      (Submodule.span ℂ (Set.range (fiberSection M σ))).smul_mem c hx
  | add x y hx hy => exact Submodule.add_mem _ hx hy

omit [NumberField K] in
lemma span_fiberSection_tmul (σ : K →+* ℂ) :
    Submodule.span ℂ (Set.range (fun xy : M × N =>
      fiberSection (M ⊗[𝓞 K] N) σ (xy.1 ⊗ₜ[𝓞 K] xy.2))) = ⊤ := by
  let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  apply top_unique
  intro z hz
  clear hz
  induction z using TensorProduct.inductionOn with
  | tmul c z =>
    have hz : fiberSection (M ⊗[𝓞 K] N) σ z ∈ Submodule.span ℂ
        (Set.range (fun xy : M × N => fiberSection _ σ (xy.1 ⊗ₜ[𝓞 K] xy.2))) := by
      induction z using TensorProduct.inductionOn with
      | tmul x y => exact Submodule.subset_span ⟨(x, y), rfl⟩
      | add x y hx hy => simpa [fiberSection, tmul_add] using Submodule.add_mem _ hx hy
    simpa [fiberSection, smul_tmul'] using Submodule.smul_mem _ c hz
  | add x y hx hy => exact Submodule.add_mem _ hx hy

omit [NumberField K] in
/-- The canonical binary tensor scalar-extension equivalence. -/
def binaryTensorFiberEquiv (σ : K →+* ℂ) :
    ComplexFiber (M ⊗[𝓞 K] N) σ ≃ₗ[ℂ] ComplexFiber M σ ⊗[ℂ] ComplexFiber N σ :=
  letI : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  AlgebraTensorModule.distribBaseChange (𝓞 K) ℂ M N

omit [NumberField K] in
@[simp]
lemma binaryTensorFiberEquiv_section (σ : K →+* ℂ) (x : M) (y : N) :
    binaryTensorFiberEquiv σ (fiberSection _ σ (x ⊗ₜ[𝓞 K] y)) =
      fiberSection M σ x ⊗ₜ[ℂ] fiberSection N σ y := by
  let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  exact AlgebraTensorModule.distribBaseChange_tmul (𝓞 K) ℂ x y 1

omit [NumberField K] in
/-- Binary scalar extension intertwines the right tensor of any integral map. -/
lemma binaryTensorFiberEquiv_rTensor (f : M →ₗ[𝓞 K] P) (σ : K →+* ℂ)
    (z : ComplexFiber (M ⊗[𝓞 K] N) σ) :
    binaryTensorFiberEquiv σ (fiberMap (f.rTensor N) σ z) =
      (fiberMap f σ).rTensor (ComplexFiber N σ) (binaryTensorFiberEquiv σ z) := by
  let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  induction z using TensorProduct.inductionOn with
  | tmul c z =>
    have hz : binaryTensorFiberEquiv σ (fiberMap (f.rTensor N) σ (fiberSection _ σ z)) =
        (fiberMap f σ).rTensor (ComplexFiber N σ)
          (binaryTensorFiberEquiv σ (fiberSection _ σ z)) := by
      induction z using TensorProduct.inductionOn with
      | tmul x y => simp
      | add x y hx hy => simpa only [fiberSection, tmul_add, map_add] using congrArg₂ (· + ·) hx hy
    have hc : c ⊗ₜ[𝓞 K] z = c • fiberSection _ σ z := by simp [fiberSection, smul_tmul']
    simpa only [hc, map_smul] using congrArg (c • ·) hz
  | add x y hx hy => simp only [map_add, hx, hy]

namespace HermitianMetric

/-- The existing tensor form has the binary product formula on integral sections. -/
lemma tensor_inner_section (h : HermitianMetric K M)
    (g : HermitianMetric K N) (σ : K →+* ℂ) (x x' : M) (y y' : N) :
    ((h ⊗[𝓞 K] g).fiber σ).inner (fiberSection _ σ (x ⊗ₜ[𝓞 K] y))
      (fiberSection _ σ (x' ⊗ₜ[𝓞 K] y')) =
      (h.fiber σ).inner (fiberSection M σ x) (fiberSection M σ x') *
        (g.fiber σ).inner (fiberSection N σ y) (fiberSection N σ y') := by
  change (tensorFiber (fun i : Unit ⊕ Unit => Sum.casesOn i (fun _ => h) (fun _ => g)) σ).inner
    (fiberSection _ σ (binaryTensorEquiv (𝓞 K) M N (x ⊗ₜ[𝓞 K] y)))
    (fiberSection _ σ (binaryTensorEquiv (𝓞 K) M N (x' ⊗ₜ[𝓞 K] y'))) = _
  rw [binaryTensorEquiv_tmul, binaryTensorEquiv_tmul]
  exact (tensorFiber_inner_tprod _ σ _ _).trans (by simp [Fintype.prod_sum_type])

/-- The full complex scalar-extension equivalence preserves the Hilbert form. -/
lemma tensor_inner (h : HermitianMetric K M)
    (g : HermitianMetric K N) (σ : K →+* ℂ)
    (x y : ComplexFiber (M ⊗[𝓞 K] N) σ) :
    ((h ⊗[𝓞 K] g).fiber σ).inner x y =
      (Tensor.binaryCore (h.fiber σ) (g.fiber σ)).inner
        (binaryTensorFiberEquiv σ x) (binaryTensorFiberEquiv σ y) := by
  apply Tensor.inner_ext_of_span (fun xy : M × N => fiberSection _ σ (xy.1 ⊗ₜ[𝓞 K] xy.2))
    (span_fiberSection_tmul σ) ((h ⊗[𝓞 K] g).fiber σ)
    (Tensor.binaryCore (h.fiber σ) (g.fiber σ)) LinearMap.id
    (binaryTensorFiberEquiv σ).toLinearMap _ x y
  intro a b
  simpa only [LinearMap.id_apply, LinearEquiv.coe_coe, binaryTensorFiberEquiv_section,
    Tensor.binaryCore_inner_tmul] using tensor_inner_section h g σ a.1 b.1 a.2 b.2

omit [NumberField K] in
/-- Equality of all fiber pairings determines the Hermitian metric. -/
@[ext]
lemma ext_inner {h g : HermitianMetric K M}
    (he : ∀ σ x y, (h.fiber σ).inner x y = (g.fiber σ).inner x y) : h = g := by
  have hf : h.fiber = g.fiber := by
    funext σ
    have hi : (h.fiber σ).inner = (g.fiber σ).inner := funext fun x => funext fun y => he σ x y
    generalize h.fiber σ = c at hi ⊢
    generalize g.fiber σ = d at hi ⊢
    rcases c with ⟨⟨⟨ci⟩, cs, cp, ca, cm⟩, cd⟩
    rcases d with ⟨⟨⟨di⟩, ds, dp, da, dm⟩, dd⟩
    cases hi
    rfl
  cases h
  cases g
  cases hf
  rfl

omit [NumberField K] in
/-- It suffices to compare pairings on the spanning integral sections. -/
lemma ext_section_inner {h g : HermitianMetric K M}
    (he : ∀ σ x y, (h.fiber σ).inner (fiberSection M σ x) (fiberSection M σ y) =
      (g.fiber σ).inner (fiberSection M σ x) (fiberSection M σ y)) : h = g := by
  apply ext_inner
  intro σ x y
  exact Tensor.inner_ext_of_span (fiberSection M σ) (span_fiberSection σ)
    (h.fiber σ) (g.fiber σ) LinearMap.id LinearMap.id (he σ) x y

/-- Tensoring an integral injection commutes with the actual induced metric. -/
lemma tensor_pullback [Module.Flat (𝓞 K) N]
    (h : HermitianMetric K P) (g : HermitianMetric K N)
    (f : M →ₗ[𝓞 K] P) (hf : Function.Injective f) :
    (h ⊗[𝓞 K] g).pullback (f.rTensor N) (Module.Flat.rTensor_preserves_injective_linearMap f hf) =
      (h.pullback f hf) ⊗[𝓞 K] g := by
  apply ext_inner
  intro σ x y
  apply Tensor.inner_ext_of_span (fun xy : M × N => fiberSection _ σ (xy.1 ⊗ₜ[𝓞 K] xy.2))
    (span_fiberSection_tmul σ) (((h ⊗[𝓞 K] g).pullback (f.rTensor N)
      (Module.Flat.rTensor_preserves_injective_linearMap f hf)).fiber σ)
    (((h.pullback f hf) ⊗[𝓞 K] g).fiber σ) LinearMap.id LinearMap.id _ x y
  intro a b
  simp only [LinearMap.id_apply, pullback_inner, fiberMap_section,
    LinearMap.rTensor_tmul, tensor_inner_section]

end HermitianMetric
end BostConjecture.Arithmetic
