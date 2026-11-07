/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Bundle.Basic
public import BostConjecture.Tensor.Metric.Basic

/-!
# Intrinsic finite tensor Hermitian metrics

The canonical scalar-extension equivalence transports the Hilbert tensor
form to the actual arithmetic tensor module. Its conjugation compatibility
is proved on integral pure tensors and extended by sesquilinearity.
-/

@[expose] public section

noncomputable section

open NumberField PiTensorProduct
open scoped TensorProduct BostConjecture.Tensor

namespace BostConjecture.Arithmetic

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι]
variable (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module (𝓞 K) (M i)]

/-- The canonical complex fiber equivalence for an arithmetic finite tensor product. -/
def tensorFiberEquiv (σ : K →+* ℂ) :
    ComplexFiber (⨂[𝓞 K] i, M i) σ ≃ₗ[ℂ] (⨂[ℂ] i, ComplexFiber (M i) σ) :=
  letI : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  Tensor.baseChangeEquiv (𝓞 K) ℂ M

@[simp]
lemma tensorFiberEquiv_section_tprod (σ : K →+* ℂ) (x : ∀ i, M i) :
    tensorFiberEquiv M σ (fiberSection _ σ (tprod (𝓞 K) x)) =
      tprod ℂ (fun i => fiberSection (M i) σ (x i)) := by
  let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  exact (Tensor.baseChangeEquiv_tmul (𝓞 K) ℂ M 1 x).trans (one_smul _ _)

variable {M}
namespace HermitianMetric

/-- The positive tensor form on the actual arithmetic complex fiber. -/
@[instance_reducible]
def tensorFiber (h : ∀ i, HermitianMetric K (M i)) (σ : K →+* ℂ) :
    InnerProductSpace.Core ℂ (ComplexFiber (⨂[𝓞 K] i, M i) σ) := by
  letI : ∀ i, InnerProductSpace.Core ℂ (ComplexFiber (M i) σ) := fun i => (h i).fiber σ
  letI : ∀ i, NormedAddCommGroup (ComplexFiber (M i) σ) := fun i =>
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber (M i) σ)
  letI : ∀ i, InnerProductSpace ℂ (ComplexFiber (M i) σ) := fun i =>
    InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber (M i) σ))
  letI := InnerProductSpace.Core.toNormedAddCommGroup
    (𝕜 := ℂ) (F := ⨂[ℂ] i, ComplexFiber (M i) σ)
  letI := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (⨂[ℂ] i, ComplexFiber (M i) σ))
  letI := NormedAddCommGroup.induced _ _ (tensorFiberEquiv M σ) (tensorFiberEquiv M σ).injective
  letI := InnerProductSpace.induced (tensorFiberEquiv M σ).toLinearMap
  exact InnerProductSpace.toCore

/-- Pairing integral pure tensors multiplies the factor pairings. -/
lemma tensorFiber_inner_tprod (h : ∀ i, HermitianMetric K (M i))
    (σ : K →+* ℂ) (x y : ∀ i, M i) :
    (tensorFiber h σ).inner (fiberSection _ σ (tprod (𝓞 K) x))
      (fiberSection _ σ (tprod (𝓞 K) y)) =
        ∏ i, ((h i).fiber σ).inner (fiberSection (M i) σ (x i))
          (fiberSection (M i) σ (y i)) := by
  let : ∀ i, InnerProductSpace.Core ℂ (ComplexFiber (M i) σ) := fun i => (h i).fiber σ
  let : ∀ i, NormedAddCommGroup (ComplexFiber (M i) σ) := fun i =>
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber (M i) σ)
  let : ∀ i, InnerProductSpace ℂ (ComplexFiber (M i) σ) := fun i =>
    InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber (M i) σ))
  change (Tensor.hilbertCore (fun i => ComplexFiber (M i) σ)).inner
    (tensorFiberEquiv M σ _) (tensorFiberEquiv M σ _) = _
  rw [tensorFiberEquiv_section_tprod, tensorFiberEquiv_section_tprod,
    Tensor.hilbertCore_inner_tprod, finprod_eq_prod_of_fintype]

/-- Tensor forms inherit conjugation on arbitrary integral tensor sections. -/
lemma tensorFiber_conjugate (h : ∀ i, HermitianMetric K (M i))
    (σ : K →+* ℂ) (x y : ⨂[𝓞 K] i, M i) :
    (tensorFiber h (ComplexEmbedding.conjugate σ)).inner
      (fiberSection _ (ComplexEmbedding.conjugate σ) x)
      (fiberSection _ (ComplexEmbedding.conjugate σ) y) =
        star ((tensorFiber h σ).inner (fiberSection _ σ x) (fiberSection _ σ y)) := by
  let : InnerProductSpace.Core ℂ (ComplexFiber (⨂[𝓞 K] i, M i) σ) := tensorFiber h σ
  let : InnerProductSpace.Core ℂ
    (ComplexFiber (⨂[𝓞 K] i, M i) (ComplexEmbedding.conjugate σ)) :=
      tensorFiber h (ComplexEmbedding.conjugate σ)
  have hp (x y : ∀ i, M i) :
      (tensorFiber h (ComplexEmbedding.conjugate σ)).inner
        (fiberSection _ (ComplexEmbedding.conjugate σ) (tprod (𝓞 K) x))
        (fiberSection _ (ComplexEmbedding.conjugate σ) (tprod (𝓞 K) y)) =
      star ((tensorFiber h σ).inner (fiberSection _ σ (tprod (𝓞 K) x))
        (fiberSection _ σ (tprod (𝓞 K) y))) := by
    simp only [tensorFiber_inner_tprod, HermitianMetric.conjugate, star_prod]
  induction x using PiTensorProduct.induction_on with
  | smul_tprod a x =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod b y =>
      simp only [fiberSection_smul, InnerProductSpace.Core.inner_smul_left,
        InnerProductSpace.Core.inner_smul_right, hp, ComplexEmbedding.conjugate_coe_eq,
        RCLike.star_def, map_mul]
    | add y z hy hz =>
      simpa only [fiberSection, TensorProduct.tmul_add,
        InnerProductSpace.Core.inner_add_right, star_add] using congrArg₂ (· + ·) hy hz
  | add x z hx hz =>
    simpa only [fiberSection, TensorProduct.tmul_add,
      InnerProductSpace.Core.inner_add_left, star_add] using congrArg₂ (· + ·) hx hz

/-- The intrinsic Hermitian metric on a finite integral tensor product. -/
def piTensor (h : ∀ i, HermitianMetric K (M i)) :
    HermitianMetric K (⨂[𝓞 K] i, M i) where
  fiber := tensorFiber h
  conjugate := tensorFiber_conjugate h

/-- The norm of an integral pure tensor is the product of its factor norms. -/
lemma sectionNorm_piTensor_tprod (h : ∀ i, HermitianMetric K (M i))
    (σ : K →+* ℂ) (x : ∀ i, M i) :
    (piTensor h).sectionNorm σ (tprod (𝓞 K) x) = ∏ i, (h i).sectionNorm σ (x i) := by
  let : ∀ i, InnerProductSpace.Core ℂ (ComplexFiber (M i) σ) := fun i => (h i).fiber σ
  have hi (i : ι) :
      (((((h i).fiber σ).inner (fiberSection (M i) σ (x i))
        (fiberSection (M i) σ (x i))).re : ℝ) : ℂ) =
      ((h i).fiber σ).inner (fiberSection (M i) σ (x i)) (fiberSection (M i) σ (x i)) := by
    apply Complex.ext
    · rfl
    · exact (InnerProductSpace.Core.inner_self_im (𝕜 := ℂ) _).symm
  change Real.sqrt (((tensorFiber h σ).inner _ _).re) = _
  rw [tensorFiber_inner_tprod]
  have he : (∏ i, ((h i).fiber σ).inner (fiberSection (M i) σ (x i))
      (fiberSection (M i) σ (x i))) =
      ((∏ i, (((h i).fiber σ).inner (fiberSection (M i) σ (x i))
        (fiberSection (M i) σ (x i))).re : ℝ) : ℂ) := by
    rw [Complex.ofReal_prod]
    exact Finset.prod_congr rfl (fun i _ => (hi i).symm)
  rw [he, Complex.ofReal_re]
  exact Real.sqrt_prod _ (fun i _ => ((h i).fiber σ).re_inner_nonneg _)

end HermitianMetric
end BostConjecture.Arithmetic
