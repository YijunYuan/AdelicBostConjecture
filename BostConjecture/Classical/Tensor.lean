/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Tensor.Algebra.BaseChange
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import BostConjecture.Classical.Submodule

/-!
# Tensor products of the original Hermitian metrics

The finite tensor metric induces the binary metric and the original
`h ⊗[𝓞 K] g` notation.
-/

@[expose] public section
noncomputable section

section TensorInnerProduct

namespace BostConjecture.Tensor

open PiTensorProduct
open scoped TensorProduct

@[instance_reducible]
private def coreOfEquiv {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] (e : V ≃ₗ[ℂ] W) :
    InnerProductSpace.Core ℂ V := by
  let := NormedAddCommGroup.induced V W e e.injective
  let := InnerProductSpace.induced e.toLinearMap
  exact InnerProductSpace.toCore

private theorem coreOfEquiv_inner {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] (e : V ≃ₗ[ℂ] W) (x y : V) :
    (coreOfEquiv e).inner x y = inner ℂ (e x) (e y) := rfl

variable {ι : Type*} (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℂ (E i)]

/-- Existence of the positive tensor form, by finite induction from the binary tensor product. -/
theorem exists_hilbertCore [Finite ι] :
    ∃ h : InnerProductSpace.Core ℂ (⨂[ℂ] i, E i),
      ∀ x y : ∀ i, E i, h.inner (tprod ℂ x) (tprod ℂ y) = ∏ᶠ i, inner ℂ (x i) (y i) := by
  classical
  induction ι using Finite.induction_empty_option with
  | of_equiv e ih =>
    obtain ⟨c, hc⟩ := ih (fun i => E (e i))
    let : InnerProductSpace.Core ℂ (⨂[ℂ] i, E (e i)) := c
    let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ⨂[ℂ] i, E (e i))
    let := InnerProductSpace.ofCore
      (inferInstance : PreInnerProductSpace.Core ℂ (⨂[ℂ] i, E (e i)))
    refine ⟨coreOfEquiv (W := ⨂[ℂ] i, E (e i)) (reindex ℂ E e.symm), ?_⟩
    intro x y
    rw [coreOfEquiv_inner, reindex_tprod, reindex_tprod]
    change c.inner (tprod ℂ (fun i => x (e i))) (tprod ℂ (fun i => y (e i))) = _
    simpa only [hc] using finprod_comp_equiv e (f := fun i => inner ℂ (x i) (y i))
  | h_empty =>
    refine ⟨coreOfEquiv (isEmptyEquiv PEmpty (R := ℂ) (s := E)), ?_⟩
    intro x y
    simp [coreOfEquiv_inner, finprod_eq_prod_of_fintype]
  | h_option ih =>
    obtain ⟨c, hc⟩ := ih (fun i => E (some i))
    let : InnerProductSpace.Core ℂ (⨂[ℂ] i, E (some i)) := c
    let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ⨂[ℂ] i, E (some i))
    let := InnerProductSpace.ofCore
      (inferInstance : PreInnerProductSpace.Core ℂ (⨂[ℂ] i, E (some i)))
    refine ⟨coreOfEquiv (optionEquiv ℂ E), ?_⟩
    intro x y
    rw [coreOfEquiv_inner, optionEquiv_tprod, optionEquiv_tprod, TensorProduct.inner_tmul]
    change c.inner (tprod ℂ (fun i => x (some i))) (tprod ℂ (fun i => y (some i))) *
      inner ℂ (x none) (y none) = _
    rw [hc, finprod_option (Set.toFinite _), mul_comm]

/-- The canonical positive Hermitian core on the actual finite tensor product. -/
@[instance_reducible]
scoped instance hilbertCore [Finite ι] : InnerProductSpace.Core ℂ (⨂[ℂ] i, E i) :=
  (exists_hilbertCore E).choose

/-- Its defining formula is the usual Hilbert tensor product formula. -/
theorem hilbertCore_inner_tprod [Finite ι] (x y : ∀ i, E i) :
    (hilbertCore E).inner (tprod ℂ x) (tprod ℂ y) = ∏ᶠ i, inner ℂ (x i) (y i) :=
  (exists_hilbertCore E).choose_spec x y

end BostConjecture.Tensor

end TensorInnerProduct

section FiniteTensorMetric

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

end HermitianMetric
end BostConjecture.Arithmetic

end FiniteTensorMetric

section BinaryTensorMetric

open NumberField PiTensorProduct
open scoped TensorProduct

namespace BostConjecture.Arithmetic

universe u

/-- The two factors, indexed for the existing finite tensor construction. -/
abbrev binaryTensorFamily (M N : Type u) : Unit ⊕ Unit → Type u
  | .inl _ => M
  | .inr _ => N

instance {M N : Type u} [AddCommGroup M] [AddCommGroup N] (i : Unit ⊕ Unit) :
    AddCommGroup (binaryTensorFamily M N i) :=
  Sum.casesOn i (fun _ => inferInstance) (fun _ => inferInstance)

instance {R : Type*} [CommRing R] {M N : Type u}
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] (i : Unit ⊕ Unit) :
    Module R (binaryTensorFamily M N i) :=
  Sum.casesOn i (fun _ => inferInstance) (fun _ => inferInstance)

variable (R : Type*) [CommRing R] (M N : Type u)
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

/-- The binary tensor as the two-factor finite tensor product. -/
def binaryTensorEquiv :
    M ⊗[R] N ≃ₗ[R] (⨂[R] i, binaryTensorFamily M N i) :=
  (TensorProduct.congr (subsingletonEquiv (R := R) (s := fun _ : Unit => M) ()).symm
    (subsingletonEquiv (R := R) (s := fun _ : Unit => N) ()).symm).trans
      (tmulEquivDep R (binaryTensorFamily M N))

variable {R M N}
@[simp]
lemma binaryTensorEquiv_tmul (x : M) (y : N) :
    binaryTensorEquiv R M N (x ⊗ₜ[R] y) =
      tprod R (fun i => Sum.casesOn i (fun _ => x) (fun _ => y)) := by
  simp [binaryTensorEquiv, subsingletonEquiv_symm_apply', tmulEquivDep_apply]

variable {K : Type*} [Field K] [NumberField K] [Module (𝓞 K) M] [Module (𝓞 K) N]

namespace HermitianMetric

/-- Binary Hilbert tensor metric, using the established finite-family metric. -/
def tensor (h : HermitianMetric K M) (g : HermitianMetric K N) :
    HermitianMetric K (M ⊗[𝓞 K] N) :=
  (piTensor (fun i : Unit ⊕ Unit => Sum.casesOn i (fun _ => h) (fun _ => g))).pullback
    (binaryTensorEquiv (𝓞 K) M N).toLinearMap (binaryTensorEquiv (𝓞 K) M N).injective

/-- Tensor product of Hermitian metrics on modules over `𝓞 K`.
Available with `open scoped HermitianMetric`, using the explicit ring notation `𝓞 K`. -/
scoped notation:100 h:100 " ⊗[" "𝓞 " K "] " g:101 => tensor (K := K) h g

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

end HermitianMetric
end BostConjecture.Arithmetic

end BinaryTensorMetric
