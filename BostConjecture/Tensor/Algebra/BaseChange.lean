/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Scalar extension on finite tensor products

The canonical map sends a pure tensor to the tensor of its scalar-extended
factors. For finite families its scalar-linear extension is an isomorphism,
natural in the modules. No flatness or freeness assumption is needed.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Tensor

open PiTensorProduct
open scoped TensorProduct

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
variable {ι : Type*} (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/-- Canonical scalar extension of a tensor, with scalars restricted to the source ring. -/
def scalarExtension : (⨂[R] i, M i) →ₗ[R] (⨂[S] i, S ⊗[R] M i) :=
  PiTensorProduct.lift <| ((tprod S).restrictScalars R).compLinearMap
    (fun i => TensorProduct.mk R S (M i) 1)

@[simp]
theorem scalarExtension_tprod (v : ∀ i, M i) :
    scalarExtension R S M (tprod R v) = tprod S (fun i => 1 ⊗ₜ[R] v i) := by
  simp [scalarExtension]

/-- The scalar-linear extension of `scalarExtension`. -/
def baseChangeMap : S ⊗[R] (⨂[R] i, M i) →ₗ[S] (⨂[S] i, S ⊗[R] M i) :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun := fun s => s • scalarExtension R S M
      map_add' := by intros; simp [add_smul]
      map_smul' := by intros; simp [smul_smul] }

@[simp]
theorem baseChangeMap_tmul (s : S) (z : ⨂[R] i, M i) :
    baseChangeMap R S M (s ⊗ₜ[R] z) = s • scalarExtension R S M z := rfl

/-- Separating the final factor of an option-indexed tensor product. -/
def optionEquiv (N : Option ι → Type*) [∀ i, AddCommGroup (N i)]
    [∀ i, Module R (N i)] :
    (⨂[R] i, N i) ≃ₗ[R] (⨂[R] i, N (some i)) ⊗[R] N none :=
  (reindex R N (Equiv.optionEquivSumPUnit.{0, _} ι)).trans
    ((tmulEquivDep R (fun i => N ((Equiv.optionEquivSumPUnit.{0, _} ι).symm i))).symm.trans
      (TensorProduct.congr (LinearEquiv.refl R _) (subsingletonEquiv PUnit.unit)))

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem optionEquiv_tprod (N : Option ι → Type*) [∀ i, AddCommGroup (N i)]
    [∀ i, Module R (N i)] (v : ∀ i, N i) :
    optionEquiv R N (tprod R v) = tprod R (fun i => v (some i)) ⊗ₜ[R] v none := by
  dsimp [optionEquiv]
  rw [reindex_tprod]
  rw [dsimp% tmulEquivDep_symm_apply R
    (fun i => N ((Equiv.optionEquivSumPUnit.{0, _} ι).symm i))
    (fun i => v ((Equiv.optionEquivSumPUnit.{0, _} ι).symm i))]
  simp

private theorem exists_baseChangeEquiv [Finite ι] :
    ∃ e : S ⊗[R] (⨂[R] i, M i) ≃ₗ[S] (⨂[S] i, S ⊗[R] M i),
      ∀ v : ∀ i, M i, e (1 ⊗ₜ[R] tprod R v) =
        tprod S (fun i => 1 ⊗ₜ[R] v i) := by
  classical
  induction ι using Finite.induction_empty_option with
  | of_equiv e ih =>
    obtain ⟨f, hf⟩ := ih (fun i => M (e i))
    refine ⟨((reindex R M e.symm).baseChange R S).trans
      (f.trans (reindex S (fun i => S ⊗[R] M i) e.symm).symm), ?_⟩
    intro v
    apply (reindex S (fun i => S ⊗[R] M i) e.symm).injective
    simp [hf]
  | h_empty =>
    refine ⟨((isEmptyEquiv PEmpty (R := R) (s := M)).baseChange R S).trans
      ((TensorProduct.AlgebraTensorModule.rid R S S).trans
        (isEmptyEquiv PEmpty (R := S) (s := fun i => S ⊗[R] M i)).symm), ?_⟩
    intro v
    apply (isEmptyEquiv PEmpty (R := S) (s := fun i => S ⊗[R] M i)).injective
    simp
  | h_option ih =>
    obtain ⟨f, hf⟩ := ih (fun i => M (some i))
    refine ⟨((optionEquiv R M).baseChange R S).trans
      ((TensorProduct.AlgebraTensorModule.distribBaseChange R S _ _).trans
        ((TensorProduct.congr f (LinearEquiv.refl S _)).trans
          (optionEquiv S (fun i => S ⊗[R] M i)).symm)), ?_⟩
    intro v
    apply (optionEquiv S (fun i => S ⊗[R] M i)).injective
    simp [hf]

/-- Tensor products commute with every scalar extension; no flatness or freeness is needed. -/
theorem baseChangeMap_bijective [Finite ι] : Function.Bijective (baseChangeMap R S M) := by
  obtain ⟨e, he⟩ := exists_baseChangeEquiv R S M
  have h : baseChangeMap R S M = e.toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro s z
    induction z using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      rw [TensorProduct.tmul_smul, TensorProduct.tmul_eq_smul_one_tmul]
      simp [he]
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  rw [h]
  exact e.bijective

/-- The canonical base-change isomorphism for a finite family of modules. -/
def baseChangeEquiv [Finite ι] :
    S ⊗[R] (⨂[R] i, M i) ≃ₗ[S] (⨂[S] i, S ⊗[R] M i) :=
  LinearEquiv.ofBijective (baseChangeMap R S M) (baseChangeMap_bijective R S M)

@[simp]
theorem baseChangeEquiv_tmul [Finite ι] (s : S) (v : ∀ i, M i) :
    baseChangeEquiv R S M (s ⊗ₜ[R] tprod R v) =
      s • tprod S (fun i => 1 ⊗ₜ[R] v i) := by
  simp [baseChangeEquiv]

variable {M} {N : ι → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]

/-- The canonical tensor map commutes with applying linear maps to its factors. -/
theorem scalarExtension_map (f : ∀ i, M i →ₗ[R] N i) (z : ⨂[R] i, M i) :
    scalarExtension R S N (PiTensorProduct.map f z) =
      PiTensorProduct.map (fun i => (f i).baseChange S) (scalarExtension R S M z) := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    simp only [map_smul, LinearMap.map_smul_of_tower, scalarExtension_tprod,
      map_tprod, LinearMap.baseChange_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Naturality of tensor base change, as an equality of scalar-linear maps. -/
theorem baseChangeEquiv_natural [Finite ι] (f : ∀ i, M i →ₗ[R] N i) :
    (baseChangeEquiv R S N).toLinearMap ∘ₗ (PiTensorProduct.map f).baseChange S =
      PiTensorProduct.map (fun i => (f i).baseChange S) ∘ₗ
        (baseChangeEquiv R S M).toLinearMap := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro s z
  change baseChangeMap R S N ((PiTensorProduct.map f).baseChange S (s ⊗ₜ[R] z)) =
    PiTensorProduct.map (fun i => (f i).baseChange S) (baseChangeMap R S M (s ⊗ₜ[R] z))
  simp [scalarExtension_map]

/-- Compatibility with a tower of coefficient extensions. -/
theorem scalarExtension_trans {T : Type*} [CommRing T] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] (z : ⨂[R] i, M i) :
    PiTensorProduct.map (fun i =>
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T (M i)).toLinearMap)
      (scalarExtension S T (fun i => S ⊗[R] M i) (scalarExtension R S M z)) =
        scalarExtension R T M z := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    simp only [map_smul, LinearMap.map_smul_of_tower, scalarExtension_tprod, map_tprod,
      LinearEquiv.coe_coe, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

end BostConjecture.Tensor
