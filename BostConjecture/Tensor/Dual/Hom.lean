/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Tensor.Algebra.Regroup
public import BostConjecture.Tensor.Dual.Evaluation
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.PiTensorProduct.Dual

/-!
# Canonical Hom duality and tensor-power evaluation

Only finite projectivity is used. The maps are the canonical reflexive dual,
tensor duality, and finite tensor distribution equivalences.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Tensor

open Module PiTensorProduct
open scoped TensorProduct

variable (R V W : Type*) [CommRing R] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W] [Module.Finite R V] [Module.Projective R V]
  [Module.Finite R W] [Module.Projective R W]

/-- The canonical finite-projective isomorphism `V ⊗ W* ≃ Hom(V,W)*`. -/
def homDualEquiv : V ⊗[R] Dual R W ≃ₗ[R] Dual R (V →ₗ[R] W) :=
  (TensorProduct.congr (Module.evalEquiv R V) (LinearEquiv.refl R (Dual R W))).trans
    ((TensorProduct.dualDistribEquiv R (Dual R V) W).trans
      (dualTensorHomEquiv R V W).symm.dualMap)

@[simp]
theorem homDualEquiv_tmul (v : V) (ℓ : Dual R W) (A : V →ₗ[R] W) :
    homDualEquiv R V W (v ⊗ₜ[R] ℓ) A = ℓ (A v) := by
  obtain ⟨z, rfl⟩ := (dualTensorHomEquiv R V W).surjective A
  induction z using TensorProduct.inductionOn with
  | tmul f w => simp [homDualEquiv, mul_comm]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

variable {ι : Type*} [Fintype ι]

/-- The Hom-dual tensor power in the existing source/dual-target grouping. -/
def homDualTensorEquiv :
    (⨂[R] (_ : ι), V) ⊗[R] (⨂[R] (_ : ι), Dual R W) ≃ₗ[R]
      (⨂[R] (_ : ι), Dual R (V →ₗ[R] W)) :=
  (tensorDistribEquiv R (fun _ : ι => V) (fun _ : ι => Dual R W)).trans
    (PiTensorProduct.congr fun _ => homDualEquiv R V W)

@[simp]
theorem homDualTensorEquiv_tprod (v : ι → V) (ℓ : ι → Dual R W) :
    homDualTensorEquiv R V W (tprod R v ⊗ₜ[R] tprod R ℓ) =
      tprod R (fun i => homDualEquiv R V W (v i ⊗ₜ[R] ℓ i)) := by
  simp [homDualTensorEquiv]

/-- Independent source and target maps act through the actual Hom pullback. -/
theorem homDualTensorEquiv_map (h : V →ₗ[R] V) (g : W →ₗ[R] W)
    (v : ⨂[R] (_ : ι), V) (ℓ : ⨂[R] (_ : ι), Dual R W) :
    homDualTensorEquiv R V W
      (PiTensorProduct.map (fun _ => h) v ⊗ₜ[R]
        PiTensorProduct.map (fun _ => g.dualMap) ℓ) =
      PiTensorProduct.map (fun _ => ((g.compRight R).comp (h.lcomp R W)).dualMap)
        (homDualTensorEquiv R V W (v ⊗ₜ[R] ℓ)) := by
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    induction ℓ using PiTensorProduct.induction_on with
    | smul_tprod s ℓ =>
      simp only [map_smul, TensorProduct.smul_tmul, TensorProduct.tmul_smul,
        map_tprod, homDualTensorEquiv_tprod]
      congr 2
      congr 1
      funext i
      apply LinearMap.ext
      intro A
      simp
    | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, hx, hy]
  | add x y hx hy => simp only [map_add, TensorProduct.add_tmul, hx, hy]

/-- Evaluation of the Hom-dual tensor is the already constructed pairing. -/
theorem homDualTensorEquiv_evaluation (A : V →ₗ[R] W)
    (v : ⨂[R] (_ : ι), V) (ℓ : ⨂[R] (_ : ι), Dual R W) :
    PiTensorProduct.dualDistrib (R := R) (M := fun _ : ι => V →ₗ[R] W)
      (homDualTensorEquiv R V W (v ⊗ₜ[R] ℓ)) (tprod R fun _ => A) =
        tensorPowerPairing A v ℓ := by
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    induction ℓ using PiTensorProduct.induction_on with
    | smul_tprod s ℓ =>
      simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul, map_smul,
        LinearMap.smul_apply, homDualTensorEquiv_tprod, tensorPowerPairing_tprod_tprod]
      simp [mul_left_comm]
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, LinearMap.add_apply, hx, hy]
  | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, LinearMap.add_apply, hx, hy]

end BostConjecture.Tensor
