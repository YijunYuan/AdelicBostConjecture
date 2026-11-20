/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import AdelicBostConjecture.ExternalCode.MathlibPRs.PR44845.LinearAlgebra.PiTensorProduct.Projective
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

/-!
# Canonical evaluation on tensor powers

The finite-projective duality equivalence supplies the canonical evaluation
pairing. Its permutation identity is proved on tensors and then applied to
the tensor power of a linear map. No basis or freeness assumption is used.
-/

@[expose] public section

noncomputable section

namespace AdelicBostConjecture.Tensor

open Module PiTensorProduct
open scoped TensorProduct

variable {R ι : Type*} [CommRing R] [Finite ι]
variable {V W : Type*} [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W] [Module.Finite R W] [Module.Projective R W]

/-- Canonical finite-projective evaluation is invariant under simultaneous
permutation of the tensor positions. -/
theorem evaluation_reindex (σ : Equiv.Perm ι)
    (u : ⨂[R] (_ : ι), Dual R W) (z : ⨂[R] (_ : ι), W) :
    dualDistribEquivOfProjective R (fun _ : ι => W)
      (reindex R (fun _ : ι => Dual R W) σ u)
      (reindex R (fun _ : ι => W) σ z) =
    dualDistribEquivOfProjective R (fun _ : ι => W) u z := by
  let := Fintype.ofFinite ι
  induction u using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    induction z using PiTensorProduct.induction_on with
    | smul_tprod s x =>
      simp only [map_smul, reindex_tprod, LinearMap.smul_apply,
        dualDistribEquivOfProjective_tprod_tprod, finprod_eq_prod_of_fintype]
      rw [σ.symm.prod_comp (fun q => f q (x q))]
    | add x y hx hy => simp only [map_add, hx, hy]
  | add u v hu hv => simp only [map_add, LinearMap.add_apply, hu, hv]

/-- Evaluate the tensor power of a linear map against the tensor power of the
dual of its finite projective codomain. -/
def tensorPowerPairing (i : V →ₗ[R] W) :
    (⨂[R] (_ : ι), V) →ₗ[R] Dual R (⨂[R] (_ : ι), Dual R W) :=
  (dualDistribEquivOfProjective R (fun _ : ι => W)).toLinearMap.flip ∘ₗ
    PiTensorProduct.map (fun _ : ι => i)

@[simp]
theorem tensorPowerPairing_apply (i : V →ₗ[R] W)
    (z : ⨂[R] (_ : ι), V) (u : ⨂[R] (_ : ι), Dual R W) :
    tensorPowerPairing i z u = dualDistribEquivOfProjective R (fun _ : ι => W) u
      (PiTensorProduct.map (fun _ : ι => i) z) := rfl

@[simp]
theorem tensorPowerPairing_tprod_tprod [Fintype ι] (i : V →ₗ[R] W)
    (v : ι → V) (f : ι → Dual R W) :
    tensorPowerPairing i (tprod R v) (tprod R f) = ∏ q, f q (i (v q)) := by
  simp [finprod_eq_prod_of_fintype]

/-- The ambient pairing intertwines simultaneous position permutations. -/
theorem tensorPowerPairing_reindex (i : V →ₗ[R] W) (σ : Equiv.Perm ι)
    (z : ⨂[R] (_ : ι), V) (u : ⨂[R] (_ : ι), Dual R W) :
    tensorPowerPairing i (reindex R (fun _ : ι => V) σ z)
      (reindex R (fun _ : ι => Dual R W) σ u) = tensorPowerPairing i z u := by
  simp only [tensorPowerPairing_apply]
  simpa only [map_reindex (fun _ : ι => i) σ z] using evaluation_reindex σ u _

/-- Equivariance into the contragredient representation, with the inverse
permutation on the dual tensor argument. -/
theorem tensorPowerPairing_reindex_left (i : V →ₗ[R] W) (σ : Equiv.Perm ι)
    (z : ⨂[R] (_ : ι), V) (u : ⨂[R] (_ : ι), Dual R W) :
    tensorPowerPairing i (reindex R (fun _ : ι => V) σ z) u =
      tensorPowerPairing i z (reindex R (fun _ : ι => Dual R W) σ.symm u) := by
  have h := tensorPowerPairing_reindex i σ z
    ((reindex R (fun _ : ι => Dual R W) σ).symm u)
  rwa [LinearEquiv.apply_symm_apply, reindex_symm] at h

end AdelicBostConjecture.Tensor
