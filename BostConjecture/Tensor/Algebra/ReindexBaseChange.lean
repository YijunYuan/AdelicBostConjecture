/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Tensor.Algebra.BaseChange

/-!
# Scalar extension commutes with permutations of tensor positions

The scalar-extension equivalence intertwines permutations of tensor
positions. Its pure-tensor formula establishes compatibility with the
position actions used in determinant contractions.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Tensor

open PiTensorProduct
open scoped TensorProduct

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
  {ι M : Type*} [AddCommGroup M] [Module R M]

/-- Scalar extension commutes with every permutation of tensor positions. -/
theorem scalarExtension_reindex (σ : Equiv.Perm ι) (z : ⨂[R] (_ : ι), M) :
    scalarExtension R S (fun _ : ι => M) (reindex R (fun _ : ι => M) σ z) =
      reindex S (fun _ : ι => S ⊗[R] M) σ
        (scalarExtension R S (fun _ : ι => M) z) := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    simp only [map_smul, reindex_tprod, scalarExtension_tprod]
    rw [← algebraMap_smul S r, ← algebraMap_smul S r, map_smul, reindex_tprod]
  | add x y hx hy => simp only [map_add, hx, hy]

variable [Finite ι]

/-- Scalar extension on an arbitrary tensor, rather than only a pure tensor. -/
theorem baseChangeEquiv_tmul_eq_scalarExtension (s : S) (z : ⨂[R] (_ : ι), M) :
    baseChangeEquiv R S (fun _ : ι => M) (s ⊗ₜ[R] z) =
      s • scalarExtension R S (fun _ : ι => M) z := rfl

/-- Canonical base change intertwines position permutations on the entire
scalar extension. -/
theorem baseChangeEquiv_reindex (σ : Equiv.Perm ι)
    (z : S ⊗[R] (⨂[R] (_ : ι), M)) :
    baseChangeEquiv R S (fun _ : ι => M)
      ((reindex R (fun _ : ι => M) σ).toLinearMap.baseChange S z) =
      reindex S (fun _ : ι => S ⊗[R] M) σ
        (baseChangeEquiv R S (fun _ : ι => M) z) := by
  induction z using TensorProduct.inductionOn with
  | tmul s z =>
    simp only [LinearMap.baseChange_tmul, LinearEquiv.coe_coe,
      baseChangeEquiv_tmul_eq_scalarExtension, scalarExtension_reindex, map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

end BostConjecture.Tensor
