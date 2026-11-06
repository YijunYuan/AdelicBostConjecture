/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Tensor.Dual.Evaluation
public import BostConjecture.Tensor.Algebra.BaseChange
public import BostConjecture.Arithmetic.Dual.Fiber

/-!
# Canonical tensor evaluation commutes with scalar extension

Extending scalars in the tensor evaluation map agrees with evaluating
the scalar-extended tensors and duals. Equality is checked on pure tensors.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Tensor

open Module PiTensorProduct
open scoped TensorProduct

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
  {ι : Type*} [Finite ι] (M : ι → Type*)
  [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  [∀ i, Module.Finite R (M i)] [∀ i, Module.Projective R (M i)]

/-- Tensor evaluation on extended original tensors is the extension of evaluation. -/
theorem evaluation_scalarExtension (u : ⨂[R] i, Dual R (M i)) (x : ⨂[R] i, M i) :
    dualDistribEquivOfProjective S (fun i => S ⊗[R] M i)
      (PiTensorProduct.map (fun i => (Arithmetic.dualBaseChangeEquiv R S (M i)).toLinearMap)
        (scalarExtension R S (fun i => Dual R (M i)) u))
      (scalarExtension R S M x) =
      algebraMap R S (dualDistribEquivOfProjective R M u x) := by
  let := Fintype.ofFinite ι
  induction u using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    induction x using PiTensorProduct.induction_on with
    | smul_tprod q v =>
      simp only [map_smul, scalarExtension_tprod]
      rw [← algebraMap_smul S r, ← algebraMap_smul S q]
      simp only [map_smul, map_tprod, LinearMap.smul_apply,
        dualDistribEquivOfProjective_tprod_tprod, finprod_eq_prod_of_fintype,
        LinearEquiv.coe_coe, Arithmetic.dualBaseChangeEquiv_tmul, one_mul,
        smul_eq_mul, map_mul, map_prod]
    | add x y hx hy => simp only [map_add, hx, hy]
  | add u v hu hv => simp only [map_add, LinearMap.add_apply, hu, hv]

/-- The tensor-dual evaluation square commutes on arbitrary extended tensors. -/
theorem evaluation_baseChange
    (u : S ⊗[R] (⨂[R] i, Dual R (M i))) (x : S ⊗[R] (⨂[R] i, M i)) :
    dualDistribEquivOfProjective S (fun i => S ⊗[R] M i)
      (PiTensorProduct.map (fun i => (Arithmetic.dualBaseChangeEquiv R S (M i)).toLinearMap)
        (baseChangeEquiv R S (fun i => Dual R (M i)) u))
      (baseChangeEquiv R S M x) =
      Arithmetic.dualBaseChangeEquiv R S (⨂[R] i, M i)
        ((dualDistribEquivOfProjective R M).toLinearMap.baseChange S u) x := by
  induction u using TensorProduct.inductionOn with
  | tmul a u =>
    induction x using TensorProduct.inductionOn with
    | tmul b x =>
      change dualDistribEquivOfProjective S (fun i => S ⊗[R] M i)
        (PiTensorProduct.map
          (fun i => (Arithmetic.dualBaseChangeEquiv R S (M i)).toLinearMap)
          (a • scalarExtension R S (fun i => Dual R (M i)) u))
        (b • scalarExtension R S M x) = _
      simp only [map_smul, LinearMap.smul_apply, LinearMap.baseChange_tmul,
        Arithmetic.dualBaseChangeEquiv_tmul, smul_eq_mul, evaluation_scalarExtension,
        LinearEquiv.coe_coe]
      ring
    | add x y hx hy => simp only [map_add, hx, hy]
  | add u v hu hv => simp only [map_add, LinearMap.add_apply, hu, hv]

variable {V W : Type*} [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W] [Module.Finite R W] [Module.Projective R W]

/-- Scalar extension preserves the tensor-power pairing of a linear map. -/
theorem tensorPowerPairing_scalarExtension (f : V →ₗ[R] W)
    (z : ⨂[R] (_ : ι), V) (u : ⨂[R] (_ : ι), Dual R W) :
    tensorPowerPairing (f.baseChange S) (scalarExtension R S (fun _ : ι => V) z)
      (PiTensorProduct.map (fun _ : ι => (Arithmetic.dualBaseChangeEquiv R S W).toLinearMap)
        (scalarExtension R S (fun _ : ι => Dual R W) u)) =
      algebraMap R S (tensorPowerPairing f z u) := by
  simp only [tensorPowerPairing_apply, ← scalarExtension_map,
    evaluation_scalarExtension]

/-- The full tensor-power pairing diagram commutes for arbitrary scalar-extended inputs. -/
theorem tensorPowerPairing_baseChange (f : V →ₗ[R] W)
    (z : S ⊗[R] (⨂[R] (_ : ι), V)) (u : S ⊗[R] (⨂[R] (_ : ι), Dual R W)) :
    tensorPowerPairing (f.baseChange S) (baseChangeEquiv R S (fun _ : ι => V) z)
      (PiTensorProduct.map (fun _ : ι => (Arithmetic.dualBaseChangeEquiv R S W).toLinearMap)
        (baseChangeEquiv R S (fun _ : ι => Dual R W) u)) =
      Arithmetic.dualBaseChangeEquiv R S (⨂[R] (_ : ι), Dual R W)
        ((tensorPowerPairing f).baseChange S z) u := by
  induction z using TensorProduct.inductionOn with
  | tmul a z =>
    induction u using TensorProduct.inductionOn with
    | tmul b u =>
      change tensorPowerPairing (f.baseChange S)
        (a • scalarExtension R S (fun _ : ι => V) z)
        (PiTensorProduct.map
          (fun _ : ι => (Arithmetic.dualBaseChangeEquiv R S W).toLinearMap)
          (b • scalarExtension R S (fun _ : ι => Dual R W) u)) = _
      simp only [map_smul, LinearMap.smul_apply, LinearMap.baseChange_tmul,
        Arithmetic.dualBaseChangeEquiv_tmul, smul_eq_mul,
        tensorPowerPairing_scalarExtension]
      ring
    | add u v hu hv => simp only [map_add, hu, hv]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

end BostConjecture.Tensor
