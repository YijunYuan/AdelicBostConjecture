/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Tensor.Metric.Basic
public import BostConjecture.Tensor.Algebra.Regroup

/-!
# Hilbert tensor regrouping

The algebraic interchange preserves the actual iterated Hilbert forms.
The proof extends the double pure-tensor formula by spanning.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Tensor

open PiTensorProduct
open scoped TensorProduct

variable {ι κ : Type*} [Finite ι] [Finite κ] {P : ι → κ → Type*}
  [∀ i j, AddCommGroup (P i j)] [∀ i j, Module ℂ (P i j)]

/-- Regrouping preserves the iterated canonical Hilbert form, for arbitrary tensors. -/
theorem regroupEquiv_inner (c : ∀ i j, InnerProductSpace.Core ℂ (P i j))
    (x y : ⨂[ℂ] i, ⨂[ℂ] j, P i j) :
    (tensorCore (fun j => tensorCore (fun i => c i j))).inner
      (regroupEquiv ℂ P x) (regroupEquiv ℂ P y) =
      (tensorCore (fun i => tensorCore (c i))).inner x y := by
  apply inner_ext_of_span (fun v : ∀ i j, P i j => tprod ℂ (fun i => tprod ℂ (v i)))
    (PiTensorProduct.submodule_span_eq_top (fun i => span_tprod_eq_top (R := ℂ) (s := P i)))
    _ _ (regroupEquiv ℂ P).toLinearMap LinearMap.id _ x y
  intro v w
  simp only [LinearEquiv.coe_coe, regroupEquiv_tprod, LinearMap.id_apply,
    tensorCore_inner_tprod]
  let : Fintype ι := Fintype.ofFinite ι
  let : Fintype κ := Fintype.ofFinite κ
  simpa only [finprod_eq_prod_of_fintype] using Finset.prod_comm

end BostConjecture.Tensor
