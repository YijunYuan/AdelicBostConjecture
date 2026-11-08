/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Tensor.Dual.Metric
public import BostConjecture.Tensor.Metric.Basic
public import BostConjecture.ExternalCode.MathlibPRs.PR44845.LinearAlgebra.PiTensorProduct.Projective

/-!
# Canonical projective tensor duality preserves the Hilbert form

The projective tensor-duality equivalence preserves the Hermitian forms
determined by the factor metrics. The statement applies to algebraic
duals equipped with their canonical finite-dimensional Hilbert forms.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Tensor

open Module PiTensorProduct
open scoped TensorProduct

variable {ι : Type*} [Finite ι] (E : ι → Type*)
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
  [∀ i, FiniteDimensional ℂ (E i)]

local instance : NormedAddCommGroup (⨂[ℂ] i, E i) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ⨂[ℂ] i, E i)

local instance : SeminormedAddCommGroup (⨂[ℂ] i, E i) :=
  (inferInstance : NormedAddCommGroup (⨂[ℂ] i, E i)).toSeminormedAddCommGroup

local instance : InnerProductSpace ℂ (⨂[ℂ] i, E i) :=
  InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (⨂[ℂ] i, E i))

/-- The Riesz vector of a pure tensor functional is the pure tensor of its Riesz vectors. -/
theorem dualRieszEquiv_tprod (f : ∀ i, Dual ℂ (E i)) :
    dualRieszEquiv (⨂[ℂ] i, E i)
      (dualDistribEquivOfProjective ℂ E (PiTensorProduct.tprod ℂ f)) =
      PiTensorProduct.tprod ℂ (fun i => dualRieszEquiv (E i) (f i)) := by
  apply ext_inner_right ℂ
  intro x
  rw [dualRieszEquiv_inner]
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    simp only [map_smul, inner_smul_right, dualDistribEquivOfProjective_tprod_tprod]
    congr 1
    change _ = (hilbertCore E).inner _ _
    simp only [hilbertCore_inner_tprod, dualRieszEquiv_inner]
  | add x y hx hy => simp only [map_add, inner_add_right, hx, hy]

/-- The actual finite-projective tensor duality is an isometry for the dual Hilbert forms. -/
theorem dualDistribEquivOfProjective_inner (u v : ⨂[ℂ] i, Dual ℂ (E i)) :
    (dualCore (⨂[ℂ] i, E i)).inner
      (dualDistribEquivOfProjective ℂ E u) (dualDistribEquivOfProjective ℂ E v) =
      (tensorCore (fun i => dualCore (E i))).inner u v := by
  symm
  apply inner_ext_of_span (PiTensorProduct.tprod ℂ)
    (span_tprod_eq_top (R := ℂ) (s := fun i => Dual ℂ (E i)))
    (tensorCore (fun i => dualCore (E i))) (dualCore (⨂[ℂ] i, E i))
    LinearMap.id (dualDistribEquivOfProjective ℂ E).toLinearMap _ u v
  intro f g
  simp only [LinearMap.id_apply, LinearEquiv.coe_coe, dualCore_inner,
    dualRieszEquiv_tprod, tensorCore_inner_tprod]
  change _ = (hilbertCore E).inner _ _
  simp only [hilbertCore_inner_tprod]

/-- Evaluation of arbitrary tensors has the product bound for the prescribed forms. -/
theorem tensorDual_evaluation_le (u : ⨂[ℂ] i, Dual ℂ (E i)) (x : ⨂[ℂ] i, E i) :
    ‖dualDistribEquivOfProjective ℂ E u x‖ ≤
      Real.sqrt (((tensorCore (fun i => dualCore (E i))).inner u u).re) *
        Real.sqrt (((hilbertCore E).inner x x).re) := by
  have h := dualCore_evaluation_le (⨂[ℂ] i, E i)
    (dualDistribEquivOfProjective ℂ E u) x
  rwa [dualDistribEquivOfProjective_inner] at h

end BostConjecture.Tensor
