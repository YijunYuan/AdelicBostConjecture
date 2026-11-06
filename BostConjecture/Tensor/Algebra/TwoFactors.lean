/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Canonical decomposition of a two-factor dependent tensor family

The tensor product indexed by a disjoint union of two singleton types
is identified with the binary tensor product. This equivalence intertwines
factor maps and the prescribed Hilbert forms.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Tensor

open PiTensorProduct
open scoped TensorProduct

variable (R : Type*) [CommRing R] (E : Unit ⊕ Unit → Type*)
  [∀ i, AddCommGroup (E i)] [∀ i, Module R (E i)]

/-- The sum-index tensor equivalence followed by singleton evaluation. -/
def twoFactorEquiv : (⨂[R] i, E i) ≃ₗ[R] E (.inl ()) ⊗[R] E (.inr ()) :=
  (tmulEquivDep R E).symm.trans
    (TensorProduct.congr (subsingletonEquiv ()) (subsingletonEquiv ()))

@[simp]
theorem twoFactorEquiv_tprod (x : ∀ i, E i) :
    twoFactorEquiv R E (tprod R x) = x (.inl ()) ⊗ₜ[R] x (.inr ()) := by
  simp [twoFactorEquiv]

variable {R E} {D : Unit ⊕ Unit → Type*}
  [∀ i, AddCommGroup (D i)] [∀ i, Module R (D i)]

/-- Naturality holds for the actual dependent tensor maps. -/
theorem twoFactorEquiv_map (f : ∀ i, E i →ₗ[R] D i) :
    (twoFactorEquiv R D).toLinearMap ∘ₗ PiTensorProduct.map f =
      TensorProduct.map (f (.inl ())) (f (.inr ())) ∘ₗ
        (twoFactorEquiv R E).toLinearMap := by
  ext x
  simp

end BostConjecture.Tensor
