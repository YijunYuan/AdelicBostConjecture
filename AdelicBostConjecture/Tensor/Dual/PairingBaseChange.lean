/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import AdelicBostConjecture.Tensor.Dual.RegroupBaseChange

/-!
# Scalar extension of a pairing into a tensor product

A bilinear pairing into a tensor product induces a pairing after scalar
extension. The comparison formula connects integral determinant pairings
to their complex-fiber realizations.
-/

@[expose] public section

noncomputable section

namespace AdelicBostConjecture.Tensor

open Module PiTensorProduct
open scoped TensorProduct

variable {R : Type*} [CommRing R] {κ V W X : Type*} [Finite κ]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  [AddCommGroup X] [Module R X]
  [Module.Finite R W] [Module.Projective R W]
  [Module.Finite R X] [Module.Projective R X]

/-- Transporting the codomain and its dual by inverse equivalences preserves pairing. -/
theorem tensorPowerPairing_equiv (e : W ≃ₗ[R] X) (f : V →ₗ[R] W)
    (z : ⨂[R] (_ : κ), V) (u : ⨂[R] (_ : κ), Dual R W) :
    tensorPowerPairing (e.toLinearMap ∘ₗ f) z
      (map (fun _ : κ => e.symm.dualMap.toLinearMap) u) =
      tensorPowerPairing f z u := by
  let := Fintype.ofFinite κ
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    induction u using PiTensorProduct.induction_on with
    | smul_tprod s g => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
  {ι : Type*} [Finite ι] (E : ι → Type*)
  [∀ i, AddCommGroup (E i)] [∀ i, Module R (E i)]
  [∀ i, Module.Finite R (E i)] [∀ i, Module.Projective R (E i)]
  {V : Type*} [AddCommGroup V] [Module R V]

/-- The pairing into a tensor product uses the canonical tensor-dual identification
on scalar extension of its ambient dual. -/
theorem tensorPowerPairing_tensorBaseChange (f : V →ₗ[R] (⨂[R] i, E i))
    (z : S ⊗[R] (⨂[R] (_ : κ), V))
    (u : S ⊗[R] (⨂[R] (_ : κ), Dual R (⨂[R] i, E i))) :
    tensorPowerPairing (W := ⨂[S] i, S ⊗[R] E i)
      ((baseChangeEquiv R S E).toLinearMap ∘ₗ f.baseChange S)
      (baseChangeEquiv R S (fun _ : κ => V) z)
      (map (fun _ : κ => (tensorDualBaseChangeEquiv R S E).toLinearMap)
        (baseChangeEquiv R S (fun _ : κ => Dual R (⨂[R] i, E i)) u)) =
    Arithmetic.dualBaseChangeEquiv R S (⨂[R] (_ : κ), Dual R (⨂[R] i, E i))
      ((tensorPowerPairing f).baseChange S z) u := by
  have h := tensorPowerPairing_equiv (X := ⨂[S] i, S ⊗[R] E i)
    (baseChangeEquiv R S E) (f.baseChange S)
    (baseChangeEquiv R S (fun _ : κ => V) z)
    (map (fun _ : κ => (Arithmetic.dualBaseChangeEquiv R S (⨂[R] i, E i)).toLinearMap)
      (baseChangeEquiv R S (fun _ : κ => Dual R (⨂[R] i, E i)) u))
  rw [tensorPowerPairing_baseChange] at h
  have he : (tensorDualBaseChangeEquiv R S E).toLinearMap =
      (baseChangeEquiv R S E).symm.dualMap.toLinearMap ∘ₗ
        (Arithmetic.dualBaseChangeEquiv R S (⨂[R] i, E i)).toLinearMap := rfl
  rwa [he, PiTensorProduct.map_comp, LinearMap.comp_apply]

end AdelicBostConjecture.Tensor
