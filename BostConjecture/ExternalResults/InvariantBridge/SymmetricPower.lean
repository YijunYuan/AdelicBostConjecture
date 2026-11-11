/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Yijun Yuan
-/
module

public import BostConjecture.ExternalCode.TauCeti.LinearAlgebra.SymmetricPower.Lift
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.GroupTheory.Perm.Fin

/-!
# Symmetric powers with universe-lifted finite indices

The scalar ring and the index of Mathlib `SymmetricPower` share a universe.
Using `ULift (Fin n)` preserves the actual symmetric quotient while allowing
arbitrary coefficient universes. The finite-coordinate maps below recover the
usual degree conventions without restricting the scalar ring.

Adapted from TauCeti revision `3c3a32baea963db05c302adeb307b22baae4de78`,
`TauCeti/LinearAlgebra/SymmetricPower/{Lift,Algebra}.lean`, Apache-2.0, through
this project’s existing selective ports. The adaptation changes only finite
index transport and its proofs; it retains the upstream namespace and quotient.
The intended consumer is `BostConjecture.Geometry.Polynomial.Polarization`.
-/

public section

open scoped TensorProduct

namespace TauCeti.SymmetricPower

universe u v w

variable (R : Type u) (M : Type v) [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The existing symmetric quotient indexed in the scalar ring's universe. -/
abbrev FinitePower (n : ℕ) := _root_.SymmetricPower R (ULift.{u} (Fin n)) M

/-- Pure symmetric tensors expressed in ordinary finite coordinates. -/
noncomputable def finiteTprod (n : ℕ) :
    MultilinearMap R (fun _ : Fin n ↦ M) (FinitePower R M n) :=
  (_root_.SymmetricPower.tprod R).domDomCongr Equiv.ulift

/-- Permuting finite coordinates does not change their symmetric tensor. -/
theorem finiteTprod_perm (n : ℕ) (m : Fin n → M) (e : Equiv.Perm (Fin n)) :
    finiteTprod R M n (m ∘ e) = finiteTprod R M n m := by
  have h := _root_.SymmetricPower.tprod_equiv
    (R := R) ((Equiv.ulift : ULift.{u} (Fin n) ≃ Fin n).symm.permCongr e)
    (fun i : ULift.{u} (Fin n) ↦ m i.down)
  simpa [finiteTprod, MultilinearMap.domDomCongr_apply, Function.comp_def] using h

variable {R M}

/-- A linear map on the lifted symmetric power is determined by finite pure tensors. -/
theorem finite_ext {N : Type w} [AddCommMonoid N] [Module R N] {n : ℕ}
    {f g : FinitePower R M n →ₗ[R] N}
    (h : ∀ m : Fin n → M, f (finiteTprod R M n m) = g (finiteTprod R M n m)) : f = g := by
  apply _root_.SymmetricPower.ext
  intro m
  simpa [finiteTprod, MultilinearMap.domDomCongr_apply] using h (fun i ↦ m ⟨i⟩)

/-- The universal property in ordinary finite coordinates, over any scalar universe. -/
noncomputable def finiteLift {N : Type w} [AddCommMonoid N] [Module R N] {n : ℕ}
    (f : MultilinearMap R (fun _ : Fin n ↦ M) N)
    (hf : ∀ e : Equiv.Perm (Fin n), f.domDomCongr e = f) :
    FinitePower R M n →ₗ[R] N :=
  _root_.SymmetricPower.lift (f.domDomCongr Equiv.ulift.symm) (by
    intro e
    ext m
    simpa [MultilinearMap.domDomCongr_apply, Function.comp_def, Equiv.ulift] using
      congrArg (fun f : MultilinearMap R (fun _ : Fin n ↦ M) N ↦ f (fun i ↦ m ⟨i⟩))
        (hf ((Equiv.ulift : ULift.{u} (Fin n) ≃ Fin n).permCongr e)))

/-- The finite-coordinate lift takes its prescribed values on pure tensors. -/
@[simp]
theorem finiteLift_tprod {N : Type w} [AddCommMonoid N] [Module R N] {n : ℕ}
    (f : MultilinearMap R (fun _ : Fin n ↦ M) N)
    (hf : ∀ e : Equiv.Perm (Fin n), f.domDomCongr e = f) (m : Fin n → M) :
    finiteLift f hf (finiteTprod R M n m) = f m := by
  simp [finiteLift, finiteTprod, MultilinearMap.domDomCongr_apply]

private theorem finiteTprod_cons_invariant (n : ℕ) (m : M) (e : Equiv.Perm (Fin n)) :
    ((finiteTprod R M (n + 1)).curryLeft m).domDomCongr e =
      (finiteTprod R M (n + 1)).curryLeft m := by
  ext v
  simp only [MultilinearMap.domDomCongr_apply, MultilinearMap.curryLeft_apply]
  rw [← finiteTprod_perm R M (n + 1) (Fin.cons m v)
    (Equiv.Perm.decomposeFin.symm (0, e))]
  congr 1
  funext i
  cases i using Fin.cases with
  | zero => simp
  | succ i => simp

variable (R M)

/-- Multiplication by one generator in the lifted finite symmetric powers. -/
noncomputable def finiteConsMul (n : ℕ) :
    M →ₗ[R] FinitePower R M n →ₗ[R] FinitePower R M (n + 1) where
  toFun m := finiteLift ((finiteTprod R M (n + 1)).curryLeft m)
    (finiteTprod_cons_invariant n m)
  map_add' m m' := finite_ext fun v ↦ by simp
  map_smul' c m := finite_ext fun v ↦ by simp

/-- Multiplication by a generator prepends it to a pure symmetric tensor. -/
@[simp]
theorem finiteConsMul_tprod (n : ℕ) (m : M) (v : Fin n → M) :
    finiteConsMul R M n m (finiteTprod R M n v) =
      finiteTprod R M (n + 1) (Fin.cons m v) := by
  simp [finiteConsMul, MultilinearMap.curryLeft_apply]

/-- Multiplications by two generators commute. -/
theorem finiteConsMul_comm (n : ℕ) (m m' : M) (x : FinitePower R M n) :
    finiteConsMul R M (n + 1) m (finiteConsMul R M n m' x) =
      finiteConsMul R M (n + 1) m' (finiteConsMul R M n m x) := by
  suffices h : finiteConsMul R M (n + 1) m ∘ₗ finiteConsMul R M n m' =
      finiteConsMul R M (n + 1) m' ∘ₗ finiteConsMul R M n m from LinearMap.congr_fun h x
  apply finite_ext
  intro v
  simp only [LinearMap.comp_apply, finiteConsMul_tprod]
  rw [← finiteTprod_perm R M (n + 2) (Fin.cons m (Fin.cons m' v)) (Equiv.swap 0 1)]
  exact congrArg (finiteTprod R M (n + 2))
    (Matrix.cons_cons_comp_swap_zero_one m m' v)

end TauCeti.SymmetricPower
