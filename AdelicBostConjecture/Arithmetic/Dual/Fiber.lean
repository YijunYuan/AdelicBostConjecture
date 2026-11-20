/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.LinearAlgebra.Contraction

/-!
# Scalar extension of the dual

The canonical dual base-change map is an equivalence for finite projective
modules. These general algebraic constructions supply the dual transports in
the adelic contraction proof.
-/

@[expose] public section

noncomputable section

open TensorProduct Module

namespace AdelicBostConjecture.Arithmetic

section BaseChange

variable (R S M : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M]

/-- The scalar-linear extension of Mathlib's canonical dual base-change map. -/
def dualBaseChangeMap : S ⊗[R] Dual R M →ₗ[S] Dual S (S ⊗[R] M) :=
  (Module.Dual.baseChange (V := M) S).liftBaseChange S

@[simp]
lemma dualBaseChangeMap_tmul (a b : S) (f : Dual R M) (x : M) :
    dualBaseChangeMap R S M (a ⊗ₜ[R] f) (b ⊗ₜ[R] x) =
      a * b * algebraMap R S (f x) := by
  simp [dualBaseChangeMap, Algebra.smul_def, mul_comm, mul_assoc]

variable [Module.Finite R M] [Module.Projective R M]

/-- Dual base change is bijective without an integral freeness hypothesis. -/
lemma dualBaseChangeMap_bijective : Function.Bijective (dualBaseChangeMap R S M) := by
  let e : S ⊗[R] Dual R M ≃ₗ[R] Dual S (S ⊗[R] M) :=
    (TensorProduct.comm R S (Dual R M)).trans
      ((dualTensorHomEquiv R M S).trans ((LinearMap.liftBaseChangeEquiv S).restrictScalars R))
  have he : (dualBaseChangeMap R S M).restrictScalars R = e.toLinearMap := by
    apply TensorProduct.ext'
    intro a f
    apply TensorProduct.AlgebraTensorModule.ext
    intro b x
    simp [e, dualBaseChangeMap_tmul, Algebra.smul_def, mul_comm, mul_left_comm, mul_assoc]
  change Function.Bijective ((dualBaseChangeMap R S M).restrictScalars R)
  rw [he]
  exact e.bijective

/-- The canonical scalar-linear dual base-change equivalence. -/
def dualBaseChangeEquiv : S ⊗[R] Dual R M ≃ₗ[S] Dual S (S ⊗[R] M) :=
  LinearEquiv.ofBijective (dualBaseChangeMap R S M) (dualBaseChangeMap_bijective R S M)

@[simp]
lemma dualBaseChangeEquiv_tmul (a b : S) (f : Dual R M) (x : M) :
    dualBaseChangeEquiv R S M (a ⊗ₜ[R] f) (b ⊗ₜ[R] x) =
      a * b * algebraMap R S (f x) := dualBaseChangeMap_tmul R S M a b f x

end BaseChange


end AdelicBostConjecture.Arithmetic
