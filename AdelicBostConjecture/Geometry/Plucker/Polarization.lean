/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import AdelicBostConjecture.InvariantTheory.Polynomial.Action
public import Mathlib.LinearAlgebra.SpecialLinearGroup

/-!
# Homogeneous powers and the tensor special-linear action

Powers preserve homogeneous invariants, with the degree multiplied by the exponent.
The binary tensor product carries the independent special-linear action.
-/

@[expose] public section

noncomputable section

namespace AdelicBostConjecture.Geometry

open Module InvariantTheory
open scoped TensorProduct

variable {F : Type*} [Field F] {X : Type*} [AddCommGroup X] [Module F X]

/-- Powers multiply the intrinsic homogeneous degree. -/
theorem homogeneousPolynomials_pow {d : ℕ}
    {p : SymmetricAlgebra F (Dual F X)}
    (hp : p ∈ homogeneousPolynomials F X d) (r : ℕ) :
    p ^ r ∈ homogeneousPolynomials F X (d * r) := by
  induction r with
  | zero => simp [homogeneousPolynomials]
  | succ r ih =>
    rw [pow_succ', Nat.mul_succ, Nat.add_comm, homogeneousPolynomials, pow_add]
    exact Submodule.mul_mem_mul hp ih

/-- Homogeneous invariants remain invariant under taking powers. -/
theorem homogeneousInvariants_pow {G : Type*} [Group G]
    (ρ : Representation F G X) {d : ℕ}
    {p : SymmetricAlgebra F (Dual F X)}
    (hp : p ∈ homogeneousInvariants ρ d) (r : ℕ) :
    p ^ r ∈ homogeneousInvariants ρ (d * r) := by
  apply (mem_homogeneousInvariants_iff _ _ _).mpr
  refine ⟨homogeneousPolynomials_pow hp.1 r, ?_⟩
  intro g
  rw [map_pow, (mem_homogeneousInvariants_iff _ _ _).mp hp |>.2 g]

/-- The independent special-linear action on the actual binary tensor product. -/
def tensorSpecialLinearRepresentation (F : Type*) [Field F]
    (U W : Type*) [AddCommGroup U] [Module F U] [AddCommGroup W] [Module F W] :
    Representation F (SpecialLinearGroup F U × SpecialLinearGroup F W) (U ⊗[F] W) :=
  Representation.tprod
    ((LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
      SpecialLinearGroup.toLinearEquiv).comp (MonoidHom.fst _ _))
    ((LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
      SpecialLinearGroup.toLinearEquiv).comp (MonoidHom.snd _ _))

end AdelicBostConjecture.Geometry
