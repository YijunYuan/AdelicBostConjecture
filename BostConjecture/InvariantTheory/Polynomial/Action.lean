/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.InvariantTheory.Polynomial.Basic
public import Mathlib.RepresentationTheory.Invariants

/-!
# The action on intrinsic polynomials

The representation on polynomials is inverse pullback. Its homogeneous
invariants are the intersection with the canonical degree subspace. Forward
pullback has exactly the same fixed vectors, by inversion in the group.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.InvariantTheory

variable {K G X : Type*} [Field K] [Group G] [AddCommGroup X] [Module K X]

/-- The symmetric-algebra action by inverse pullback. -/
def polynomialRepresentation (ρ : Representation K G X) :
    Representation K G (SymmetricAlgebra K (Module.Dual K X)) where
  toFun g := (polynomialPullback (ρ g⁻¹)).toLinearMap
  map_one' := by
    change (polynomialPullback (ρ (1 : G)⁻¹)).toLinearMap = _
    rw [inv_one, map_one]
    change (polynomialPullback (LinearMap.id : X →ₗ[K] X)).toLinearMap = _
    rw [polynomialPullback_id]
    rfl
  map_mul' g h := by
    change (polynomialPullback (ρ (g * h)⁻¹)).toLinearMap = _
    rw [mul_inv_rev, map_mul]
    change (polynomialPullback ((ρ h⁻¹).comp (ρ g⁻¹))).toLinearMap = _
    rw [polynomialPullback_comp]
    rfl

@[simp]
theorem polynomialRepresentation_apply (ρ : Representation K G X) (g : G)
    (p : SymmetricAlgebra K (Module.Dual K X)) :
    polynomialRepresentation ρ g p = polynomialPullback (ρ g⁻¹) p := rfl

@[simp]
theorem polynomialEval_representation (ρ : Representation K G X) (g : G) (x : X)
    (p : SymmetricAlgebra K (Module.Dual K X)) :
    polynomialEval x (polynomialRepresentation ρ g p) = polynomialEval (ρ g⁻¹ x) p :=
  polynomialEval_pullback _ _ _

/-- Homogeneous polynomial invariants of degree `d`. -/
def homogeneousInvariants (ρ : Representation K G X) (d : ℕ) :
    Submodule K (SymmetricAlgebra K (Module.Dual K X)) :=
  homogeneousPolynomials K X d ⊓ (polynomialRepresentation ρ).invariants

theorem mem_homogeneousInvariants_iff (ρ : Representation K G X) (d : ℕ)
    (p : SymmetricAlgebra K (Module.Dual K X)) :
    p ∈ homogeneousInvariants ρ d ↔
      p ∈ homogeneousPolynomials K X d ∧ ∀ g, polynomialPullback (ρ g) p = p := by
  change (_ ∧ ∀ g, polynomialPullback (ρ g⁻¹) p = p) ↔ _
  constructor
  · rintro ⟨hd, hi⟩
    exact ⟨hd, fun g => by simpa using hi g⁻¹⟩
  · rintro ⟨hd, hi⟩
    exact ⟨hd, fun g => hi g⁻¹⟩

theorem polynomialEval_orbit_of_mem_invariants (ρ : Representation K G X)
    {p : SymmetricAlgebra K (Module.Dual K X)}
    (hp : p ∈ (polynomialRepresentation ρ).invariants) (g : G) (x : X) :
    polynomialEval (ρ g x) p = polynomialEval x p := by
  have h : polynomialPullback (ρ g) p = p := by simpa using hp g⁻¹
  rw [← polynomialEval_pullback, h]

/-- The action restricted to homogeneous polynomials of one degree. -/
def homogeneousPolynomialRepresentation (ρ : Representation K G X) (d : ℕ) :
    Representation K G (homogeneousPolynomials K X d) :=
  (polynomialRepresentation ρ).subrepresentation (homogeneousPolynomials K X d)
    (fun g _ hp => polynomialPullback_mem_homogeneous (ρ g⁻¹) hp)

@[simp]
theorem homogeneousPolynomialRepresentation_apply (ρ : Representation K G X) (d : ℕ)
    (g : G) (p : homogeneousPolynomials K X d) :
    (homogeneousPolynomialRepresentation ρ d g p : SymmetricAlgebra K (Module.Dual K X)) =
      polynomialRepresentation ρ g p := rfl

/-- Fixed vectors in the degree representation are precisely homogeneous invariants. -/
def homogeneousInvariantsEquiv (ρ : Representation K G X) (d : ℕ) :
    homogeneousInvariants ρ d ≃ₗ[K] (homogeneousPolynomialRepresentation ρ d).invariants where
  toFun p := ⟨⟨p, p.property.1⟩, fun g => Subtype.ext (p.property.2 g)⟩
  invFun p := ⟨p.val.val, p.val.property, fun g => congrArg Subtype.val (p.property g)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance finiteDimensional_homogeneousInvariants [FiniteDimensional K X]
    (ρ : Representation K G X) (d : ℕ) : FiniteDimensional K (homogeneousInvariants ρ d) :=
  Module.Finite.equiv (homogeneousInvariantsEquiv ρ d).symm

end BostConjecture.InvariantTheory
