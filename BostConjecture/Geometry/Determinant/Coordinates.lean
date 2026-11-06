/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.Determinant

/-!
# Coordinates on the top exterior power

A finite basis canonically trivializes its top exterior power. This module
keeps the determinant-line API independent of rectangular representation theory.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Geometry

open Module exteriorPower

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {a : ℕ}

/-- Coordinates on the actual top exterior power, normalized by the basis wedge. -/
def determinantCoordinates (b : Basis (Fin a) R M) : (⋀[R]^a M) ≃ₗ[R] R :=
  LinearEquiv.ofLinearMap (alternatingMapLinearEquiv b.det)
    (LinearMap.toSpanSingleton R _ (ιMulti R a b))
    (by ext; simp [Basis.det_self])
    (by
      apply exteriorPower.linearMap_ext
      apply b.ext_alternating
      intro p hp
      let σ : Equiv.Perm (Fin a) := Equiv.ofBijective p
        (Finite.injective_iff_bijective.mp hp)
      simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
        LinearMap.id_apply, LinearMap.toSpanSingleton_apply,
        alternatingMapLinearEquiv_apply_ιMulti]
      change b.det (b ∘ σ) • ιMulti R a b = ιMulti R a (b ∘ σ)
      simp [AlternatingMap.map_perm, Basis.det_self])

@[simp]
theorem determinantCoordinates_ιMulti (b : Basis (Fin a) R M) (v : Fin a → M) :
    determinantCoordinates b (ιMulti R a v) = b.det v :=
  alternatingMapLinearEquiv_apply_ιMulti b.det v

@[simp]
theorem determinantCoordinates_symm_apply (b : Basis (Fin a) R M) (r : R) :
    (determinantCoordinates b).symm r = r • ιMulti R a b := rfl

/-- The determinant coordinate of a top wedge transforms by the frame determinant. -/
theorem determinantCoordinates_change_basis (b c : Basis (Fin a) R M)
    (η : ⋀[R]^a M) :
    determinantCoordinates c η =
      (LinearMap.toMatrix b c (LinearMap.id : M →ₗ[R] M)).det *
        determinantCoordinates b η := by
  have h : c.det b = (LinearMap.toMatrix b c (LinearMap.id : M →ₗ[R] M)).det := by
    rw [Basis.det_apply]
    congr 1
    ext i j
    simp [Basis.toMatrix_apply, LinearMap.toMatrix_apply]
  obtain ⟨r, rfl⟩ := (determinantCoordinates b).symm.surjective η
  simp only [determinantCoordinates_symm_apply, map_smul, determinantCoordinates_ιMulti,
    Basis.det_self, smul_eq_mul, mul_one]
  rw [h, mul_comm]

end BostConjecture.Geometry
