/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Copyright (c) 2026 Daniel Horton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Fabian Glöckle, Kyle Miller, Daniel Horton
-/
module

public import Mathlib.LinearAlgebra.Dual.Defs

/-!
# Dual of the base ring

Selective extraction from Mathlib PR #44845 at commit
47365e3b9fd4329f058c31ac7aa9565a6036b17d.
Changed file: extracted the equivalence and its inverse application lemma into this
project-local module; proofs and canonical declaration names are unchanged.

## Source

Adapted from <https://github.com/DanielJHorton/mathlib4>, revision
`47365e3b9fd4329f058c31ac7aa9565a6036b17d`.
Original source:
* `Mathlib.LinearAlgebra.Dual.Defs`.

The original declaration namespaces and license notices are retained, except for
project-specific adaptations documented in the project contribution records.
-/

@[expose] public section

namespace Module.Dual

variable (R : Type*) [CommSemiring R]

/-- A linear equivalence `Dual R R ≃ₗ[R] R` (viewing `R` as a module over itself) whose underlying
linear map is `LinearMap.applyₗ 1` with inverse given by `LinearMap.mulRight R` -/
def dualBaseRingEquiv : Dual R R ≃ₗ[R] R := { LinearMap.applyₗ 1 with
  invFun := LinearMap.mulRight R
  left_inv := by intro; ext; simp
  right_inv := by intro; simp
}

variable {R}

@[simp]
theorem dualBaseRingEquiv_symm_apply (x : R) :
    (dualBaseRingEquiv R).symm x = LinearMap.mulRight R x := rfl

end Module.Dual

