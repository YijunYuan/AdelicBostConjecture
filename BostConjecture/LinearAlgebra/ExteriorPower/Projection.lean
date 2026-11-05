/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

Modified for BostConjecture: extracted the two projection declarations added by
Nailin Guan in Mathlib PR #40948 at b642b6723caf97b7b462dd5ddeabb0226c3b5433.
See vendor/mathlib-prs/40948/PROVENANCE.json.
-/
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading

/-! # Projection from the exterior algebra onto a homogeneous exterior power -/

@[expose] public section

namespace ExteriorAlgebra

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]

/-- Projection from `ExteriorAlgebra` to exterior power. -/
def toExteriorPower (i : ℕ) : ExteriorAlgebra R M →ₗ[R] (⋀[R]^i M) :=
    (DFinsupp.lapply i).comp (GradedAlgebra.liftι R M).toLinearMap

lemma toExteriorPower_eq (i : ℕ) (x : ⋀[R]^i M) : toExteriorPower R M i x = x := by
  simp [toExteriorPower, GradedAlgebra.liftι_eq]

end ExteriorAlgebra
