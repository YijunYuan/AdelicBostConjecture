/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

/-
Modified for AdelicBostConjecture: extracted the two projection declarations added by
Nailin Guan in Mathlib PR #40948 at b642b6723caf97b7b462dd5ddeabb0226c3b5433.
See AdelicBostConjecture/ExternalCode/MathlibPRs/PR40948/PROVENANCE.json.
-/
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading

/-!
# Projection from the exterior algebra onto a homogeneous exterior power

## Source

Adapted from <https://github.com/Thmoas-Guan/mathlib4_fork>, revision
`b642b6723caf97b7b462dd5ddeabb0226c3b5433`.
Original source:
* `Mathlib.LinearAlgebra.ExteriorAlgebra.Grading`.

The original declaration namespaces and license notices are retained, except for
project-specific adaptations documented in the project contribution records.
-/

@[expose] public section

namespace ExteriorAlgebra

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]

/-- Projection from `ExteriorAlgebra` to exterior power. -/
def toExteriorPower (i : ℕ) : ExteriorAlgebra R M →ₗ[R] (⋀[R]^i M) :=
    (DFinsupp.lapply i).comp (GradedAlgebra.liftι R M).toLinearMap

lemma toExteriorPower_eq (i : ℕ) (x : ⋀[R]^i M) : toExteriorPower R M i x = x := by
  simp [toExteriorPower, GradedAlgebra.liftι_eq]

end ExteriorAlgebra
