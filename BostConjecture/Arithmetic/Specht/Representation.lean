/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Specht.Lattice.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The actual integral Specht representation

The action restricts position permutations to the existing integral orbit lattice.

Reference: this paper, §§3, 6, pages 4 and 9.
-/

@[expose] public section

noncomputable section

open TensorProduct

namespace BostConjecture.Arithmetic.Specht

open BostConjecture.Specht

variable {n : ℕ} {μ : YoungDiagram}

/-- The existing orbit-lattice action, with its representation laws. -/
def integralRepresentation (t : OAI.Saxl.Tableau n μ) :
    Representation ℤ (Equiv.Perm (Fin n)) (orbitLattice t) where
  toFun := orbitAction t
  map_one' := by ext x w; rfl
  map_mul' g h := by ext x w; rfl

end BostConjecture.Arithmetic.Specht
