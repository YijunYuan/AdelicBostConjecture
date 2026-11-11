/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Adelic.Semistability.Independent

/-!
# Line factors in irreducible isometric actions

A trivial action on a one-dimensional factor preserves irreducibility.
The actual completed orthogonal tensor norms are invariant, so the group
criterion applies to the binary tensor type used by determinant--Specht bundles.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace BostConjecture.Arithmetic

variable {K G D E : Type*} [Field K] [Group G]
  [AddCommGroup D] [Module K D] [FiniteDimensional K D]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

end BostConjecture.Arithmetic
