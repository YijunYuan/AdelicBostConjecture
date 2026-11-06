module

public import BostConjecture.Arithmetic.Specht.Bundle
public import BostConjecture.Arithmetic.RestrictionCovolume.Free
public import BostConjecture.Specht.Metric

/-!
# Intrinsic degree of the arithmetic Specht lattice

The actual integral lattice basis has the same Gram determinant in every
archimedean fiber. The intrinsic free-basis degree formula therefore gives
minus the logarithm of the existing lattice covolume.

Reference: `bost_specht_manuscript.pdf`, Lemma 6.1, pages 8–9.
-/

@[expose] public section

noncomputable section

open Module NumberField TensorProduct exteriorPower MeasureTheory

namespace BostConjecture.Arithmetic.Specht

open BostConjecture.Specht

variable {K : Type*} [Field K] [NumberField K] {n : ℕ} {μ : YoungDiagram}

end BostConjecture.Arithmetic.Specht
