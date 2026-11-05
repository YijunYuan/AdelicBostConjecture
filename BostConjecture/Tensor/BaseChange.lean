module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Lift

/-!
# Scalar extension on finite tensor products

The canonical map sends a pure tensor to the tensor of its scalar-extended
factors. This is the forward map used in localization compatibility squares.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Tensor

open PiTensorProduct
open scoped TensorProduct

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
variable {ι : Type*} (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/-- Canonical scalar extension of a tensor, with scalars restricted to the source ring. -/
def scalarExtension : (⨂[R] i, M i) →ₗ[R] (⨂[S] i, S ⊗[R] M i) :=
  PiTensorProduct.lift <| ((tprod S).restrictScalars R).compLinearMap
    (fun i => TensorProduct.mk R S (M i) 1)

@[simp]
theorem scalarExtension_tprod (v : ∀ i, M i) :
    scalarExtension R S M (tprod R v) = tprod S (fun i => 1 ⊗ₜ[R] v i) := by
  simp [scalarExtension]

end BostConjecture.Tensor
