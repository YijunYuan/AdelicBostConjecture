module

public import BostConjecture.Tensor.DualRegroupBaseChange

/-! # Scalar extension of a pairing into a tensor product -/

@[expose] public section

noncomputable section

namespace BostConjecture.Tensor

open Module PiTensorProduct
open scoped TensorProduct

variable {R : Type*} [CommRing R] {κ V W X : Type*} [Fintype κ]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  [AddCommGroup X] [Module R X]
  [Module.Finite R W] [Module.Projective R W]
  [Module.Finite R X] [Module.Projective R X]

/-- Transporting the codomain and its dual by inverse equivalences preserves pairing. -/
theorem tensorPowerPairing_equiv (e : W ≃ₗ[R] X) (f : V →ₗ[R] W)
    (z : ⨂[R] (_ : κ), V) (u : ⨂[R] (_ : κ), Dual R W) :
    tensorPowerPairing (e.toLinearMap ∘ₗ f) z
      (map (fun _ : κ => e.symm.dualMap.toLinearMap) u) =
      tensorPowerPairing f z u := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    induction u using PiTensorProduct.induction_on with
    | smul_tprod s g => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

end BostConjecture.Tensor
