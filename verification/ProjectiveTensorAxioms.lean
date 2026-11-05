import BostConjecture.LinearAlgebra.PiTensorProduct.Projective

-- Narrow transitive axiom audit of every public declaration selectively ported from PR #44845.
#print axioms Module.Dual.dualBaseRingEquiv
#print axioms Module.Dual.dualBaseRingEquiv_apply
#print axioms Module.Dual.dualBaseRingEquiv_symm_apply
#print axioms PiTensorProduct.Projective
#print axioms PiTensorProduct.piTensorHomEquiv
#print axioms PiTensorProduct.piTensorHomEquiv_toLinearMap
#print axioms PiTensorProduct.piTensorHomEquiv_apply
#print axioms PiTensorProduct.dualDistribEquivOfProjective
#print axioms PiTensorProduct.dualDistribEquivOfProjective_toLinearMap
#print axioms PiTensorProduct.dualDistribEquivOfProjective_tprod_tprod

-- These consumers retain projectivity without introducing a freeness hypothesis.
open Module PiTensorProduct TensorProduct

section
variable {R ι : Type*} [CommSemiring R] [Finite ι] {P : ι → Type*}
  [∀ i, AddCommMonoid (P i)] [∀ i, Module R (P i)]
  [∀ i, Module.Projective R (P i)] [∀ i, Module.Finite R (P i)]

example : Module.Projective R (⨂[R] i, P i) := inferInstance

example : Function.Bijective
    (PiTensorProduct.dualDistrib : (⨂[R] i, Dual R (P i)) →ₗ[R] Dual R (⨂[R] i, P i)) := by
  exact (PiTensorProduct.dualDistribEquivOfProjective R P).bijective

example (f : ∀ i, Dual R (P i)) (x : ∀ i, P i) :
    PiTensorProduct.dualDistribEquivOfProjective R P (⨂ₜ[R] i, f i) (⨂ₜ[R] i, x i) =
      ∏ᶠ i, f i (x i) :=
  PiTensorProduct.dualDistribEquivOfProjective_tprod_tprod f x
end
