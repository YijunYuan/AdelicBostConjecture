module

public import BostConjecture.Tensor.Regroup
public import BostConjecture.Tensor.Evaluation

/-!
# Regrouping tensor powers of projective dual modules

This is the integral regrouping used before restriction of the evaluation
pairing. It uses the checked finite-projective duality equivalence directly.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Tensor

open Module PiTensorProduct
open scoped TensorProduct

variable (R : Type*) [CommRing R] {ι κ : Type*} [Finite ι] [Finite κ]
  (E : ι → Type*) [∀ i, AddCommGroup (E i)] [∀ i, Module R (E i)]
  [∀ i, Module.Finite R (E i)] [∀ i, Module.Projective R (E i)]

/-- Regroup tensor powers of dual factors into the tensor power of the ambient dual. -/
def dualRegroupEquiv : (⨂[R] i, ⨂[R] (_ : κ), Dual R (E i)) ≃ₗ[R]
    (⨂[R] (_ : κ), Dual R (⨂[R] i, E i)) :=
  (regroupEquiv R (fun i (_ : κ) => Dual R (E i))).trans
    (congr (fun _ : κ => dualDistribEquivOfProjective R E))

@[simp]
theorem dualRegroupEquiv_tprod (f : ∀ i, κ → Dual R (E i)) :
    dualRegroupEquiv R E (tprod R (fun i => tprod R (f i))) =
      tprod R (fun j => dualDistribEquivOfProjective R E
        (tprod R (fun i => f i j))) := by
  simp [dualRegroupEquiv]

/-- The integral regrouping commutes with simultaneous permutations of tensor positions. -/
theorem dualRegroupEquiv_reindex (σ : Equiv.Perm κ)
    (z : ⨂[R] i, ⨂[R] (_ : κ), Dual R (E i)) :
    dualRegroupEquiv R E
      (map (fun i => (reindex R (fun _ : κ => Dual R (E i)) σ).toLinearMap) z) =
    reindex R (fun _ : κ => Dual R (⨂[R] i, E i)) σ (dualRegroupEquiv R E z) := by
  have h : (dualRegroupEquiv R E).toLinearMap ∘ₗ
      map (fun i => (reindex R (fun _ : κ => Dual R (E i)) σ).toLinearMap) =
      (reindex R (fun _ : κ => Dual R (⨂[R] i, E i)) σ).toLinearMap ∘ₗ
        (dualRegroupEquiv R E).toLinearMap := by
    apply tensorTensor_ext R (fun i (_ : κ) => Dual R (E i))
      (Q := ⨂[R] (_ : κ), Dual R (⨂[R] i, E i))
    intro f
    simp
  exact LinearMap.congr_fun h z

end BostConjecture.Tensor
