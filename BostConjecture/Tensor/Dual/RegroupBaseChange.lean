/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Tensor.Dual.EvaluationBaseChange
public import BostConjecture.Tensor.Dual.Regroup

/-!
# Scalar extension of the canonical dual regrouping

The regrouping of tensor powers of projective duals commutes with
scalar extension. This identifies the integral construction with the
regrouping used at each complex embedding.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Tensor

open Module PiTensorProduct
open scoped TensorProduct

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
  {ι κ : Type*} [Finite ι] [Finite κ]

variable (E : ι → Type*)
  [∀ i, AddCommGroup (E i)] [∀ i, Module R (E i)]
  [∀ i, Module.Finite R (E i)] [∀ i, Module.Projective R (E i)]

/-- The canonical scalar-extension identification of the ambient tensor dual. -/
def tensorDualBaseChangeEquiv : S ⊗[R] Dual R (⨂[R] i, E i) ≃ₗ[S]
    Dual S (⨂[S] i, S ⊗[R] E i) :=
  (Arithmetic.dualBaseChangeEquiv R S (⨂[R] i, E i)).trans
    (baseChangeEquiv R S E).symm.dualMap

/-- Tensor duality itself commutes with the canonical scalar-extension maps. -/
theorem dualDistrib_baseChange (u : S ⊗[R] (⨂[R] i, Dual R (E i))) :
    tensorDualBaseChangeEquiv R S E
      ((dualDistribEquivOfProjective R E).toLinearMap.baseChange S u) =
    dualDistribEquivOfProjective S (fun i => S ⊗[R] E i)
      (map (fun i => (Arithmetic.dualBaseChangeEquiv R S (E i)).toLinearMap)
        (baseChangeEquiv R S (fun i => Dual R (E i)) u)) := by
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := (baseChangeEquiv R S E).surjective x
  simpa [tensorDualBaseChangeEquiv] using (evaluation_baseChange R S E u x).symm

@[simp]
theorem tensorDualBaseChangeEquiv_tprod (f : ∀ i, Dual R (E i)) :
    tensorDualBaseChangeEquiv R S E
      (1 ⊗ₜ[R] dualDistribEquivOfProjective R E (tprod R f)) =
    dualDistribEquivOfProjective S (fun i => S ⊗[R] E i)
      (tprod S (fun i => Arithmetic.dualBaseChangeEquiv R S (E i) (1 ⊗ₜ[R] f i))) := by
  simpa only [LinearMap.baseChange_tmul, LinearEquiv.coe_coe, baseChangeEquiv_tmul,
    one_smul, map_tprod] using dualDistrib_baseChange R S E (1 ⊗ₜ[R] tprod R f)

/-- The actual finite-projective dual regrouping commutes with scalar extension. -/
theorem dualRegroup_scalarExtension (z : ⨂[R] i, ⨂[R] (_ : κ), Dual R (E i)) :
    map (fun _ : κ => (tensorDualBaseChangeEquiv R S E).toLinearMap)
      (scalarExtension R S (fun _ : κ => Dual R (⨂[R] i, E i))
        (dualRegroupEquiv R E z)) =
    dualRegroupEquiv S (fun i => S ⊗[R] E i)
      (map (fun i =>
        map (fun _ : κ => (Arithmetic.dualBaseChangeEquiv R S (E i)).toLinearMap) ∘ₗ
          (baseChangeEquiv R S (fun _ : κ => Dual R (E i))).toLinearMap)
        (scalarExtension R S (fun i => ⨂[R] (_ : κ), Dual R (E i)) z)) := by
  have h :
      ((map (fun _ : κ => (tensorDualBaseChangeEquiv R S E).toLinearMap)).restrictScalars R) ∘ₗ
        scalarExtension R S (fun _ : κ => Dual R (⨂[R] i, E i)) ∘ₗ
        (dualRegroupEquiv R E).toLinearMap =
      ((dualRegroupEquiv S (fun i => S ⊗[R] E i)).toLinearMap.restrictScalars R) ∘ₗ
        ((map (fun i =>
          map (fun _ : κ => (Arithmetic.dualBaseChangeEquiv R S (E i)).toLinearMap) ∘ₗ
            (baseChangeEquiv R S (fun _ : κ => Dual R (E i))).toLinearMap)).restrictScalars R) ∘ₗ
        scalarExtension R S (fun i => ⨂[R] (_ : κ), Dual R (E i)) := by
    apply tensorTensor_ext R (fun i (_ : κ) => Dual R (E i))
      (Q := ⨂[S] (_ : κ), Dual S (⨂[S] i, S ⊗[R] E i))
    intro f
    simp
  exact LinearMap.congr_fun h z

/-- Compatibility on the entire scalar extension of the iterated tensor product. -/
theorem dualRegroup_baseChange
    (z : S ⊗[R] (⨂[R] i, ⨂[R] (_ : κ), Dual R (E i))) :
    map (fun _ : κ => (tensorDualBaseChangeEquiv R S E).toLinearMap)
      (baseChangeEquiv R S (fun _ : κ => Dual R (⨂[R] i, E i))
        ((dualRegroupEquiv R E).toLinearMap.baseChange S z)) =
    dualRegroupEquiv S (fun i => S ⊗[R] E i)
      (map (fun i =>
        map (fun _ : κ => (Arithmetic.dualBaseChangeEquiv R S (E i)).toLinearMap) ∘ₗ
          (baseChangeEquiv R S (fun _ : κ => Dual R (E i))).toLinearMap)
        (baseChangeEquiv R S (fun i => ⨂[R] (_ : κ), Dual R (E i)) z)) := by
  induction z using TensorProduct.inductionOn with
  | tmul s z =>
    change map (fun _ : κ => (tensorDualBaseChangeEquiv R S E).toLinearMap)
      (s • scalarExtension R S (fun _ : κ => Dual R (⨂[R] i, E i))
        (dualRegroupEquiv R E z)) =
      dualRegroupEquiv S (fun i => S ⊗[R] E i)
        (map _ (s • scalarExtension R S (fun i => ⨂[R] (_ : κ), Dual R (E i)) z))
    simp only [map_smul, dualRegroup_scalarExtension]
  | add x y hx hy => simp only [map_add, hx, hy]

end BostConjecture.Tensor
