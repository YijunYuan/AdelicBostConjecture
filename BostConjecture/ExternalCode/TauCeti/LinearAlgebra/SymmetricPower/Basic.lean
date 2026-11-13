/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.LinearAlgebra.TensorPower.Symmetric

/-!
# Symmetric power maps and symmetrization

Selectively adapted from TauCeti revision
`3c3a32baea963db05c302adeb307b22baae4de78`; see
`BostConjecture/ExternalCode/TauCeti/Provenance/SymmetricPower/PROVENANCE.md`. Only the natural
tensor section
and its required quotient/map API are retained.

## Source

Adapted from <https://github.com/TauCetiProject/TauCeti>, revision
`3c3a32baea963db05c302adeb307b22baae4de78`.
Original source:
* `TauCeti/LinearAlgebra/SymmetricPower/Basic.lean`.

The original declaration namespaces and license notices are retained, except for
project-specific adaptations documented in `CONTRIBUTIONS.md`.
-/

public section

open scoped TensorProduct

universe u v

-- Mathlib's `SymmetricPower` requires its ring and index type in the same universe.
variable {R ι : Type u} {M : Type v}

namespace SymmetricPower

section CommSemiring

variable [CommSemiring R]
variable [AddCommMonoid M] [Module R M]

/-- A linear map out of a symmetric power is determined by its values on pure symmetric
tensors. -/
@[ext]
theorem ext {N : Type*} [AddCommMonoid N] [Module R N] {g h : Sym[R] ι M →ₗ[R] N}
    (hgh : ∀ m : ι → M, g (⨂ₛ[R] i, m i) = h (⨂ₛ[R] i, m i)) : g = h := by
  refine LinearMap.ext_on (span_tprod_eq_top R ι M) ?_
  rintro _ ⟨m, rfl⟩
  exact hgh m

/-- A linear map sends every symmetric tensor into a submodule if it does so on pure tensors. -/
theorem _root_.LinearMap.apply_mem_of_forall_symmetricPower_tprod {N : Type*} [AddCommMonoid N]
    [Module R N] (f : Sym[R] ι M →ₗ[R] N) (p : Submodule R N)
    (h : ∀ m : ι → M, f (⨂ₛ[R] i, m i) ∈ p) (x : Sym[R] ι M) : f x ∈ p := by
  have hle : (⊤ : Submodule R (Sym[R] ι M)) ≤ p.comap f := by
    rw [← span_tprod_eq_top R ι M, Submodule.span_le]
    rintro _ ⟨m, rfl⟩
    exact h m
  exact hle Submodule.mem_top

private theorem map_rel {N : Type*} [AddCommMonoid N] [Module R N] (f : M →ₗ[R] N) :
    addConGen (Rel R ι M) ≤
      AddCon.ker ((mk R ι N).toAddMonoidHom.comp
        (PiTensorProduct.map fun _ : ι => f).toAddMonoidHom) := by
  apply AddCon.addConGen_le.2
  intro x y h
  cases h with
  | perm e m =>
      apply (AddCon.ker_rel _).2
      simpa only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
        PiTensorProduct.map_tprod, tprod, LinearMap.compMultilinearMap_apply,
        Function.comp_apply] using (tprod_equiv (R := R) e (f ∘ m)).symm

/-- A linear map induces a linear map on every symmetric tensor power. -/
noncomputable def map {N : Type*} [AddCommMonoid N] [Module R N] (f : M →ₗ[R] N) :
    Sym[R] ι M →ₗ[R] Sym[R] ι N where
  toFun :=
    (addConGen (Rel R ι M)).lift
      ((mk R ι N).toAddMonoidHom.comp
        (PiTensorProduct.map fun _ : ι => f).toAddMonoidHom)
      (map_rel f)
  map_add' := map_add _
  map_smul' r x := AddCon.induction_on x fun x => by
    exact congrArg (mk R ι N) ((PiTensorProduct.map fun _ : ι => f).map_smul r x)

/-- The map on symmetric powers commutes with the quotient map from the tensor power. -/
@[simp]
theorem map_mk {N : Type*} [AddCommMonoid N] [Module R N] (f : M →ₗ[R] N) (x : ⨂[R] (_ : ι), M) :
    map f (mk R ι M x) = mk R ι N (PiTensorProduct.map (fun _ : ι => f) x) :=
  AddCon.lift_mk' (map_rel f) x

/-- The map induced on symmetric powers sends a pure tensor to the tensor of the images. -/
@[simp]
theorem map_tprod {N : Type*} [AddCommMonoid N] [Module R N] (f : M →ₗ[R] N) (m : ι → M) :
    map f (⨂ₛ[R] i, m i) = ⨂ₛ[R] i, f (m i) := by
  simp only [tprod, LinearMap.compMultilinearMap_apply, map_mk,
    PiTensorProduct.map_tprod]

end CommSemiring

/-!
### The symmetrization back into the tensor power -/

section Symmetrization

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [Fintype ι] [DecidableEq ι]

variable (R ι M) in
/-- The symmetrization operator `∑_σ σ` on the tensor power, permuting the tensor factors. -/
private noncomputable def symmetrizer : (⨂[R] (_ : ι), M) →ₗ[R] ⨂[R] (_ : ι), M :=
  ∑ σ : Equiv.Perm ι, (PiTensorProduct.reindex R (fun _ : ι => M) σ).toLinearMap

private theorem symmetrizer_tprod (m : ι → M) :
    symmetrizer R ι M (⨂ₜ[R] i, m i) = ∑ σ : Equiv.Perm ι, ⨂ₜ[R] i, m (σ i) := by
  rw [symmetrizer, LinearMap.sum_apply]
  refine Fintype.sum_equiv (Equiv.inv (Equiv.Perm ι)) _ _ fun σ => ?_
  simp

private theorem symmetrizer_rel :
    addConGen (Rel R ι M) ≤ AddCon.ker (symmetrizer R ι M).toAddMonoidHom := by
  apply AddCon.addConGen_le.2
  intro x y h
  cases h with
  | perm e m =>
      refine (AddCon.ker_rel _).2 ?_
      simp only [LinearMap.toAddMonoidHom_coe, symmetrizer_tprod]
      refine Fintype.sum_bijective (e⁻¹ * ·) (Group.mulLeft_bijective _) _ _ fun σ => ?_
      congr 1
      funext i
      simp

variable (R ι M) in
/-- **The symmetrization**, from the symmetric power back into the tensor power: the descent of
the symmetrization operator `∑_σ σ` through the quotient map `SymmetricPower.mk`.

This is the counterpart of Mathlib's `exteriorPower.toTensorPower`. -/
noncomputable def toTensorPower : Sym[R] ι M →ₗ[R] ⨂[R] (_ : ι), M where
  toFun := (addConGen (Rel R ι M)).lift (symmetrizer R ι M).toAddMonoidHom symmetrizer_rel
  map_add' := map_add _
  map_smul' r x := AddCon.induction_on x fun x => (symmetrizer R ι M).map_smul r x

private theorem toTensorPower_mk' (x : ⨂[R] (_ : ι), M) :
    toTensorPower R ι M (mk R ι M x) = (symmetrizer R ι M).toAddMonoidHom x :=
  (rfl)

/-- The symmetrization of a pure symmetric tensor is the sum of the pure tensors over all
orderings of its factors. -/
@[simp]
theorem toTensorPower_tprod (m : ι → M) :
    toTensorPower R ι M (⨂ₛ[R] i, m i) = ∑ σ : Equiv.Perm ι, ⨂ₜ[R] i, m (σ i) := by
  rw [tprod, LinearMap.compMultilinearMap_apply, toTensorPower_mk']
  exact symmetrizer_tprod m

/-- Symmetrizing and then projecting back to the symmetric power multiplies by `(card ι)!`: the
`(card ι)!` reorderings of a pure tensor all become the same symmetric tensor. -/
@[simp]
theorem mk_comp_toTensorPower :
    (mk R ι M) ∘ₗ (toTensorPower R ι M) =
      (Fintype.card ι).factorial • LinearMap.id (R := R) (M := Sym[R] ι M) := by
  ext m
  have h (σ : Equiv.Perm ι) : mk R ι M (⨂ₜ[R] i, m (σ i)) = ⨂ₛ[R] i, m i :=
    tprod_equiv σ m
  simp [h, Fintype.card_perm]

/-- The symmetrization is natural in the module. -/
theorem toTensorPower_comp_map {N : Type*} [AddCommMonoid N] [Module R N] (f : M →ₗ[R] N) :
    (toTensorPower R ι N) ∘ₗ (map (ι := ι) f) =
      (PiTensorProduct.map fun _ : ι => f) ∘ₗ (toTensorPower R ι M) := by
  ext m
  simp

end Symmetrization

end SymmetricPower
