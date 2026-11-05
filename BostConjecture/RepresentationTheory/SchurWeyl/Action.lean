/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic

/-! Selected permutation action and group-algebra range API.
See vendor/tauceti-schur-weyl/PROVENANCE.md for the pinned source and scope. -/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace PiTensorProduct

variable (R : Type u) (M : Type v) (ι : Type w)
variable [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The representation of the permutation group of `ι` on the `ι`-indexed tensor power,
acting by reindexing the tensor factors. -/
noncomputable def reindexRepresentation :
    Representation R (Equiv.Perm ι) (⨂[R] _ : ι, M) where
  toFun σ := (reindex R (fun _ : ι => M) σ).toLinearMap
  map_one' := by
    simpa only [Equiv.Perm.one_def, Module.End.one_eq_id,
      LinearEquiv.refl_toLinearMap] using
      congrArg LinearEquiv.toLinearMap
        (reindex_refl (R := R) (s := fun _ : ι => M))
  map_mul' σ τ := by
    apply LinearMap.ext
    intro x
    simp only [Module.End.mul_apply, LinearEquiv.coe_toLinearMap]
    simpa only [Equiv.Perm.mul_def] using
      (reindex_reindex (R := R) (s := fun _ : ι => M) τ σ x).symm

/-- The permutation representation acts by `PiTensorProduct.reindex`. -/
@[simp]
theorem reindexRepresentation_apply (σ : Equiv.Perm ι) :
    reindexRepresentation R M ι σ = (reindex R (fun _ : ι => M) σ).toLinearMap :=
  (rfl)

/-- Permuting factors commutes with applying the same linear map in every tensor factor. -/
theorem commute_reindexRepresentation_map (σ : Equiv.Perm ι) (f : M →ₗ[R] M) :
    Commute (reindexRepresentation R M ι σ) (map fun _ : ι => f) := by
  apply LinearMap.ext
  intro x
  simpa only [Module.End.mul_apply, reindexRepresentation_apply,
    LinearEquiv.coe_toLinearMap] using
    (map_reindex (f := fun _ : ι => f) σ x).symm


end PiTensorProduct
section Range

namespace MonoidAlgebra

variable {k G A : Type*} [CommSemiring k] [Monoid G] [Semiring A] [Algebra k A]

/-- **The image of a monoid-algebra lift is the span of the image of the monoid homomorphism.**
The monoid algebra `k[G]` is spanned by the elements of `G`, so an element of its image is a finite
`k`-combination of the elements `F g`, and conversely every `F g` lies in the image. -/
theorem toSubmodule_range_lift (F : G →* A) :
    Subalgebra.toSubmodule (MonoidAlgebra.lift k A G F).range =
      Submodule.span k (Set.range F) := by
  -- `k[G]` is spanned by `G`: each element lies in the span of its support
  -- (`MonoidAlgebra.mem_span_support_coeff`), a subset of the image of `MonoidAlgebra.of`
  have htop : Submodule.span k (Set.range ⇑(MonoidAlgebra.of k G)) = ⊤ :=
    eq_top_iff.2 fun a _ =>
      Submodule.span_mono (Set.image_subset_range _ _) (MonoidAlgebra.mem_span_support_coeff a)
  -- and `F` is the composite of `MonoidAlgebra.of` with the monoid-algebra lift
  have hrange : Set.range F = (MonoidAlgebra.lift k A G F).toLinearMap ''
      Set.range ⇑(MonoidAlgebra.of k G) := by
    rw [← Set.range_comp]
    simp [Function.comp_def]
  rw [hrange, ← Submodule.map_span, htop, Submodule.map_top]
  ext x
  simp [AlgHom.mem_range]

end MonoidAlgebra

namespace Representation

variable {k G V : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]

/-- **The image of a representation's monoid-algebra action is the span of the representation.** -/
theorem toSubmodule_range_asAlgebraHom (ρ : Representation k G V) :
    Subalgebra.toSubmodule ρ.asAlgebraHom.range = Submodule.span k (Set.range ρ) := by
  simpa only [Representation.asAlgebraHom_def] using MonoidAlgebra.toSubmodule_range_lift ρ

/-- If an endomorphism commutes with every operator in a representation, then it commutes with
the action of every element of the monoid algebra. -/
theorem commute_asAlgebraHom_of_forall_commute (ρ : Representation k G V) {x : Module.End k V}
    (h : ∀ g, Commute x (ρ g)) (a : MonoidAlgebra k G) : Commute x (ρ.asAlgebraHom a) := by
  refine Commute.span_right (R := k) (s := Set.range ρ) (fun y hy ↦ ?_) _ ?_
  · obtain ⟨g, rfl⟩ := hy
    exact h g
  · rw [← toSubmodule_range_asAlgebraHom ρ]
    exact ⟨a, rfl⟩

/-- An endomorphism centralizes the image of a representation's monoid-algebra action exactly
when it commutes with every operator in the representation. -/
theorem mem_centralizer_range_asAlgebraHom_iff (ρ : Representation k G V) {x : Module.End k V} :
    x ∈ Subalgebra.centralizer k (Set.range ⇑ρ.asAlgebraHom) ↔ ∀ g, Commute x (ρ g) := by
  rw [Subalgebra.mem_centralizer_iff]
  refine ⟨fun hx g ↦ (hx _ ⟨MonoidAlgebra.of k G g, Representation.asAlgebraHom_of ρ g⟩).symm,
    fun hx y hy ↦ ?_⟩
  obtain ⟨a, rfl⟩ := hy
  exact (commute_asAlgebraHom_of_forall_commute ρ hx a).symm


end Representation
end Range
