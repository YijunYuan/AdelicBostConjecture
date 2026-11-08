/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import BostConjecture.ExternalCode.MathlibPRs.PR44845.LinearAlgebra.PiTensorProduct.Projective
public import BostConjecture.ExternalCode.TauCeti.RepresentationTheory.SchurWeyl.Invariants

/-!
# The permutation commutant through the canonical projective tensor-Hom equivalence

Selected from TauCeti, adapted to the checked Mathlib PR #44845 API.

## Source

Adapted from <https://github.com/TauCetiProject/TauCeti>, revision
`b3b0334ab9203d9faee4b2f34cd75161463ecdd0`.
Original source:
* `TauCeti/RepresentationTheory/Symmetric/TensorAction/Centralizer.lean`.

The original declaration namespaces and license notices are retained, except for
project-specific adaptations documented in `CONTRIBUTIONS.md`.
-/

@[expose] public section

open scoped Nat TensorProduct

namespace PiTensorProduct

universe u v w

section Semiring

variable {R : Type u} {M : Type v} {ι : Type w}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- Permuting the factors is invertible: the operators of the permutation representation compose to
the identity along inverse permutations. -/
private theorem reindexRepresentation_mul_inv (σ : Equiv.Perm ι) :
    reindexRepresentation R M ι σ * reindexRepresentation R M ι σ⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel, map_one]

variable [Finite ι] [Module.Projective R M] [Module.Finite R M]

/-- **The comparison isomorphism carries a permuted pure tensor to the conjugated map.** This is
the pure-tensor case of `PiTensorProduct.piTensorHomEquiv_reindexRepresentation_mul`, and is
Mathlib's compatibility of `PiTensorProduct.map` with `PiTensorProduct.reindex`. -/
theorem piTensorHomEquiv_reindexRepresentation_tprod_mul (σ : Equiv.Perm ι)
    (f : ι → (M →ₗ[R] M)) :
    piTensorHomEquiv R (fun _ : ι => M) (fun _ : ι => M)
          (reindexRepresentation R (M →ₗ[R] M) ι σ (tprod R f)) *
        reindexRepresentation R M ι σ =
      reindexRepresentation R M ι σ *
        piTensorHomEquiv R (fun _ : ι => M) (fun _ : ι => M) (tprod R f) := by
  rw [reindexRepresentation_apply, LinearEquiv.coe_toLinearMap, reindex_tprod,
    piTensorHomEquiv_apply, piTensorHomMap_tprod_eq_map, piTensorHomEquiv_apply,
    piTensorHomMap_tprod_eq_map, reindexRepresentation_apply,
    Module.End.mul_eq_comp, Module.End.mul_eq_comp]
  exact map_comp_reindex_eq f σ

/-- **The comparison isomorphism intertwines the two actions.** Permuting the factors of a tensor
of endomorphisms is conjugating the corresponding endomorphism of the tensor power by the
permutation of the factors. -/
theorem piTensorHomEquiv_reindexRepresentation_mul (σ : Equiv.Perm ι)
    (x : ⨂[R] _ : ι, M →ₗ[R] M) :
    piTensorHomEquiv R (fun _ : ι => M) (fun _ : ι => M)
          (reindexRepresentation R (M →ₗ[R] M) ι σ x) *
        reindexRepresentation R M ι σ =
      reindexRepresentation R M ι σ *
        piTensorHomEquiv R (fun _ : ι => M) (fun _ : ι => M) x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [map_smul, LinearEquiv.map_smul, LinearEquiv.map_smul, smul_mul_assoc, mul_smul_comm,
      piTensorHomEquiv_reindexRepresentation_tprod_mul]
  | add x y hx hy =>
    rw [map_add, LinearEquiv.map_add, LinearEquiv.map_add, add_mul, mul_add, hx, hy]

end Semiring

section Ring

variable {R : Type u} {M : Type v} {ι : Type w}
variable [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι]
  [Module.Projective R M] [Module.Finite R M]

/-- **The commutant of the permutation action on a tensor power is the span of the diagonal
operators.** For a finite projective module `M` and `(#ι)!` invertible in `R`, an endomorphism of
`⨂[R] (_ : ι), M` commutes with every permutation of the tensor factors exactly when it is an
`R`-linear combination of the operators `f^{⊗ι}` applying one endomorphism `f` in every factor.

Diagonal tensor operators commute with factor permutations; conversely, their span
exhausts the commutant. -/
theorem mem_span_range_map_const_iff_forall_commute (h : IsUnit ((Fintype.card ι)! : R))
    (T : (⨂[R] _ : ι, M) →ₗ[R] ⨂[R] _ : ι, M) :
    T ∈ Submodule.span R (Set.range fun f : M →ₗ[R] M => map fun _ : ι => f) ↔
      ∀ σ : Equiv.Perm ι, Commute T (reindexRepresentation R M ι σ) := by
  -- The diagonal operators are the images of the pure powers of endomorphisms.
  have hdiag : (fun f : M →ₗ[R] M => map fun _ : ι => f) =
      ⇑(piTensorHomEquiv R (fun _ : ι => M) (fun _ : ι => M)).toLinearMap ∘
        fun f : M →ₗ[R] M => ⨂ₜ[R] (_ : ι), f := by
    funext f
    simp [piTensorHomMap_tprod_eq_map]
  -- So their span is the image of the invariants under the comparison map.
  have hspan : Submodule.span R (Set.range fun f : M →ₗ[R] M => map fun _ : ι => f) =
      Submodule.map (piTensorHomEquiv R (fun _ : ι => M) (fun _ : ι => M)).toLinearMap
        (reindexRepresentation R (M →ₗ[R] M) ι).invariants := by
    rw [invariants_reindexRepresentation h, Submodule.map_span, ← Set.range_comp, hdiag]
  rw [hspan, Submodule.mem_map_equiv, Representation.mem_invariants]
  refine forall_congr' fun σ => ?_
  -- Being fixed by `σ` is, after comparison, commuting with the permutation of the factors.
  have hkey := piTensorHomEquiv_reindexRepresentation_mul σ
    ((piTensorHomEquiv R (fun _ : ι => M) (fun _ : ι => M)).symm T)
  rw [LinearEquiv.apply_symm_apply] at hkey
  refine ⟨fun hfix => ?_, fun hcomm => ?_⟩
  · rw [Commute, SemiconjBy, ← hkey, hfix, LinearEquiv.apply_symm_apply]
  · refine (piTensorHomEquiv R (fun _ : ι => M) (fun _ : ι => M)).injective ?_
    rw [LinearEquiv.apply_symm_apply]
    have hcancel := congrArg (· * reindexRepresentation R M ι σ⁻¹) (hkey.trans hcomm.symm)
    simpa only [mul_assoc, reindexRepresentation_mul_inv, mul_one] using hcancel

end Ring

end PiTensorProduct
