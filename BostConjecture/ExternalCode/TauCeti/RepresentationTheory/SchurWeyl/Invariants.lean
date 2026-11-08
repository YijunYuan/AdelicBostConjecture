/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import BostConjecture.ExternalCode.TauCeti.RepresentationTheory.SchurWeyl.Action
public import BostConjecture.ExternalCode.TauCeti.RepresentationTheory.SchurWeyl.Polarization

/-!
# Symmetric tensors are spanned by pure powers. Selected TauCeti proof;

the final averaging argument is direct and imports no additional representation API.

## Source

Adapted from <https://github.com/TauCetiProject/TauCeti>, revision
`b3b0334ab9203d9faee4b2f34cd75161463ecdd0`.
Original source:
* `TauCeti/RepresentationTheory/Symmetric/TensorAction/Invariants.lean`.

The original declaration namespaces and license notices are retained, except for
project-specific adaptations documented in `CONTRIBUTIONS.md`.
-/

@[expose] public section

open scoped TensorProduct
universe u v w

namespace PiTensorProduct

section

variable {R : Type u} {M : Type v} {ι : Type w}
variable [CommRing R] [AddCommGroup M] [Module R M]

/-- A pure power `⨂ₜ i, x` is fixed by every permutation of the tensor factors. -/
theorem tprod_const_mem_invariants (x : M) :
    (⨂ₜ[R] (_ : ι), x) ∈ (reindexRepresentation R M ι).invariants := by
  intro σ
  rw [reindexRepresentation_apply, LinearEquiv.coe_toLinearMap, reindex_tprod]

end

section

variable {R : Type u} {M : Type v} {ι : Type w}
variable [CommRing R] [AddCommMonoid M] [Module R M] [Fintype ι] [DecidableEq ι]

/-- Symmetrizing any tensor lands in the span of the pure powers. -/
theorem sum_reindexRepresentation_mem_span (y : ⨂[R] _ : ι, M) :
    ∑ σ : Equiv.Perm ι, reindexRepresentation R M ι σ y ∈
      Submodule.span R (Set.range fun x : M => ⨂ₜ[R] (_ : ι), x) := by
  classical
  have hy : y ∈ (⊤ : Submodule R (⨂[R] _ : ι, M)) := Submodule.mem_top
  rw [← span_tprod_eq_top] at hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨m, rfl⟩ := hz
    have hperm : ∀ σ : Equiv.Perm ι, reindexRepresentation R M ι σ (tprod R m) =
        ⨂ₜ[R] i, m (σ⁻¹ i) := by
      intro σ
      rw [reindexRepresentation_apply, LinearEquiv.coe_toLinearMap, reindex_tprod]
      rfl
    have hinv : (∑ σ : Equiv.Perm ι, ⨂ₜ[R] i, m (σ⁻¹ i)) =
        ∑ σ : Equiv.Perm ι, ⨂ₜ[R] i, m (σ i) :=
      Equiv.sum_comp (Equiv.inv (Equiv.Perm ι)) fun σ => ⨂ₜ[R] i, m (σ i)
    rw [Finset.sum_congr rfl fun σ _ => hperm σ, hinv,
      ← sum_neg_one_pow_card_smul_tprod_sum_compl]
    exact Submodule.sum_mem _ fun S _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨_, rfl⟩)
  | zero => simp
  | add z z' hz hz' ihz ihz' => simpa [Finset.sum_add_distrib] using Submodule.add_mem _ ihz ihz'
  | smul r z hz ihz => simpa [← Finset.smul_sum] using Submodule.smul_mem _ r ihz

/-- **The symmetrization operator has the symmetric tensors as its range.** The range of `∑_σ σ` is
the span of the pure powers; the operator scales an invariant tensor by `(#ι)!`, so it is the
projection onto that span only up to that factor. -/
theorem range_sum_reindexRepresentation (h : IsUnit ((Fintype.card ι).factorial : R)) :
    LinearMap.range (∑ σ : Equiv.Perm ι, reindexRepresentation R M ι σ) =
      Submodule.span R (Set.range fun x : M => ⨂ₜ[R] (_ : ι), x) := by
  let := h.invertible
  refine le_antisymm ?_ (Submodule.span_le.mpr ?_)
  · rintro _ ⟨y, rfl⟩
    simpa [LinearMap.sum_apply] using sum_reindexRepresentation_mem_span y
  · rintro _ ⟨x, rfl⟩
    have hfix : ∀ σ : Equiv.Perm ι,
        reindexRepresentation R M ι σ (⨂ₜ[R] (_ : ι), x) = ⨂ₜ[R] (_ : ι), x := fun σ => by simp
    refine ⟨⅟((Fintype.card ι).factorial : R) • (⨂ₜ[R] (_ : ι), x), ?_⟩
    rw [map_smul, LinearMap.sum_apply, Finset.sum_congr rfl fun σ _ => hfix σ,
      Finset.sum_const, Finset.card_univ, Fintype.card_perm, ← Nat.cast_smul_eq_nsmul R, smul_smul,
      invOf_mul_self, one_smul]

end

section

variable {R : Type u} {M : Type v} {ι : Type w}
variable [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι]

/-- **The symmetric tensors are the span of the pure powers.** When `(#ι)!` is invertible in `R`,
the invariants of the permutation action on `⨂[R] (_ : ι), M` are spanned by the pure powers
`⨂ₜ i, x`. -/
@[simp]
theorem invariants_reindexRepresentation (h : IsUnit ((Fintype.card ι).factorial : R)) :
    (reindexRepresentation R M ι).invariants =
      Submodule.span R (Set.range fun x : M => ⨂ₜ[R] (_ : ι), x) := by
  classical
  let := h.invertible
  refine le_antisymm (fun y hy => ?_) (Submodule.span_le.mpr ?_)
  · change ∀ σ, reindexRepresentation R M ι σ y = y at hy
    have hs := sum_reindexRepresentation_mem_span y
    have he : (∑ σ : Equiv.Perm ι, reindexRepresentation R M ι σ y) =
        ((Fintype.card ι).factorial : R) • y := by
      simp only [hy, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
        Nat.cast_smul_eq_nsmul]
    rw [he] at hs
    simpa only [smul_smul, invOf_mul_self, one_smul] using
      Submodule.smul_mem _ (⅟((Fintype.card ι).factorial : R)) hs
  · rintro _ ⟨x, rfl⟩
    exact tprod_const_mem_invariants x

end

end PiTensorProduct
