/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import AdelicBostConjecture.ExternalCode.TauCeti.RepresentationTheory.SchurWeyl.Centralizer
public import AdelicBostConjecture.ExternalCode.TauCeti.RepresentationTheory.SchurWeyl.DoubleCentralizer
public import AdelicBostConjecture.ExternalCode.TauCeti.RepresentationTheory.SchurWeyl.GeneralLinear
public import Mathlib.RepresentationTheory.Maschke

/-!
# The permutation span is the diagonal commutant

Selected TauCeti double-centralizer argument, generalized from coordinate
spaces to the existing finite-dimensional module and reindexing APIs.
See the accompanying provenance records.

## Source

Adapted from <https://github.com/TauCetiProject/TauCeti>, revision
`b3b0334ab9203d9faee4b2f34cd75161463ecdd0`.
Original source:
* `TauCeti.RepresentationTheory.Symmetric.TensorAction.SchurWeyl`.

The original declaration namespaces and license notices are retained, except for
project-specific adaptations documented in the project contribution records.
-/

@[expose] public section

open scoped TensorProduct

namespace PiTensorProduct

variable {F M ι : Type*} [Field F] [AddCommGroup M] [Module F M]
  [FiniteDimensional F M] [Fintype ι]

/-- The centralizer of the permutation image is the diagonal span. -/
theorem coe_centralizer_reindex_eq_diagonal_span
    (h : IsUnit ((Fintype.card ι).factorial : F)) :
    (Subalgebra.centralizer F
      ((reindexRepresentation F M ι).asAlgebraHom.range : Set (Module.End F (⨂[F] _ : ι, M))) :
      Set (Module.End F (⨂[F] _ : ι, M))) =
    (Submodule.span F (Set.range fun f : M →ₗ[F] M => map fun _ : ι => f) :
      Set (Module.End F (⨂[F] _ : ι, M))) := by
  ext y
  rw [SetLike.mem_coe, SetLike.mem_coe, AlgHom.coe_range,
    Representation.mem_centralizer_range_asAlgebraHom_iff,
    mem_span_range_map_const_iff_forall_commute h]

variable [NeZero ((Fintype.card ι).factorial : F)]

/-- Semisimplicity of the permutation group-algebra image gives the reverse commutant. -/
theorem centralizer_diagonal_span_eq_reindex_range :
    Subalgebra.centralizer F
      (Submodule.span F (Set.range fun f : M →ₗ[F] M => map fun _ : ι => f) :
        Set (Module.End F (⨂[F] _ : ι, M))) =
      (reindexRepresentation F M ι).asAlgebraHom.range := by
  classical
  have : NeZero (Nat.card (Equiv.Perm ι) : F) := by
    rwa [Nat.card_eq_fintype_card, Fintype.card_perm]
  rw [← coe_centralizer_reindex_eq_diagonal_span (isUnit_iff_ne_zero.2 (NeZero.ne _))]
  have := Module.Finite.of_restrictScalars_finite F
    (Module.End (reindexRepresentation F M ι).asAlgebraHom.range (⨂[F] _ : ι, M))
    (⨂[F] _ : ι, M)
  exact AlgHom.centralizer_centralizer_range (reindexRepresentation F M ι).asAlgebraHom

/-- Schur-Weyl as a span-membership criterion, with no faithfulness or dimension bound. -/
theorem mem_permutation_span_iff_commute_diagonal (T : Module.End F (⨂[F] _ : ι, M)) :
    T ∈ Submodule.span F (Set.range (reindexRepresentation F M ι)) ↔
      ∀ f : M →ₗ[F] M, Commute T (map fun _ : ι => f) := by
  rw [← Representation.toSubmodule_range_asAlgebraHom,
    ← centralizer_diagonal_span_eq_reindex_range]
  change T ∈ Subalgebra.centralizer F _ ↔ _
  rw [Subalgebra.mem_centralizer_iff]
  refine ⟨fun h f => (h _ (Submodule.subset_span ⟨f, rfl⟩)).symm, fun h g hg => ?_⟩
  refine (Commute.span_right ?_ g hg).symm
  rintro _ ⟨f, rfl⟩
  exact h f

/-- It suffices to commute with invertible diagonal operators. -/
theorem mem_permutation_span_of_commute_units [Infinite F]
    (T : Module.End F (⨂[F] _ : ι, M))
    (hT : ∀ g : (Module.End F M)ˣ, Commute T (map fun _ : ι => (g : Module.End F M))) :
    T ∈ Submodule.span F (Set.range (reindexRepresentation F M ι)) := by
  apply (mem_permutation_span_iff_commute_diagonal T).mpr
  intro f
  apply Commute.span_right (R := F) (fun x hx => ?_) _ (map_const_mem_span_range_map_const_units f)
  obtain ⟨g, rfl⟩ := hx
  exact hT g

end PiTensorProduct
