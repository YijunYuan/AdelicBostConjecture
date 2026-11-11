/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Adelic.Geometry.Plucker

/-!
# Nonzero original-field pairings from geometric semistability

This is the algebraic nonvanishing step in the proof of this paper's Theorem 6.2.
It applies to every finite family, in particular to binary families indexed by
`Bool` or by `Unit ⊕ Unit`. The output is the canonical pairing over the original
field at every positive multiple of one common admissible degree.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Adelic.Geometry

open Module BostConjecture.InvariantTheory BostConjecture.Geometry
open scoped TensorProduct

variable {K : Type*} [Field K] [CharZero K] {ι : Type*} [Fintype ι]
  (E : ι → Type*) [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]
  [∀ i, FiniteDimensional K (E i)] [∀ i, Nontrivial (E i)]
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Nontrivial V]

/-- Geometric tensor-subspace semistability produces the actual original-field
determinant pairing in every positive multiple of a common rectangular degree.
All dimensions and rank-at-stalk witnesses are canonical; no basis or invariant
is required as an additional hypothesis. -/
theorem exists_canonicalPairing_nonzero_sequence_of_geometricSemistability
    (A : V →ₗ[K] (⨂[K] i, E i))
    (h : ArakelovGeometry.InvariantTheory.IsGeometricallySemistableTensorSubspace E A) :
    ∃ d₀ : ℕ, 0 < d₀ ∧ Module.finrank K V ∣ d₀ ∧
      (∀ i, Module.finrank K (E i) ∣ d₀) ∧
      ∀ r : ℕ, 0 < r → ∃ (l : ℕ) (k : ι → ℕ) (hl : 0 < l) (hk : ∀ i, 0 < k i)
        (t : ∀ i, OAI.Saxl.Tableau (d₀ * r)
          (Specht.rectangle (Module.finrank K (E i)) (k i)))
        (v : OAI.Saxl.Tableau (d₀ * r) (Specht.rectangle (Module.finrank K V) l)),
        canonicalPairing E hk t (fun i q ↦ by simp) hl v (fun q ↦ by simp) A ≠ 0 := by
  let L := AlgebraicClosure K
  let bV := (Module.finBasis K V).baseChange L
  let bE := fun i ↦ ((Module.finBasis K (E i)).baseChange L).dualBasis
  change ArakelovGeometry.InvariantTheory.IsPluckerSemistable
    (ArakelovGeometry.InvariantTheory.tensorSLRepresentation (fun i ↦ L ⊗[K] E i))
    ((ArakelovGeometry.tensorBaseChangeEquiv K L E).toLinearMap.comp (A.baseChange L)) at h
  rw [tensorBaseChangeEquiv_eq] at h
  obtain ⟨m, p, hm, hp, hpA⟩ :=
    exists_homogeneousInvariant_of_isPluckerSemistable _ _ bV h
  rw [tensorSLRepresentation_eq] at hp
  obtain ⟨hp, hi⟩ := (mem_homogeneousInvariants_iff _ _ _).mp hp
  exact exists_canonicalPairing_nonzero_sequence (F := L) E A
    Module.finrank_pos (fun _ ↦ Module.finrank_pos) hm
    (fun i q ↦ by simp) (fun q ↦ by simp) bV bE hp hi hpA

end BostConjecture.Adelic.Geometry
