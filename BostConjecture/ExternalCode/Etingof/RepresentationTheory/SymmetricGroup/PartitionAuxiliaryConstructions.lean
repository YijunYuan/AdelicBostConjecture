/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

/- Ported to Lean 4.35.0 for BostConjecture; see the project's CONTRIBUTIONS.md. -/

public import Mathlib.Combinatorics.Enumerative.Partition.Basic

/-!
# Standard tableaux indexed by partitions

## Source

Adapted from <https://github.com/mathlib-initiative/Etingof-RepresentationTheory-draft1>, revision
`c6d86a8bd52065aafb8251fa1cdcd55b609743ef`.
Original source:
* `clean-code/release/RepresentationTheory/SymmetricGroup/PartitionAuxiliaryConstructions.lean`.

The original declaration namespaces and license notices are retained, except for
project-specific adaptations documented in `CONTRIBUTIONS.md`.
Only the sorted row lengths and standard-tableau type needed for the hook-length formula
are retained; permutation subgroups, group-algebra elements and canonical fillings are omitted.
-/

public section

namespace RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions

/-- Associates an auxiliary list of natural numbers with a partition. -/
@[expose] noncomputable def auxiliaryPartitionNatList {n : ℕ} (la : Nat.Partition n) : List ℕ :=
  la.parts.sort (· ≥ ·)

/-- An auxiliary type indexed by a natural number and a partition of it. -/
@[expose] noncomputable def AuxiliaryPartitionSource (n : ℕ) (la : Nat.Partition n) : Type :=
  let parts := (auxiliaryPartitionNatList la)
  let Cell := { c : ℕ × ℕ // c.1 < parts.length ∧ c.2 < parts.getD c.1 0 }
  { f : Cell → Fin n //
    Function.Bijective f ∧
    (∀ c₁ c₂ : Cell, c₁.1.1 = c₂.1.1 → c₁.1.2 < c₂.1.2 → f c₁ < f c₂) ∧
    (∀ c₁ c₂ : Cell, c₁.1.2 = c₂.1.2 → c₁.1.1 < c₂.1.1 → f c₁ < f c₂) }

end RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions
