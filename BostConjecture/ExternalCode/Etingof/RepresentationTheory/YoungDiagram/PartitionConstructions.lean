/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

/- Ported to Lean 4.35.0 for BostConjecture; see the project's CONTRIBUTIONS.md. -/

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Combinatorics.Young.YoungDiagram

/-!
# Auxiliary partition constructions

## Source

Adapted from <https://github.com/mathlib-initiative/Etingof-RepresentationTheory-draft1>, revision
`c6d86a8bd52065aafb8251fa1cdcd55b609743ef`.
Original source:
* `clean-code.release.RepresentationTheory.YoungDiagram.PartitionConstructions`.

The original declaration namespaces and license notices are retained, except for
project-specific adaptations documented in the project contribution records.
The unused semistandard-tableau counting function is omitted.
-/

@[expose] public section

namespace RepresentationTheory.YoungDiagram.PartitionConstructions

/-- Assigns an auxiliary Young diagram to each partition of a natural number. -/
noncomputable def auxiliaryYoungDiagramOfPartition {n : ℕ} (μ : Nat.Partition n) : YoungDiagram :=
  YoungDiagram.ofRowLens (μ.parts.sort (· ≥ ·))
    (List.sortedGE_iff_pairwise.mpr (Multiset.pairwise_sort (s := μ.parts) (r := (· ≥ ·))))

end RepresentationTheory.YoungDiagram.PartitionConstructions
