/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/
module

/- Ported to Lean 4.35.0 for AdelicBostConjecture; see the project's CONTRIBUTIONS.md. -/
public import AdelicBostConjecture.ExternalCode.Etingof.RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions

/-!
# Finiteness of standard tableaux of a partition

The partition cells are finite, and consequently the type of bijective,
row- and column-increasing fillings by `Fin n` is finite.

## Source

Adapted from <https://github.com/mathlib-initiative/Etingof-RepresentationTheory-draft1>, revision
`c6d86a8bd52065aafb8251fa1cdcd55b609743ef`.
Original source:
* `clean-code.release.RepresentationTheory.Partition.YoungDiagram`.

The original declaration namespaces and license notices are retained, except for
project-specific adaptations documented in the project contribution records.
-/

@[expose] public section

namespace RepresentationTheory.Partition.YoungDiagram

open RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions

private lemma getD_le_sum (l : List ℕ) (i : ℕ) : l.getD i 0 ≤ l.sum := by
  induction l generalizing i with
  | nil => simp [List.getD]
  | cons a as ih =>
    cases i with
    | zero =>
      show (a :: as).getD 0 0 ≤ (a :: as).sum
      rw [List.getD_cons_zero, List.sum_cons]
      omega
    | succ i =>
      simpa only [List.getD_cons_succ, List.sum_cons] using le_trans (ih i) (Nat.le_add_left _ _)

/-- The sorted parts of a partition sum to its size. -/
lemma sum_sortedParts (n : ℕ) (la : Nat.Partition n) :
    (auxiliaryPartitionNatList la).sum = n := by
  have h := Multiset.sort_eq la.parts (· ≥ ·)
  have : ((auxiliaryPartitionNatList la) : Multiset ℕ).sum = la.parts.sum := congrArg Multiset.sum h
  rw [Multiset.sum_coe] at this; rw [this, la.parts_sum]

/-- The finite type of row-column coordinates lying inside a partition's sorted parts. -/
noncomputable instance cellsFintype (n : ℕ) (la : Nat.Partition n) :
    Fintype { c : ℕ × ℕ //
      c.1 < (auxiliaryPartitionNatList la).length ∧
      c.2 < (auxiliaryPartitionNatList la).getD c.1 0 } := by
  haveI : Fintype { c : ℕ × ℕ //
      c ∈ (Finset.range
        (auxiliaryPartitionNatList la).length ×ˢ Finset.range (n+1)) } :=
    (Finset.range
      (auxiliaryPartitionNatList la).length ×ˢ Finset.range (n+1)).fintypeCoeSort
  apply Fintype.ofInjective
    (fun ⟨c, hc⟩ => (⟨c, by
      simp only [Finset.mem_product, Finset.mem_range]
      exact ⟨hc.1, by
        have := getD_le_sum
          (auxiliaryPartitionNatList la) c.1
        have := sum_sortedParts n la; omega⟩
    ⟩ : { c : ℕ × ℕ //
        c ∈ (Finset.range
          (auxiliaryPartitionNatList la).length ×ˢ Finset.range (n+1)) }))
  intro ⟨a, _⟩ ⟨b, _⟩ h
  exact Subtype.ext (Subtype.mk.inj h)

/-- A finite-type structure on an auxiliary partition-indexed type. -/
noncomputable instance auxiliaryFintype (n : ℕ) (la : Nat.Partition n) :
    Fintype (AuxiliaryPartitionSource n la) := by
  unfold AuxiliaryPartitionSource
  haveI := cellsFintype n la
  exact Subtype.fintype _

/-- An auxiliary partition-indexed type is finite. -/
instance auxiliary_finite (n : ℕ) (la : Nat.Partition n) :
    Finite (AuxiliaryPartitionSource n la) := inferInstance

end RepresentationTheory.Partition.YoungDiagram
