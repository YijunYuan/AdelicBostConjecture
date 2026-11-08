/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/
module

public import BostConjecture.Specht.Lattice.Basis
public import BostConjecture.ExternalCode.Etingof.RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics
public import Mathlib.Combinatorics.Enumerative.Partition.YoungDiagram

/-!
# Hook enumeration of the existing standard tableaux

Inverting an enumerating tableau identifies it with the increasing fillings
counted by the imported hook formula. The cell comparison adapts the private
`sytCell_iff_mem_toYoungDiagram` and `sytCellEquiv` from the attributed Etingof
extraction; see `CONTRIBUTIONS.md`. No new tableau representation is introduced.

## Source

The two cell comparisons adapt
`clean-code/release/RepresentationTheory/Combinatorics/YoungDiagram/CornerStatistics.lean`
from <https://github.com/mathlib-initiative/Etingof-RepresentationTheory-draft1>, revision
`c6d86a8bd52065aafb8251fa1cdcd55b609743ef`, under Apache-2.0.
The inversion and compatibility with the project's standard tableaux are local bridge proofs.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Specht

open OAI.Saxl
open RepresentationTheory.SymmetricGroup.PartitionAuxiliaryConstructions
open RepresentationTheory.YoungDiagram.PartitionConstructions
open RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics

variable {n : ℕ}

/-- The row-length cell predicate agrees with membership in the Young diagram. -/
theorem partitionCell_mem (p : Nat.Partition n) (c : ℕ × ℕ) :
    (c.1 < (auxiliaryPartitionNatList p).length ∧
      c.2 < (auxiliaryPartitionNatList p).getD c.1 0) ↔
      c ∈ (auxiliaryYoungDiagramOfPartition p).cells := by
  simp only [auxiliaryYoungDiagramOfPartition, auxiliaryPartitionNatList,
    YoungDiagram.mem_cells, YoungDiagram.mem_ofRowLens]
  constructor
  · rintro ⟨h, hc⟩
    have he := List.getD_eq_getElem _ 0 h
    exact ⟨h, by omega⟩
  · rintro ⟨h, hc⟩
    have he := List.getD_eq_getElem _ 0 h
    exact ⟨h, by omega⟩

/-- The partition cell convention preserves the two box coordinates. -/
def partitionCellEquiv (p : Nat.Partition n) :
    {c : ℕ × ℕ // c.1 < (auxiliaryPartitionNatList p).length ∧
      c.2 < (auxiliaryPartitionNatList p).getD c.1 0} ≃
      (auxiliaryYoungDiagramOfPartition p).cells where
  toFun c := ⟨c, (partitionCell_mem p c).mp c.property⟩
  invFun c := ⟨c, (partitionCell_mem p c).mpr c.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Inversion identifies enumerating standard tableaux with the imported fillings. -/
def standardTableauEquivPartition (p : Nat.Partition n) :
    {t : Tableau n (auxiliaryYoungDiagramOfPartition p) // IsStandard t} ≃
      AuxiliaryPartitionSource n p where
  toFun T := ⟨T.val.symm ∘ partitionCellEquiv p,
    T.val.symm.bijective.comp (partitionCellEquiv p).bijective, by
      constructor
      · intro c d hr hc
        simpa using T.property.1 (T.val.symm (partitionCellEquiv p c))
          (T.val.symm (partitionCellEquiv p d)) (by simpa [partitionCellEquiv] using hr)
          (by simpa [partitionCellEquiv] using hc)
      · intro c d hc hr
        simpa using T.property.2 (T.val.symm (partitionCellEquiv p c))
          (T.val.symm (partitionCellEquiv p d)) (by simpa [partitionCellEquiv] using hc)
          (by simpa [partitionCellEquiv] using hr)⟩
  invFun F := ⟨(Equiv.ofBijective F.val F.property.1).symm.trans (partitionCellEquiv p), by
    constructor
    · intro i j hr hc
      have h := F.property.2.1 ((Equiv.ofBijective F.val F.property.1).symm i)
        ((Equiv.ofBijective F.val F.property.1).symm j) hr hc
      change (Equiv.ofBijective F.val F.property.1) _ <
        (Equiv.ofBijective F.val F.property.1) _ at h
      simpa only [Equiv.apply_symm_apply] using h
    · intro i j hc hr
      have h := F.property.2.2 ((Equiv.ofBijective F.val F.property.1).symm i)
        ((Equiv.ofBijective F.val F.property.1).symm j) hc hr
      change (Equiv.ofBijective F.val F.property.1) _ <
        (Equiv.ofBijective F.val F.property.1) _ at h
      simpa only [Equiv.apply_symm_apply] using h⟩
  left_inv T := by
    apply Subtype.ext
    apply Equiv.ext
    intro i
    apply T.val.symm.injective
    simpa only [Equiv.symm_apply_apply, Equiv.trans_apply, Equiv.ofBijective_apply,
      Function.comp_apply] using
      (Equiv.ofBijective (T.val.symm ∘ partitionCellEquiv p)
        (T.val.symm.bijective.comp (partitionCellEquiv p).bijective)).apply_symm_apply i
  right_inv F := by
    apply Subtype.ext
    funext c
    simp [Function.comp_def]

/-- The imported tableau count is the cardinality of the accepted standard basis index. -/
theorem card_standard_eq_partition (p : Nat.Partition n) :
    Fintype.card {t : Tableau n (auxiliaryYoungDiagramOfPartition p) // IsStandard t} =
      Nat.card (AuxiliaryPartitionSource n p) := by
  simpa only [← Nat.card_eq_fintype_card] using Nat.card_congr (standardTableauEquivPartition p)

/-- Hook enumeration for any diagram, expressed in the existing tableau model. -/
theorem card_standard_mul_hookProduct (μ : YoungDiagram) (h : μ.card = n) :
    Fintype.card {t : Tableau n μ // IsStandard t} *
      μ.cells.prod (fun c => μ.rowLen c.1 + μ.colLen c.2 - c.1 - c.2 - 1) =
      n.factorial := by
  have hp := Partition.auxiliaryCard_mul_hookLengthProduct_eq_factorial n (μ.toPartition h)
  rw [← card_standard_eq_partition] at hp
  have he : auxiliaryYoungDiagramOfPartition (μ.toPartition h) = μ :=
    YoungDiagram.ofPartition_toPartition h
  simp only [← Nat.card_eq_fintype_card] at hp ⊢
  rw [he] at hp
  simpa only [YoungDiagram.auxiliaryDiagramStatistic,
    YoungDiagram.auxiliaryCellStatistic] using hp

end BostConjecture.Specht
