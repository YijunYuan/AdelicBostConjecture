/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Specht.Tableau.Basic
public import BostConjecture.Specht.Lattice.Metric

/-!
# The norm of an integral polytabloid

Distinct column permutations give distinct orthonormal row words, so the
squared norm of a polytabloid is the order of its column group.
Reference: this paper §4, page 5 (the initial seminormal norm).
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Specht

open OAI.Saxl

variable {n : ℕ} {μ : YoungDiagram}

/-- Column permutations act freely on the row word. -/
theorem column_rowWord_injective (t : Tableau n μ) :
    Function.Injective (fun g : columnGroup t =>
      rowWord t ∘ (g : Equiv.Perm (Fin n))) := by
  intro g h he
  apply Subtype.ext
  apply Equiv.ext
  intro i
  apply t.injective
  apply Subtype.ext
  exact Prod.ext (congrArg Fin.val (congrFun he i))
    ((g.property i).trans (h.property i).symm)

/-- The unsigned summands in a polytabloid are distinct orthonormal vectors. -/
theorem polytabloid_summands_orthonormal (t : Tableau n μ) :
    Orthonormal ℝ (fun g : columnGroup t =>
      realCast n (μ.colLen 0)
        (wordRepInt n (μ.colLen 0) g (Pi.single (rowWord t) 1))) := by
  simp only [wordRepInt_single]
  exact realCast_single_orthonormal.comp _
    ((column_rowWord_injective t).comp (Equiv.inv (columnGroup t)).injective)

/-- The squared Hilbert norm of an integral polytabloid is its column-group order. -/
theorem norm_polytabloidInt_sq (t : Tableau n μ) :
    ‖realCast n (μ.colLen 0) (polytabloidInt t)‖ ^ 2 = Nat.card (columnGroup t) := by
  classical
  let := Fintype.ofFinite (columnGroup t)
  rw [← real_inner_self_eq_norm_sq]
  unfold polytabloidInt
  simp only [map_sum, map_smul, ← Int.cast_smul_eq_zsmul ℝ]
  rw [(polytabloid_summands_orthonormal t).inner_sum]
  have hs (g : columnGroup t) :
      (((Equiv.Perm.sign (g : Equiv.Perm (Fin n)) : ℤ) : ℝ)) *
        (((Equiv.Perm.sign (g : Equiv.Perm (Fin n)) : ℤ) : ℝ)) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  simp only [RCLike.conj_to_real, hs, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, Nat.card_eq_fintype_card]

/-- The coefficient square sum is an integer identity, so it transports to
bilinear coefficient pairings over every characteristic-zero field. -/
theorem sum_polytabloidInt_sq (t : Tableau n μ) :
    ∑ w, polytabloidInt t w ^ 2 = (Nat.card (columnGroup t) : ℤ) := by
  have h := norm_polytabloidInt_sq t
  rw [← real_inner_self_eq_norm_sq, inner_realCast] at h
  apply Int.cast_injective (α := ℝ)
  push_cast
  simpa only [pow_two] using h

end BostConjecture.Specht
