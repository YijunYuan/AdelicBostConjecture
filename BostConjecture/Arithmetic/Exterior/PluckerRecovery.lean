/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Geometry.Determinant.Coordinates

/-!
# Recovering a subspace from a nonzero determinant vector

Multiplication by a vector in the exterior algebra annihilates a nonzero
top wedge exactly when that vector belongs to the original subspace.
-/

@[expose] public section

noncomputable section

open Module exteriorPower

namespace BostConjecture.Arithmetic

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] {r : ℕ}

/-- A wedge is nonzero exactly when its factors are linearly independent. -/
lemma ιMulti_ne_zero_iff {v : Fin r → V} :
    ιMulti k r v ≠ 0 ↔ LinearIndependent k v := by
  constructor
  · intro h
    by_contra hn
    exact h ((ιMulti k r).map_linearDependent v hn)
  · intro hv
    let P := Submodule.span k (Set.range v)
    let b := Basis.span hv
    have hb : ιMulti k r b ≠ 0 := by
      intro he
      have hc := congrArg (Geometry.determinantCoordinates b) he
      simp only [Geometry.determinantCoordinates_ιMulti, Basis.det_self, map_zero,
        one_ne_zero] at hc
    have hm : map r P.subtype (ιMulti k r b) = ιMulti k r v := by
      rw [map_apply_ιMulti]
      congr 1
      funext i
      exact Basis.coe_span_apply hv i
    rw [← hm]
    simpa only [map_zero] using (map_injective_field (n := r) P.injective_subtype).ne hb

/-- The same criterion inside the exterior algebra. -/
lemma exteriorAlgebra_ιMulti_ne_zero_iff {v : Fin r → V} :
    ExteriorAlgebra.ιMulti k r v ≠ 0 ↔ LinearIndependent k v := by
  have he : ExteriorAlgebra.ιMulti k r v = ((ιMulti k r v : ⋀[k]^r V) : ExteriorAlgebra k V) := rfl
  rw [he, ← ιMulti_ne_zero_iff]
  exact not_congr ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

/-- A nonzero top exterior vector recovers its subspace by annihilation. -/
theorem mem_iff_mul_plucker_eq_zero (W : Submodule k V) (b : Basis (Fin r) k W)
    (η : ⋀[k]^r W) (hη : η ≠ 0) (x : V) :
    x ∈ W ↔ ExteriorAlgebra.ι k x * (map r W.subtype η : ExteriorAlgebra k V) = 0 := by
  let v : Fin r → V := W.subtype ∘ b
  have hv : LinearIndependent k v := b.linearIndependent.map' _ W.ker_subtype
  have hspan : Submodule.span k (Set.range v) = W := by
    change Submodule.span k (Set.range (W.subtype ∘ b)) = W
    rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  obtain ⟨a, rfl⟩ := (Geometry.determinantCoordinates b).symm.surjective η
  have ha : a ≠ 0 := fun he => hη (by simp [he])
  have he : (map r W.subtype ((Geometry.determinantCoordinates b).symm a) :
      ExteriorAlgebra k V) = a • ExteriorAlgebra.ιMulti k r v := by
    simp only [Geometry.determinantCoordinates_symm_apply, map_smul, map_apply_ιMulti]
    rfl
  rw [he, mul_smul_comm, smul_eq_zero, or_iff_right ha]
  have hc : ExteriorAlgebra.ι k x * ExteriorAlgebra.ιMulti k r v =
      ExteriorAlgebra.ιMulti k (r + 1) (Fin.cons x v) := by
    simp [ExteriorAlgebra.ιMulti_succ_apply, Matrix.vecTail]
  rw [hc, ← not_iff_not]
  change x ∉ W ↔ ExteriorAlgebra.ιMulti k (r + 1) (Fin.cons x v) ≠ 0
  rw [exteriorAlgebra_ιMulti_ne_zero_iff, linearIndependent_finCons,
    and_iff_right hv, hspan]

/-- Equality of nonzero determinant images forces equality of their subspaces. -/
theorem eq_of_plucker_eq (U W : Submodule k V)
    (b : Basis (Fin r) k U) (c : Basis (Fin r) k W)
    (η : ⋀[k]^r U) (ζ : ⋀[k]^r W) (hη : η ≠ 0) (hζ : ζ ≠ 0)
    (he : map r U.subtype η = map r W.subtype ζ) : U = W := by
  ext x
  rw [mem_iff_mul_plucker_eq_zero U b η hη,
    mem_iff_mul_plucker_eq_zero W c ζ hζ, he]

end BostConjecture.Arithmetic
