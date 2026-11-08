/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Geometry.Determinant.Coordinates

/-!
# Shears on the determinant of a product

Adding a linear function of the second summand to the first acts trivially
on the top exterior power. This is the section-independence calculation
for the determinant of an exact sequence.
-/

@[expose] public section

noncomputable section

open Module

namespace exteriorPower

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {a b : ℕ}

/-- The upper triangular shear attached to a map between the summands. -/
def upperShear (t : N →ₗ[R] M) : (M × N) →ₗ[R] (M × N) :=
  (LinearMap.fst R M N + t.comp (LinearMap.snd R M N)).prod (LinearMap.snd R M N)

@[simp]
lemma upperShear_apply (t : N →ₗ[R] M) (x : M × N) :
    upperShear t x = (x.1 + t x.2, x.2) := rfl

/-- The determinant of a shear is one in a concatenated finite basis. -/
lemma prodBasis_det_upperShear (p : Basis (Fin a) R M) (q : Basis (Fin b) R N)
    (t : N →ₗ[R] M) :
    ((p.prod q).reindex finSumFinEquiv).det
      (upperShear t ∘ ((p.prod q).reindex finSumFinEquiv)) = 1 := by
  classical
  rw [Basis.det_reindex]
  have hv : (upperShear t ∘ ((p.prod q).reindex finSumFinEquiv)) ∘ finSumFinEquiv =
      upperShear t ∘ (p.prod q) := by
    funext i
    simp
  rw [hv, Basis.det_apply]
  have hm : (p.prod q).toMatrix (upperShear t ∘ (p.prod q)) =
      Matrix.fromBlocks 1 (LinearMap.toMatrix q p t) 0 1 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Basis.toMatrix_apply, LinearMap.toMatrix_apply, Matrix.one_apply,
        Finsupp.single_apply, eq_comm]
  rw [hm, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, Matrix.det_one, one_mul]

/-- The top exterior power of a shear is the identity, including zero ranks. -/
lemma map_upperShear_top_of_basis (p : Basis (Fin a) R M) (q : Basis (Fin b) R N)
    (t : N →ₗ[R] M) (x : ⋀[R]^(a + b) (M × N)) :
    map (a + b) (upperShear t) x = x := by
  let d := BostConjecture.Geometry.determinantCoordinates ((p.prod q).reindex finSumFinEquiv)
  obtain ⟨r, rfl⟩ := d.symm.surjective x
  apply d.injective
  simp only [d, BostConjecture.Geometry.determinantCoordinates_symm_apply, map_smul,
    map_apply_ιMulti, BostConjecture.Geometry.determinantCoordinates_ιMulti,
    prodBasis_det_upperShear, Basis.det_self]

end exteriorPower
