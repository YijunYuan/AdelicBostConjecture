module

public import BostConjecture.Arithmetic.ExteriorProduct
public import BostConjecture.Geometry.DeterminantCoordinates
public import Mathlib.LinearAlgebra.Basis.Prod

/-!
# Determinants of products

The canonical exterior product sends the tensor of two determinant generators
to the determinant generator of the concatenated basis. This proves the local
free calculation needed for the integral projective determinant isomorphism.
-/

@[expose] public section

noncomputable section

open Module TensorProduct

namespace exteriorPower

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {a b : ℕ}

lemma prodBasis_reindex (p : Basis (Fin a) R M) (q : Basis (Fin b) R N) :
    Fin.append (fun i => (p i, 0)) (fun j => (0, q j)) =
      (p.prod q).reindex finSumFinEquiv := by
  funext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;> simp

/-- The top exterior product multiplies the two determinant coordinates. -/
lemma prodMap_coordinates (p : Basis (Fin a) R M) (q : Basis (Fin b) R N)
    (x : ⋀[R]^a M) (y : ⋀[R]^b N) :
    BostConjecture.Geometry.determinantCoordinates ((p.prod q).reindex finSumFinEquiv)
        (prodMap R M N a b (x ⊗ₜ[R] y)) =
      BostConjecture.Geometry.determinantCoordinates p x *
        BostConjecture.Geometry.determinantCoordinates q y := by
  obtain ⟨r, rfl⟩ := (BostConjecture.Geometry.determinantCoordinates p).symm.surjective x
  obtain ⟨s, rfl⟩ := (BostConjecture.Geometry.determinantCoordinates q).symm.surjective y
  simp only [BostConjecture.Geometry.determinantCoordinates_symm_apply,
    smul_tmul, tmul_smul, map_smul, prodMap_ιMulti, prodBasis_reindex,
    BostConjecture.Geometry.determinantCoordinates_ιMulti, Basis.det_self,
    smul_eq_mul, mul_one]
  exact mul_comm s r

/-- The canonical determinant product is an isomorphism in every finite free frame. -/
lemma prodMap_bijective_of_basis (p : Basis (Fin a) R M) (q : Basis (Fin b) R N) :
    Function.Bijective (prodMap R M N a b) := by
  let d := BostConjecture.Geometry.determinantCoordinates ((p.prod q).reindex finSumFinEquiv)
  let e := (TensorProduct.congr (BostConjecture.Geometry.determinantCoordinates p)
    (BostConjecture.Geometry.determinantCoordinates q)) ≪≫ₗ
      TensorProduct.lid R R ≪≫ₗ d.symm
  have he : prodMap R M N a b = e.toLinearMap := by
    apply TensorProduct.ext'
    intro x y
    apply d.injective
    change d (prodMap R M N a b (x ⊗ₜ[R] y)) =
      d (d.symm (BostConjecture.Geometry.determinantCoordinates p x *
        BostConjecture.Geometry.determinantCoordinates q y))
    rw [LinearEquiv.apply_symm_apply]
    exact prodMap_coordinates p q x y
  rw [he]
  exact e.bijective

end exteriorPower
