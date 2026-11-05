module

public import BostConjecture.InvariantTheory.PluckerAction
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Polynomial matrix coefficients of the Plücker action

Tensor matrix entries are products of entries of the two factors. Exterior
matrix entries are minors of that tensor matrix. Evaluation is proved equal
to the existing intrinsic tensor/exterior action, including arbitrary vectors.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.InvariantTheory

open Module exteriorPower
open scoped TensorProduct

variable {K U W ι κ : Type*} [Field K]
  [AddCommGroup U] [Module K U] [AddCommGroup W] [Module K W]

/-- The universal tensor matrix, in the entries of its two factors. -/
def tensorMatrixPolynomial (K : Type*) [CommRing K] (ι κ : Type*)
    (a b : ι × κ) : MvPolynomial ((ι × ι) ⊕ (κ × κ)) K :=
  MvPolynomial.X (Sum.inl (a.1, b.1)) * MvPolynomial.X (Sum.inr (a.2, b.2))

/-- Matrix-entry substitution associated to two actual endomorphisms. -/
def matrixPairEntries (bU : Basis ι K U) (bW : Basis κ K W)
    (f : U →ₗ[K] U) (g : W →ₗ[K] W) : ((ι × ι) ⊕ (κ × κ)) → K :=
  Sum.elim (fun ij => bU.coord ij.1 (f (bU ij.2)))
    (fun ij => bW.coord ij.1 (g (bW ij.2)))

@[simp]
theorem aeval_tensorMatrixPolynomial (bU : Basis ι K U) (bW : Basis κ K W)
    (f : U →ₗ[K] U) (g : W →ₗ[K] W) (a b : ι × κ) :
    MvPolynomial.aeval (matrixPairEntries bU bW f g) (tensorMatrixPolynomial K ι κ a b) =
      (bU.tensorProduct bW).coord a
        (TensorProduct.map f g ((bU.tensorProduct bW) b)) := by
  rcases a with ⟨i, j⟩
  rcases b with ⟨k, l⟩
  simp [tensorMatrixPolynomial, matrixPairEntries, Basis.coord_apply, mul_comm]

variable [LinearOrder (ι × κ)]

/-- Exterior matrix coefficients are minors of the universal tensor matrix.
The determinant is transposed to match Mathlib's exterior-coordinate formula. -/
def pluckerMatrixPolynomial (s : ℕ) (I J : Set.powersetCard (ι × κ) s) :
    MvPolynomial ((ι × ι) ⊕ (κ × κ)) K :=
  (Matrix.of fun i j : Fin s => tensorMatrixPolynomial K ι κ
    (Set.powersetCard.ofFinEmbEquiv.symm I j)
    (Set.powersetCard.ofFinEmbEquiv.symm J i)).det

/-- Evaluating the explicit minor gives the actual exterior matrix coefficient. -/
theorem aeval_pluckerMatrixPolynomial (bU : Basis ι K U) (bW : Basis κ K W)
    (f : U →ₗ[K] U) (g : W →ₗ[K] W) (s : ℕ)
    (I J : Set.powersetCard (ι × κ) s) :
    MvPolynomial.aeval (matrixPairEntries bU bW f g)
        (pluckerMatrixPolynomial (K := K) s I J) =
      ((bU.tensorProduct bW).exteriorPower s).coord I
        (exteriorPower.map s (TensorProduct.map f g)
          (((bU.tensorProduct bW).exteriorPower s) J)) := by
  rw [basis_coord, basis_apply, ιMulti_family, map_apply_ιMulti,
    ιMultiDual_apply_ιMulti]
  unfold pluckerMatrixPolynomial
  rw [← AlgHom.coe_toRingHom, RingHom.map_det]
  congr 1
  ext i j
  exact aeval_tensorMatrixPolynomial bU bW f g _ _

variable [Fintype ι] [Fintype κ]

/-- The coordinate polynomials of the orbit map of an arbitrary exterior vector. -/
def pluckerOrbitPolynomial (bU : Basis ι K U) (bW : Basis κ K W) (s : ℕ)
    (z : ⋀[K]^s (U ⊗[K] W)) (I : Set.powersetCard (ι × κ) s) :
    MvPolynomial ((ι × ι) ⊕ (κ × κ)) K :=
  ∑ J, MvPolynomial.C (((bU.tensorProduct bW).exteriorPower s).repr z J) *
    pluckerMatrixPolynomial (K := K) s I J

/-- Every coordinate of the intrinsic orbit map is the displayed polynomial. -/
theorem aeval_pluckerOrbitPolynomial (bU : Basis ι K U) (bW : Basis κ K W) (s : ℕ)
    (z : ⋀[K]^s (U ⊗[K] W)) (f : U →ₗ[K] U) (g : W →ₗ[K] W)
    (I : Set.powersetCard (ι × κ) s) :
    MvPolynomial.aeval (matrixPairEntries bU bW f g) (pluckerOrbitPolynomial bU bW s z I) =
      ((bU.tensorProduct bW).exteriorPower s).coord I
        (exteriorPower.map s (TensorProduct.map f g) z) := by
  classical
  conv_rhs => rw [← ((bU.tensorProduct bW).exteriorPower s).sum_repr z]
  simp only [pluckerOrbitPolynomial, map_sum, map_mul, MvPolynomial.aeval_C,
    Algebra.algebraMap_self, RingHom.id_apply, aeval_pluckerMatrixPolynomial,
    map_smul, smul_eq_mul]

/-- Polynomiality specializes to the existing special-linear Plücker representation. -/
theorem aeval_pluckerOrbitPolynomial_specialLinear
    (bU : Basis ι K U) (bW : Basis κ K W) (s : ℕ)
    (z : ⋀[K]^s (U ⊗[K] W))
    (g : SpecialLinearGroup K U × SpecialLinearGroup K W)
    (I : Set.powersetCard (ι × κ) s) :
    MvPolynomial.aeval (matrixPairEntries bU bW (g.1 : U →ₗ[K] U) (g.2 : W →ₗ[K] W))
        (pluckerOrbitPolynomial bU bW s z I) =
      ((bU.tensorProduct bW).exteriorPower s).coord I (pluckerRepresentation K U W s g z) :=
  aeval_pluckerOrbitPolynomial bU bW s z _ _ I

end BostConjecture.InvariantTheory
