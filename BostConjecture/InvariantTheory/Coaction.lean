module

public import BostConjecture.InvariantTheory.PluckerCoordinates
public import BostConjecture.InvariantTheory.SpecialLinearCoordinates
public import BostConjecture.InvariantTheory.PolynomialAction
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Flat.Basic

/-!
# Coordinate pullback for the actual Plücker action

Polynomial coefficients lie in the determinant-one coordinate algebra. The
forward convention is evaluation at `(g,x)` equal to `p (ρ(g) x)`.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.InvariantTheory

open Module exteriorPower
open scoped TensorProduct

section MatrixPullback

variable {K A X τ : Type*} [Field K] [CommRing A] [Algebra K A]
  [AddCommGroup X] [Module K X] [Fintype τ] [DecidableEq τ]

/-- Specialize only the coefficients of an intrinsic polynomial. -/
def polynomialCoefficientEval (e : A →ₐ[K] K) :
    A ⊗[K] SymmetricAlgebra K (Dual K X) →ₐ[K] SymmetricAlgebra K (Dual K X) :=
  (Algebra.TensorProduct.lid K _).toAlgHom.comp
    (Algebra.TensorProduct.map e (AlgHom.id K _))

@[simp]
theorem polynomialCoefficientEval_tmul (e : A →ₐ[K] K) (a : A)
    (p : SymmetricAlgebra K (Dual K X)) :
    polynomialCoefficientEval e (a ⊗ₜ[K] p) = e a • p := by
  simp [polynomialCoefficientEval]

/-- Linear substitution with matrix entries in a coefficient algebra. -/
def matrixPolynomialPullback (b : Basis τ K X) (C : Matrix τ τ A) :
    SymmetricAlgebra K (Dual K X) →ₐ[K] A ⊗[K] SymmetricAlgebra K (Dual K X) :=
  SymmetricAlgebra.lift (b.dualBasis.constr K
    (fun i => ∑ j, C i j ⊗ₜ[K] SymmetricAlgebra.ι K _ (b.dualBasis j)))

@[simp]
theorem matrixPolynomialPullback_ι_dualBasis (b : Basis τ K X) (C : Matrix τ τ A)
    (i : τ) :
    matrixPolynomialPullback b C (SymmetricAlgebra.ι K _ (b.dualBasis i)) =
      ∑ j, C i j ⊗ₜ[K] SymmetricAlgebra.ι K _ (b.dualBasis j) := by
  simp only [matrixPolynomialPullback, SymmetricAlgebra.lift_ι_apply, Basis.constr_basis]

/-- Coefficient specialization recovers the intrinsic linear pullback. -/
theorem polynomialCoefficientEval_comp_matrixPolynomialPullback
    (b : Basis τ K X) (C : Matrix τ τ A) (e : A →ₐ[K] K) (f : X →ₗ[K] X)
    (hC : ∀ i j, e (C i j) = b.coord i (f (b j))) :
    (polynomialCoefficientEval e).comp (matrixPolynomialPullback b C) =
      polynomialPullback f := by
  apply SymmetricAlgebra.algHom_ext
  apply b.dualBasis.ext
  intro i
  change polynomialCoefficientEval e
    (matrixPolynomialPullback b C (SymmetricAlgebra.ι K _ (b.dualBasis i))) =
    polynomialPullback f (SymmetricAlgebra.ι K _ (b.dualBasis i))
  simp only [matrixPolynomialPullback_ι_dualBasis, map_sum, polynomialCoefficientEval_tmul,
    polynomialPullback_ι, ← map_smul]
  rw [← map_sum]
  congr 1
  apply b.ext
  intro j
  simp [hC, Basis.coord_apply, Finsupp.single_apply]

theorem mul_mem_baseChange {B : Type*} [CommRing B] [Algebra K B]
    {P Q : Submodule K B} {x y : A ⊗[K] B}
    (hx : x ∈ P.baseChange A) (hy : y ∈ Q.baseChange A) :
    x * y ∈ (P * Q).baseChange A := by
  obtain ⟨x, rfl⟩ := hx
  obtain ⟨y, rfl⟩ := hy
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simpa only [map_add, add_mul] using
      ((P * Q).baseChange A).add_mem hx hx'
  | tmul a p =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simpa only [map_add, mul_add] using
        ((P * Q).baseChange A).add_mem hy hy'
    | tmul a' q =>
      simp only [LinearMap.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul]
      exact Submodule.tmul_mem_baseChange_of_mem _ (Submodule.mul_mem_mul p.property q.property)

theorem matrixPolynomialPullback_ι_mem_baseChange (b : Basis τ K X) (C : Matrix τ τ A)
    (ℓ : Dual K X) :
    matrixPolynomialPullback b C (SymmetricAlgebra.ι K _ ℓ) ∈
      (homogeneousPolynomials K X 1).baseChange A := by
  rw [← b.dualBasis.sum_repr ℓ, map_sum, map_sum]
  apply Submodule.sum_mem
  intro i _
  rw [map_smul, map_smul]
  apply Submodule.smul_of_tower_mem
  rw [matrixPolynomialPullback_ι_dualBasis]
  apply Submodule.sum_mem
  intro j _
  apply Submodule.tmul_mem_baseChange_of_mem
  change _ ∈ (LinearMap.range (SymmetricAlgebra.ι K (Dual K X))) ^ 1
  rw [pow_one]
  exact ⟨b.dualBasis j, rfl⟩

/-- Linear substitution with arbitrary algebra coefficients preserves the homogeneous degree. -/
theorem matrixPolynomialPullback_mem_baseChange (b : Basis τ K X) (C : Matrix τ τ A)
    {d : ℕ} {p : SymmetricAlgebra K (Dual K X)}
    (hp : p ∈ homogeneousPolynomials K X d) :
    matrixPolynomialPullback b C p ∈ (homogeneousPolynomials K X d).baseChange A := by
  induction hp using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [AlgHom.commutes]
    change (algebraMap K A r) ⊗ₜ[K] (1 : SymmetricAlgebra K (Dual K X)) ∈ _
    apply Submodule.tmul_mem_baseChange_of_mem
    simp [homogeneousPolynomials]
  | add p q d hp hq ihp ihq =>
    simpa only [map_add] using ((homogeneousPolynomials K X d).baseChange A).add_mem ihp ihq
  | mem_mul m hm d p hp ih =>
    obtain ⟨ℓ, rfl⟩ := hm
    rw [map_mul]
    have h := mul_mem_baseChange (matrixPolynomialPullback_ι_mem_baseChange b C ℓ) ih
    simpa only [homogeneousPolynomials, pow_one, ← pow_succ'] using h

/-- The degree-restricted coefficient substitution, in the tensor product with
the existing homogeneous submodule. Flatness identifies this tensor product
with its image in the full polynomial algebra. -/
def homogeneousMatrixPolynomialPullback (b : Basis τ K X) (C : Matrix τ τ A) (d : ℕ) :
    homogeneousPolynomials K X d →ₗ[K] A ⊗[K] homogeneousPolynomials K X d := by
  let e := (Submodule.toBaseChange.toLinearEquiv A (homogeneousPolynomials K X d)).restrictScalars K
  exact e.symm.toLinearMap.comp
    (LinearMap.codRestrict ((homogeneousPolynomials K X d).baseChange A |>.restrictScalars K)
      ((matrixPolynomialPullback b C).toLinearMap.comp (homogeneousPolynomials K X d).subtype)
      (fun p => matrixPolynomialPullback_mem_baseChange b C p.property))

/-- Including the degree piece recovers the full coefficient substitution. -/
theorem homogeneousMatrixPolynomialPullback_include
    (b : Basis τ K X) (C : Matrix τ τ A) (d : ℕ) (p : homogeneousPolynomials K X d) :
    (homogeneousPolynomials K X d).subtype.baseChange A
      (homogeneousMatrixPolynomialPullback b C d p) = matrixPolynomialPullback b C p := by
  let e := Submodule.toBaseChange.toLinearEquiv A (homogeneousPolynomials K X d)
  exact congrArg Subtype.val (e.apply_symm_apply
    ⟨matrixPolynomialPullback b C p, matrixPolynomialPullback_mem_baseChange b C p.property⟩)

end MatrixPullback

section PluckerPullback

variable {K U W ι κ : Type*} [Field K]
  [AddCommGroup U] [Module K U] [AddCommGroup W] [Module K W]
  [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Coordinates of an intrinsic determinant-one automorphism in a supplied basis. -/
def specialLinearMatrix (b : Basis ι K U) (g : SpecialLinearGroup K U) :
    Matrix.SpecialLinearGroup ι K :=
  (Matrix.SpecialLinearGroup.toLin_equiv b).symm g

/-- Coordinate-algebra evaluation at the existing intrinsic group element. -/
def pluckerGroupEval (bU : Basis ι K U) (bW : Basis κ K W)
    (g : SpecialLinearGroup K U × SpecialLinearGroup K W) :
    SpecialLinearPairCoordinateRing K ι κ →ₐ[K] K :=
  specialLinearPairEval (specialLinearMatrix bU g.1, specialLinearMatrix bW g.2)

@[simp]
theorem pluckerGroupEval_mk (bU : Basis ι K U) (bW : Basis κ K W)
    (g : SpecialLinearGroup K U × SpecialLinearGroup K W)
    (p : MvPolynomial ((ι × ι) ⊕ (κ × κ)) K) :
    pluckerGroupEval bU bW g (Ideal.Quotient.mkₐ K (specialLinearPairIdeal K ι κ) p) =
      MvPolynomial.aeval
        (matrixPairEntries bU bW (g.1 : U →ₗ[K] U) (g.2 : W →ₗ[K] W)) p := by
  unfold pluckerGroupEval
  rw [specialLinearPairEval_mk]
  congr 2
  funext i
  cases i <;> simp [specialLinearMatrix,
    Matrix.SpecialLinearGroup.toLin_equiv.symm_toLinearMap_eq,
    matrixPairEntries, LinearMap.toMatrix_apply,
    Basis.coord_apply]

variable [LinearOrder (ι × κ)]

/-- The pullback of intrinsic polynomials along the actual algebraic Plücker action. -/
def pluckerCoordinatePullback (bU : Basis ι K U) (bW : Basis κ K W) (s : ℕ) :
    SymmetricAlgebra K (Dual K (⋀[K]^s (U ⊗[K] W))) →ₐ[K]
      SpecialLinearPairCoordinateRing K ι κ ⊗[K]
        SymmetricAlgebra K (Dual K (⋀[K]^s (U ⊗[K] W))) :=
  matrixPolynomialPullback ((bU.tensorProduct bW).exteriorPower s)
    (fun I J => Ideal.Quotient.mkₐ K (specialLinearPairIdeal K ι κ)
      (pluckerMatrixPolynomial (K := K) s I J))

/-- Specialization of the coefficient ring is exactly forward pullback by the actual action. -/
theorem polynomialCoefficientEval_comp_pluckerCoordinatePullback
    (bU : Basis ι K U) (bW : Basis κ K W) (s : ℕ)
    (g : SpecialLinearGroup K U × SpecialLinearGroup K W) :
    (polynomialCoefficientEval (pluckerGroupEval bU bW g)).comp
      (pluckerCoordinatePullback bU bW s) =
        polynomialPullback (pluckerRepresentation K U W s g) := by
  apply polynomialCoefficientEval_comp_matrixPolynomialPullback
  intro I J
  rw [pluckerGroupEval_mk, aeval_pluckerMatrixPolynomial]
  rfl

@[simp]
theorem polynomialCoefficientEval_pluckerCoordinatePullback
    (bU : Basis ι K U) (bW : Basis κ K W) (s : ℕ)
    (g : SpecialLinearGroup K U × SpecialLinearGroup K W)
    (p : SymmetricAlgebra K (Dual K (⋀[K]^s (U ⊗[K] W)))) :
    polynomialCoefficientEval (pluckerGroupEval bU bW g) (pluckerCoordinatePullback bU bW s p) =
      polynomialPullback (pluckerRepresentation K U W s g) p :=
  DFunLike.congr_fun (polynomialCoefficientEval_comp_pluckerCoordinatePullback bU bW s g) p

/-- Joint evaluation has the required forward coaction convention. -/
theorem polynomialEval_pluckerCoordinatePullback
    (bU : Basis ι K U) (bW : Basis κ K W) (s : ℕ)
    (g : SpecialLinearGroup K U × SpecialLinearGroup K W)
    (p : SymmetricAlgebra K (Dual K (⋀[K]^s (U ⊗[K] W))))
    (z : ⋀[K]^s (U ⊗[K] W)) :
    polynomialEval z (polynomialCoefficientEval (pluckerGroupEval bU bW g)
      (pluckerCoordinatePullback bU bW s p)) =
        polynomialEval (pluckerRepresentation K U W s g z) p := by
  rw [polynomialCoefficientEval_pluckerCoordinatePullback, polynomialEval_pullback]

/-- The actual forward coordinate map on one homogeneous degree. -/
def pluckerPolynomialCoaction (bU : Basis ι K U) (bW : Basis κ K W) (s d : ℕ) :
    homogeneousPolynomials K (⋀[K]^s (U ⊗[K] W)) d →ₗ[K]
      SpecialLinearPairCoordinateRing K ι κ ⊗[K]
        homogeneousPolynomials K (⋀[K]^s (U ⊗[K] W)) d :=
  homogeneousMatrixPolynomialPullback ((bU.tensorProduct bW).exteriorPower s)
    (fun I J => Ideal.Quotient.mkₐ K (specialLinearPairIdeal K ι κ)
      (pluckerMatrixPolynomial (K := K) s I J)) d

theorem pluckerPolynomialCoaction_include
    (bU : Basis ι K U) (bW : Basis κ K W) (s d : ℕ)
    (p : homogeneousPolynomials K (⋀[K]^s (U ⊗[K] W)) d) :
    (homogeneousPolynomials K (⋀[K]^s (U ⊗[K] W)) d).subtype.baseChange
        (SpecialLinearPairCoordinateRing K ι κ) (pluckerPolynomialCoaction bU bW s d p) =
      pluckerCoordinatePullback bU bW s p :=
  homogeneousMatrixPolynomialPullback_include _ _ _ _

/-- Evaluation of the degree coordinate map is the agreed intrinsic forward pullback. -/
theorem polynomialCoefficientEval_pluckerPolynomialCoaction
    (bU : Basis ι K U) (bW : Basis κ K W) (s d : ℕ)
    (g : SpecialLinearGroup K U × SpecialLinearGroup K W)
    (p : homogeneousPolynomials K (⋀[K]^s (U ⊗[K] W)) d) :
    polynomialCoefficientEval (pluckerGroupEval bU bW g)
      ((homogeneousPolynomials K (⋀[K]^s (U ⊗[K] W)) d).subtype.baseChange
        (SpecialLinearPairCoordinateRing K ι κ) (pluckerPolynomialCoaction bU bW s d p)) =
      polynomialPullback (pluckerRepresentation K U W s g) p := by
  rw [pluckerPolynomialCoaction_include, polynomialCoefficientEval_pluckerCoordinatePullback]

/-- A coefficientwise fixed polynomial is an invariant of the existing representation.
The converse requires rational-point detection and is not asserted here. -/
theorem mem_homogeneousInvariants_of_pluckerPolynomialCoaction_eq
    (bU : Basis ι K U) (bW : Basis κ K W) (s d : ℕ)
    (p : homogeneousPolynomials K (⋀[K]^s (U ⊗[K] W)) d)
    (hp : pluckerPolynomialCoaction bU bW s d p =
      (1 : SpecialLinearPairCoordinateRing K ι κ) ⊗ₜ[K] p) :
    (p : SymmetricAlgebra K (Dual K (⋀[K]^s (U ⊗[K] W)))) ∈
      homogeneousInvariants (pluckerRepresentation K U W s) d := by
  apply (mem_homogeneousInvariants_iff _ _ _).mpr
  refine ⟨p.property, fun g => ?_⟩
  have h := polynomialCoefficientEval_pluckerPolynomialCoaction bU bW s d g p
  have he := congrArg (fun q => polynomialCoefficientEval (pluckerGroupEval bU bW g)
    ((homogeneousPolynomials K (⋀[K]^s (U ⊗[K] W)) d).subtype.baseChange
      (SpecialLinearPairCoordinateRing K ι κ) q)) hp
  exact h.symm.trans (he.trans (by simp))

end PluckerPullback

end BostConjecture.InvariantTheory
