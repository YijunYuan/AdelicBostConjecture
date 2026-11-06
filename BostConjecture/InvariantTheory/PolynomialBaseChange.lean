module

public import BostConjecture.InvariantTheory.Coaction
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Scalar extension of intrinsic homogeneous polynomials

Matched bases identify the scalar-extended symmetric algebra of the dual
with the polynomial algebra of the extended vector space. The equivalence
preserves each homogeneous degree in both directions.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.InvariantTheory

open Module
open scoped TensorProduct

variable {K L X Y ι : Type*} [Field K] [Field L] [Algebra K L]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module L Y]
  [Fintype ι] [DecidableEq ι]

/-- Extension of polynomial coefficients in the coordinates of matched bases. -/
def polynomialBaseChangeEquiv (b : Basis ι K X) (c : Basis ι L Y) :
    L ⊗[K] SymmetricAlgebra K (Dual K X) ≃ₐ[L] SymmetricAlgebra L (Dual L Y) :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L)
    (SymmetricAlgebra.equivMvPolynomial b.dualBasis)).trans
      ((MvPolynomial.algebraTensorAlgEquiv K L).trans
        (SymmetricAlgebra.equivMvPolynomial c.dualBasis).symm)

@[simp]
theorem polynomialBaseChangeEquiv_tmul_ι (b : Basis ι K X) (c : Basis ι L Y)
    (l : L) (i : ι) :
    polynomialBaseChangeEquiv b c (l ⊗ₜ[K] SymmetricAlgebra.ι K _ (b.dualBasis i)) =
      l • SymmetricAlgebra.ι L _ (c.dualBasis i) := by
  change (SymmetricAlgebra.equivMvPolynomial c.dualBasis).symm
    (MvPolynomial.algebraTensorAlgEquiv K L
      (l ⊗ₜ[K] (SymmetricAlgebra.equivMvPolynomial b.dualBasis)
        (SymmetricAlgebra.ι K _ (b.dualBasis i)))) = _
  simp only [SymmetricAlgebra.equivMvPolynomial_ι_apply,
    MvPolynomial.algebraTensorAlgEquiv_tmul, MvPolynomial.map_X,
    map_smul, SymmetricAlgebra.equivMvPolynomial_symm_X]

@[simp]
theorem polynomialBaseChangeEquiv_symm_ι (b : Basis ι K X) (c : Basis ι L Y)
    (i : ι) :
    (polynomialBaseChangeEquiv b c).symm (SymmetricAlgebra.ι L _ (c.dualBasis i)) =
      1 ⊗ₜ[K] SymmetricAlgebra.ι K _ (b.dualBasis i) := by
  apply (polynomialBaseChangeEquiv b c).injective
  rw [AlgEquiv.apply_symm_apply, polynomialBaseChangeEquiv_tmul_ι, one_smul]

/-- Extension preserves the degree of products of linear forms. -/
theorem polynomialBaseChangeEquiv_tmul_mem_homogeneous
    (b : Basis ι K X) (c : Basis ι L Y) {d : ℕ}
    {p : SymmetricAlgebra K (Dual K X)} (hp : p ∈ homogeneousPolynomials K X d)
    (l : L) :
    polynomialBaseChangeEquiv b c (l ⊗ₜ[K] p) ∈ homogeneousPolynomials L Y d := by
  suffices h : polynomialBaseChangeEquiv b c (1 ⊗ₜ[K] p) ∈
      homogeneousPolynomials L Y d by
    simpa only [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one] using
      (homogeneousPolynomials L Y d).smul_mem l h
  induction hp using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    change (SymmetricAlgebra.equivMvPolynomial c.dualBasis).symm
      (MvPolynomial.algebraTensorAlgEquiv K L
        (1 ⊗ₜ[K] (SymmetricAlgebra.equivMvPolynomial b.dualBasis)
          (algebraMap K _ r))) ∈ homogeneousPolynomials L Y 0
    simp only [AlgEquiv.commutes, MvPolynomial.algebraTensorAlgEquiv_tmul,
      MvPolynomial.algebraMap_eq, MvPolynomial.map_C, one_smul]
    change (SymmetricAlgebra.equivMvPolynomial c.dualBasis).symm
      (algebraMap L _ (algebraMap K L r)) ∈ homogeneousPolynomials L Y 0
    rw [AlgEquiv.commutes]
    exact Submodule.algebraMap_mem _
  | add p q d hp hq ihp ihq =>
    simpa only [TensorProduct.tmul_add, map_add] using
      (homogeneousPolynomials L Y d).add_mem ihp ihq
  | mem_mul m hm d p hp ih =>
    obtain ⟨ℓ, rfl⟩ := hm
    have hℓ : polynomialBaseChangeEquiv b c (1 ⊗ₜ[K] SymmetricAlgebra.ι K _ ℓ) ∈
        homogeneousPolynomials L Y 1 := by
      rw [← b.dualBasis.sum_repr ℓ, map_sum, TensorProduct.tmul_sum, map_sum]
      apply Submodule.sum_mem
      intro i _
      rw [map_smul, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
        polynomialBaseChangeEquiv_tmul_ι]
      apply Submodule.smul_mem
      change _ ∈ (LinearMap.range (SymmetricAlgebra.ι L (Dual L Y))) ^ 1
      rw [pow_one]
      exact ⟨c.dualBasis i, rfl⟩
    have h := Submodule.mul_mem_mul hℓ ih
    simpa only [homogeneousPolynomials, pow_one, ← pow_succ',
      ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul] using h

theorem polynomialBaseChangeEquiv_mem_homogeneous
    (b : Basis ι K X) (c : Basis ι L Y) {d : ℕ}
    {z : L ⊗[K] SymmetricAlgebra K (Dual K X)}
    (hz : z ∈ (homogeneousPolynomials K X d).baseChange L) :
    polynomialBaseChangeEquiv b c z ∈ homogeneousPolynomials L Y d := by
  obtain ⟨z, rfl⟩ := hz
  induction z using TensorProduct.inductionOn with
  | add z w hz hw => simpa only [map_add] using
      (homogeneousPolynomials L Y d).add_mem hz hw
  | tmul l p =>
    exact polynomialBaseChangeEquiv_tmul_mem_homogeneous b c p.property l

/-- The inverse also preserves homogeneous degrees; surjectivity is not assumed. -/
theorem polynomialBaseChangeEquiv_symm_mem_baseChange
    (b : Basis ι K X) (c : Basis ι L Y) {d : ℕ}
    {p : SymmetricAlgebra L (Dual L Y)} (hp : p ∈ homogeneousPolynomials L Y d) :
    (polynomialBaseChangeEquiv b c).symm p ∈
      (homogeneousPolynomials K X d).baseChange L := by
  induction hp using Submodule.pow_induction_on_left' with
  | algebraMap l =>
    rw [AlgEquiv.commutes]
    exact Submodule.tmul_mem_baseChange_of_mem l (by simp [homogeneousPolynomials])
  | add p q d hp hq ihp ihq =>
    simpa only [map_add] using ((homogeneousPolynomials K X d).baseChange L).add_mem ihp ihq
  | mem_mul m hm d p hp ih =>
    obtain ⟨ℓ, rfl⟩ := hm
    have hℓ : (polynomialBaseChangeEquiv b c).symm (SymmetricAlgebra.ι L _ ℓ) ∈
        (homogeneousPolynomials K X 1).baseChange L := by
      rw [← c.dualBasis.sum_repr ℓ, map_sum, map_sum]
      apply Submodule.sum_mem
      intro i _
      rw [map_smul, map_smul, polynomialBaseChangeEquiv_symm_ι]
      apply Submodule.smul_mem
      apply Submodule.tmul_mem_baseChange_of_mem
      change _ ∈ (LinearMap.range (SymmetricAlgebra.ι K (Dual K X))) ^ 1
      rw [pow_one]
      exact ⟨b.dualBasis i, rfl⟩
    have h := mul_mem_baseChange hℓ ih
    simpa only [homogeneousPolynomials, pow_one, ← pow_succ', map_mul] using h

/-- The scalar extension of the existing degree subspace equals the degree
subspace of the extended polynomial algebra. -/
theorem polynomialBaseChangeEquiv_mem_homogeneous_iff
    (b : Basis ι K X) (c : Basis ι L Y) (d : ℕ)
    (z : L ⊗[K] SymmetricAlgebra K (Dual K X)) :
    polynomialBaseChangeEquiv b c z ∈ homogeneousPolynomials L Y d ↔
      z ∈ (homogeneousPolynomials K X d).baseChange L := by
  constructor
  · intro h
    simpa only [AlgEquiv.symm_apply_apply] using
      polynomialBaseChangeEquiv_symm_mem_baseChange b c h
  · exact polynomialBaseChangeEquiv_mem_homogeneous b c

end BostConjecture.InvariantTheory
