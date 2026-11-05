module

public import BostConjecture.Balanced.SpectralExpansion
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.LinearAlgebra.Determinant

/-! # Determinants of Hermitian exponentials -/

@[expose] public section

noncomputable section

namespace BostConjecture.Balanced

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

omit [FiniteDimensional ℂ E] in
theorem det_eq_prod_of_basis {ι : Type*} [Fintype ι] (b : Module.Basis ι ℂ E)
    (A : Module.End ℂ E) (a : ι → ℂ) (ha : ∀ i, A (b i) = a i • b i) :
    LinearMap.det A = ∏ i, a i := by
  classical
  rw [← LinearMap.det_toMatrix b]
  have hm : LinearMap.toMatrix b b A = Matrix.diagonal a := by
    ext i j
    by_cases h : i = j <;> simp [LinearMap.toMatrix_apply, ha, h]
  rw [hm, Matrix.det_diagonal]

/-- A Hermitian exponential has positive real determinant, equal to the exponential of its trace. -/
theorem det_exp_of_isSymmetric (A : Module.End ℂ E) (hA : A.IsSymmetric) :
    LinearMap.det (NormedSpace.exp (LinearMap.toContinuousLinearMap A)).toLinearMap =
      (Real.exp (LinearMap.trace ℂ E A).re : ℂ) := by
  rw [det_eq_prod_of_basis (hA.eigenvectorBasis rfl).toBasis _
    (fun i => (Real.exp (hA.eigenvalues rfl i) : ℂ))]
  · rw [hA.trace_eq_sum_eigenvalues rfl]
    simp [Real.exp_sum]
  · intro i
    simpa using exp_real_smul_apply_of_apply_eq_smul (LinearMap.toContinuousLinearMap A)
      (hA.eigenvectorBasis rfl i) (hA.eigenvalues rfl i) 1 (hA.apply_eigenvectorBasis rfl i)

/-- A Hermitian generator with determinant-one exponential has trace zero. -/
theorem trace_eq_zero_of_det_exp_eq_one (A : Module.End ℂ E) (hA : A.IsSymmetric)
    (hdet : LinearMap.det (NormedSpace.exp (LinearMap.toContinuousLinearMap A)).toLinearMap = 1) :
    LinearMap.trace ℂ E A = 0 := by
  rw [det_exp_of_isSymmetric A hA] at hdet
  have hre : (LinearMap.trace ℂ E A).re = 0 := by
    apply (Real.exp_eq_one_iff _).mp
    exact_mod_cast hdet
  rw [hA.trace_eq_sum_eigenvalues rfl] at hre ⊢
  have hs : ∑ i, hA.eigenvalues rfl i = 0 := by simpa using hre
  simp [hs]

end BostConjecture.Balanced
