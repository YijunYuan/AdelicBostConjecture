/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Compactness.Action.TraceMultiplication
public import BostConjecture.Arithmetic.Compactness.Action.IntegralMatrices

/-!
# Finitely many actual integral multiplication matrices

The finite set depends only on the number field element and the compact set
of real frames. Every actual Hermitian metric and every integral basis whose
orthonormal coordinate frame belongs to that compact set gives a matrix in it.
No choice of a free basis over the ring of integers is required.

Reference: this paper, page 11, Lemma 7.1.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct Matrix

namespace BostConjecture.Arithmetic.Compactness

variable {K : Type*} [Field K] [NumberField K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A universal finite set of possible matrices for multiplication by `a`.
Its definition is independent of the module and the metric. -/
theorem finite_actual_integral_actions (a : 𝓞 K)
    {S : Set (GeneralLinearGroup ι ℝ)} (hS : IsCompact S) :
    {N : Matrix ι ι ℤ | ∃ B ∈ S, ∀ i j,
      |(B.val * N.map (Int.castRingHom ℝ) * (B⁻¹).val) i j| ≤
        ∑ σ : K →+* ℂ, ‖σ a‖}.Finite :=
  finite_bounded_integral_conjugates hS _

variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]
variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]

/-- Every actual integral multiplication matrix lies in the universal finite
set when its lattice frame lies in the prescribed compact family. -/
theorem integral_action_mem (h : HermitianMetric K M) (a : 𝓞 K)
    (b : Module.Basis ι ℤ M) (b₀ : OrthonormalBasis ι ℝ h.TraceSpace)
    {S : Set (GeneralLinearGroup ι ℝ)} (B : GeneralLinearGroup ι ℝ)
    (hBS : B ∈ S) (hB : B.val = b₀.toBasis.toMatrix (h.traceBasis b)) :
    LinearMap.toMatrix b b (Algebra.lsmul ℤ ℤ M a) ∈
      {N : Matrix ι ι ℤ | ∃ B ∈ S, ∀ i j,
        |(B.val * N.map (Int.castRingHom ℝ) * (B⁻¹).val) i j| ≤
          ∑ σ : K →+* ℂ, ‖σ a‖} := by
  refine ⟨B, hBS, ?_⟩
  rw [h.traceMul_matrix_conjugate a b b₀.toBasis B hB]
  exact h.traceMul_toMatrix_abs_le a b₀ (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    (fun σ => Finset.single_le_sum (fun τ _ => norm_nonneg (τ a)) (Finset.mem_univ σ))

end BostConjecture.Arithmetic.Compactness
