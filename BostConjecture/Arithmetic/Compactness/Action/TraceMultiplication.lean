/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Compactness.Topology.MetricTopology
public import BostConjecture.Arithmetic.RestrictionCovolume.TraceSpace

/-!
# Arithmetic multiplication on the actual real trace space

The canonical real tensor equivalence transports integral multiplication to
the trace space. Its archimedean action is scalar multiplication in each
actual fiber, giving an operator bound independent of the Hermitian metric.

Reference: this paper, page 11, Lemma 7.1.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace BostConjecture.Arithmetic.HermitianMetric

variable {K : Type*} [Field K] [NumberField K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]
variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]

/-- Actual integral multiplication extended to the trace space through the
canonical real scalar-extension equivalence. -/
def traceMul (h : HermitianMetric K M) (a : 𝓞 K) :
    h.TraceSpace →ₗ[ℝ] h.TraceSpace :=
  h.realTensorEquiv.toLinearMap.comp
    (((Algebra.lsmul ℤ ℤ M a).baseChange ℝ).comp h.realTensorEquiv.symm.toLinearMap)

@[simp]
lemma traceMul_realTensorEquiv (h : HermitianMetric K M) (a : 𝓞 K)
    (r : ℝ) (x : M) :
    h.traceMul a (h.realTensorEquiv (r ⊗ₜ[ℤ] x)) =
      h.realTensorEquiv (r ⊗ₜ[ℤ] (a • x)) := by
  change h.realTensorEquiv (((Algebra.lsmul ℤ ℤ M a).baseChange ℝ)
    (h.realTensorEquiv.symm (h.realTensorEquiv (r ⊗ₜ[ℤ] x)))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

@[simp]
lemma traceMul_section (h : HermitianMetric K M) (a : 𝓞 K) (x : M) :
    h.traceMul a (h.traceSection x) = h.traceSection (a • x) := by
  simpa only [realTensorEquiv_tmul, one_smul] using h.traceMul_realTensorEquiv a 1 x

/-- The real extension preserves the actual integral lattice. -/
lemma traceMul_mem_traceLattice (h : HermitianMetric K M) (a : 𝓞 K)
    {z : h.TraceSpace} (hz : z ∈ h.traceLattice) : h.traceMul a z ∈ h.traceLattice := by
  obtain ⟨x, rfl⟩ := hz
  exact ⟨a • x, (h.traceMul_section a x).symm⟩

/-- The transported action has the prescribed scalar action in each actual fiber. -/
lemma traceInclusion_traceMul (h : HermitianMetric K M) (a : 𝓞 K)
    (z : h.TraceSpace) (σ : K →+* ℂ) :
    h.traceInclusion (h.traceMul a z) σ = σ a • h.traceInclusion z σ := by
  obtain ⟨w, rfl⟩ := h.realTensorEquiv.surjective z
  induction w using TensorProduct.inductionOn with
  | tmul r x =>
    simp only [realTensorEquiv_tmul, map_smul, traceMul_section,
      Pi.smul_apply, traceInclusion_section, fiberSection_smul]
    exact smul_comm r (σ a) (fiberSection M σ x)
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy, smul_add]

omit [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M] in
/-- The actual trace norm is the sum of the actual squared fiber norms. -/
lemma trace_norm_sq (h : HermitianMetric K M) (z : h.TraceSpace) :
    ‖z‖ ^ 2 = ∑ σ : K →+* ℂ, h.fiberNorm σ (h.traceInclusion z σ) ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℝ)]
  change (∑ σ : K →+* ℂ, ((h.fiber σ).inner
    (h.traceInclusion z σ) (h.traceInclusion z σ)).re) = _
  apply Finset.sum_congr rfl
  intro σ _
  exact (Real.sq_sqrt ((h.fiber σ).re_inner_nonneg _)).symm

/-- The action bound is independent of the metric: any simultaneous bound on
the archimedean absolute values bounds multiplication on trace space. -/
theorem traceMul_norm_le (h : HermitianMetric K M) (a : 𝓞 K)
    {C : ℝ} (hC : 0 ≤ C) (ha : ∀ σ : K →+* ℂ, ‖σ a‖ ≤ C) (z : h.TraceSpace) :
    ‖h.traceMul a z‖ ≤ C * ‖z‖ := by
  have hb : ‖h.traceMul a z‖ ^ 2 ≤ C ^ 2 * ‖z‖ ^ 2 := by
    rw [h.trace_norm_sq, h.trace_norm_sq, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro σ _
    rw [traceInclusion_traceMul, fiberNorm_smul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (ha σ) 2)
      (sq_nonneg _)
  nlinarith [norm_nonneg (h.traceMul a z), norm_nonneg z,
    mul_nonneg hC (norm_nonneg z)]

variable {ι : Type*}

@[simp]
lemma traceBasis_repr_section (h : HermitianMetric K M)
    (b : Module.Basis ι ℤ M) (x : M) (i : ι) :
    (h.traceBasis b).repr (h.traceSection x) i = (b.repr x i : ℝ) := by
  change ((b.map h.traceLatticeEquiv).ofZLatticeBasis ℝ h.traceLattice).repr
    (h.traceLatticeEquiv x).val i = _
  rw [Module.Basis.ofZLatticeBasis_repr_apply]
  simp

variable [Fintype ι] [DecidableEq ι]

/-- The integral multiplication matrix really is the matrix of trace
multiplication after extension to the reals. -/
theorem traceMul_toMatrix (h : HermitianMetric K M) (a : 𝓞 K)
    (b : Module.Basis ι ℤ M) :
    LinearMap.toMatrix (h.traceBasis b) (h.traceBasis b) (h.traceMul a) =
      (LinearMap.toMatrix b b (Algebra.lsmul ℤ ℤ M a)).map (Int.castRingHom ℝ) := by
  ext i j
  simp only [LinearMap.toMatrix_apply, traceBasis_apply, traceMul_section,
    traceBasis_repr_section, Matrix.map_apply, Algebra.lsmul_apply]
  rfl

/-- Changing from an actual integral frame to an ambient real frame conjugates
the multiplication matrix in the expected direction. -/
theorem traceMul_matrix_conjugate (h : HermitianMetric K M) (a : 𝓞 K)
    (b : Module.Basis ι ℤ M) (b₀ : Module.Basis ι ℝ h.TraceSpace)
    (B : Matrix.GeneralLinearGroup ι ℝ) (hB : B.val = b₀.toMatrix (h.traceBasis b)) :
    B.val * (LinearMap.toMatrix b b (Algebra.lsmul ℤ ℤ M a)).map (Int.castRingHom ℝ) *
      (B⁻¹).val = LinearMap.toMatrix b₀ b₀ (h.traceMul a) := by
  rw [← h.traceMul_toMatrix]
  have he : B.val * LinearMap.toMatrix (h.traceBasis b) (h.traceBasis b) (h.traceMul a) =
      LinearMap.toMatrix b₀ b₀ (h.traceMul a) * B.val := by
    rw [hB, basis_toMatrix_mul_linearMap_toMatrix, linearMap_toMatrix_mul_basis_toMatrix]
  rw [he, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]

/-- In an orthonormal real frame the entries of multiplication are bounded
by the same metric-independent archimedean bound. -/
theorem traceMul_toMatrix_abs_le (h : HermitianMetric K M) (a : 𝓞 K)
    (b₀ : OrthonormalBasis ι ℝ h.TraceSpace) {C : ℝ}
    (hC : 0 ≤ C) (ha : ∀ σ : K →+* ℂ, ‖σ a‖ ≤ C) (i j : ι) :
    |LinearMap.toMatrix b₀.toBasis b₀.toBasis (h.traceMul a) i j| ≤ C := by
  rw [LinearMap.toMatrix_apply, b₀.coe_toBasis_repr_apply,
    b₀.coe_toBasis, OrthonormalBasis.repr_apply_apply]
  have hb := norm_inner_le_norm (𝕜 := ℝ) (b₀ i) (h.traceMul a (b₀ j))
  simp only [Real.norm_eq_abs, b₀.norm_eq_one, one_mul] at hb
  exact hb.trans ((h.traceMul_norm_le a hC ha (b₀ j)).trans_eq (by
    rw [b₀.norm_eq_one, mul_one]))

end BostConjecture.Arithmetic.HermitianMetric
