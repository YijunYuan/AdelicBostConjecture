/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Balanced.ExteriorMetric
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.Convex.Deriv

/-!
# Spectral expansion of the exterior exponential

The operator exponential acts on an eigenvector by the scalar exponential.
On exterior basis wedges this multiplies the corresponding eigenvalues,
giving the nonnegative exponential sum used in the balanced norm argument.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Balanced

open exteriorPower

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- The operator exponential acts by the scalar exponential on an eigenvector. -/
theorem exp_apply_of_apply_eq_smul (A : E →L[ℂ] E) (x : E) (a : ℂ)
    (hx : A x = a • x) : NormedSpace.exp A x = NormedSpace.exp a • x := by
  let := FiniteDimensional.complete ℂ E
  have hp (n : ℕ) : (A ^ n) x = a ^ n • x := by
    induction n with
    | zero => simp
    | succ n hn => simp [pow_succ', hn, hx, smul_smul, mul_comm]
  have h := (ContinuousLinearMap.apply ℂ E x).hasSum
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A)
  simp only [map_smul, ContinuousLinearMap.apply_apply, hp, smul_smul] at h
  have h' := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) a).smul_const x
  exact h.unique (by simpa only [smul_eq_mul] using h')

theorem exp_real_smul_apply_of_apply_eq_smul (A : E →L[ℂ] E) (x : E) (a t : ℝ)
    (hx : A x = (a : ℂ) • x) :
    NormedSpace.exp (t • A) x = (Real.exp (t * a) : ℂ) • x := by
  have ht : (t • A) x = ((t * a : ℝ) : ℂ) • x := by
    simp only [smul_apply, hx, RCLike.real_smul_eq_coe_smul (K := ℂ),
      smul_smul, Complex.ofReal_mul]
    rfl
  rw [exp_apply_of_apply_eq_smul _ _ _ ht, ← Complex.exp_eq_exp_ℂ, ← Complex.ofReal_exp]

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

theorem exterior_map_basis_of_apply_eq_smul (b : OrthonormalBasis ι ℂ E)
    (s : ℕ) (A : Module.End ℂ E) (a : ι → ℂ) (ha : ∀ i, A (b i) = a i • b i)
    (I : Set.powersetCard ι s) :
    exteriorPower.map s A (exteriorOrthonormalBasis b s I) =
      (∏ j : Fin s, a (Set.powersetCard.ofFinEmbEquiv.symm I j)) •
        exteriorOrthonormalBasis b s I := by
  simp only [exteriorOrthonormalBasis_apply, ιMulti_family, map_apply_ιMulti,
    Function.comp_def, ha]
  exact (ιMulti ℂ s (M := E)).map_smul_univ _ _

omit [LinearOrder ι] [FiniteDimensional ℂ E] in
theorem norm_sq_apply_of_basis (b : OrthonormalBasis ι ℂ E)
    (A : Module.End ℂ E) (a : ι → ℂ) (ha : ∀ i, A (b i) = a i • b i) (x : E) :
    ‖A x‖ ^ 2 = ∑ i, ‖b.repr x i‖ ^ 2 * ‖a i‖ ^ 2 := by
  classical
  have hAx : A x = ∑ i, (b.repr x i * a i) • b i := by
    conv_lhs => rw [← b.sum_repr x]
    simp only [map_sum, map_smul, ha, smul_smul]
  rw [← b.sum_sq_norm_inner_right (A x)]
  apply Finset.sum_congr rfl
  intro i _
  rw [← b.repr_apply_apply, hAx]
  simp [map_sum, b.repr_self, Pi.single_apply, mul_ite, mul_pow]

theorem exterior_exp_apply_basis (b : OrthonormalBasis ι ℂ E) (s : ℕ)
    (A : E →L[ℂ] E) (a : ι → ℝ) (ha : ∀ i, A (b i) = (a i : ℂ) • b i)
    (t : ℝ) (I : Set.powersetCard ι s) :
    exteriorPower.map s (NormedSpace.exp (t • A)).toLinearMap
      (exteriorOrthonormalBasis b s I) =
      (Real.exp (t * ∑ j : Fin s, a (Set.powersetCard.ofFinEmbEquiv.symm I j)) : ℂ) •
        exteriorOrthonormalBasis b s I := by
  rw [exterior_map_basis_of_apply_eq_smul b s _ (fun i => (Real.exp (t * a i) : ℂ))
    (fun i => exp_real_smul_apply_of_apply_eq_smul A (b i) (a i) t (ha i))]
  congr 1
  rw [← Complex.ofReal_prod, ← Real.exp_sum, Finset.mul_sum]

/-- The squared norm of the actual exterior exponential is a finite sum of
nonnegative coefficients times real exponentials. -/
theorem exterior_exp_norm_sq (b : OrthonormalBasis ι ℂ E) (s : ℕ)
    (A : E →L[ℂ] E) (a : ι → ℝ) (ha : ∀ i, A (b i) = (a i : ℂ) • b i)
    (z : ⋀[ℂ]^s E) (t : ℝ) :
    ‖exteriorPower.map s (NormedSpace.exp (t • A)).toLinearMap z‖ ^ 2 =
      ∑ I, ‖(exteriorOrthonormalBasis b s).repr z I‖ ^ 2 *
        Real.exp (2 * t * ∑ j : Fin s, a (Set.powersetCard.ofFinEmbEquiv.symm I j)) := by
  rw [norm_sq_apply_of_basis (exteriorOrthonormalBasis b s) _ _
    (exterior_exp_apply_basis b s A a ha t)]
  apply Finset.sum_congr rfl
  intro I _
  congr 1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    pow_two, ← Real.exp_add]
  congr 1
  ring

/-- Spectral expansion for every Hermitian generator on the actual exterior space. -/
theorem exterior_exp_norm_sq_of_isSymmetric (A : Module.End ℂ E) (hA : A.IsSymmetric)
    (s : ℕ) (z : ⋀[ℂ]^s E) (t : ℝ) :
    ‖exteriorPower.map s
      (NormedSpace.exp (t • LinearMap.toContinuousLinearMap A)).toLinearMap z‖ ^ 2 =
      ∑ I : Set.powersetCard (Fin (Module.finrank ℂ E)) s,
        ‖(exteriorOrthonormalBasis (hA.eigenvectorBasis rfl) s).repr z I‖ ^ 2 *
          Real.exp (2 * t * ∑ j : Fin s,
            hA.eigenvalues rfl (Set.powersetCard.ofFinEmbEquiv.symm I j)) :=
  exterior_exp_norm_sq (hA.eigenvectorBasis rfl) s (LinearMap.toContinuousLinearMap A)
    (hA.eigenvalues rfl) (hA.apply_eigenvectorBasis rfl) z t

theorem convexOn_sum_exp {κ : Type*} (K : Finset κ) (c a : κ → ℝ)
    (hc : ∀ i, 0 ≤ c i) :
    ConvexOn ℝ Set.univ (fun t : ℝ => ∑ i ∈ K, c i * Real.exp (t * a i)) := by
  classical
  induction K using Finset.induction_on with
  | empty => simpa using (convexOn_const (c := (0 : ℝ)) convex_univ)
  | @insert i K hi hK =>
    have he : ConvexOn ℝ Set.univ (fun t : ℝ => Real.exp (t * a i)) := by
      simpa [Function.comp_def, mul_comm] using
        convexOn_exp.comp_linearMap (a i • (LinearMap.id : ℝ →ₗ[ℝ] ℝ))
    simpa only [Finset.sum_insert hi, Pi.add_def, smul_eq_mul] using (he.smul (hc i)).add hK

/-- The actual exterior norm squared is convex along every Hermitian exponential. -/
theorem convexOn_exterior_exp_norm_sq (A : Module.End ℂ E) (hA : A.IsSymmetric)
    (s : ℕ) (z : ⋀[ℂ]^s E) :
    ConvexOn ℝ Set.univ (fun t : ℝ => ‖exteriorPower.map s
      (NormedSpace.exp (t • LinearMap.toContinuousLinearMap A)).toLinearMap z‖ ^ 2) := by
  let b := exteriorOrthonormalBasis (hA.eigenvectorBasis rfl) s
  convert convexOn_sum_exp Finset.univ (fun I => ‖b.repr z I‖ ^ 2)
    (fun I => 2 * ∑ j : Fin s, hA.eigenvalues rfl
      (Set.powersetCard.ofFinEmbEquiv.symm I j)) (fun _ => sq_nonneg _) using 1
  funext t
  rw [exterior_exp_norm_sq_of_isSymmetric A hA]
  apply Finset.sum_congr rfl
  intro I _
  congr 2
  ring

/-- A stationary point of the Hermitian exterior norm flow is a global minimum. -/
theorem exterior_norm_sq_le_exp_of_hasDerivAt_zero (A : Module.End ℂ E)
    (hA : A.IsSymmetric) (s : ℕ) (z : ⋀[ℂ]^s E)
    (hd : HasDerivAt (fun t : ℝ => ‖exteriorPower.map s
      (NormedSpace.exp (t • LinearMap.toContinuousLinearMap A)).toLinearMap z‖ ^ 2) 0 0)
    (t : ℝ) :
    ‖z‖ ^ 2 ≤ ‖exteriorPower.map s
      (NormedSpace.exp (t • LinearMap.toContinuousLinearMap A)).toLinearMap z‖ ^ 2 := by
  have hm := (convexOn_exterior_exp_norm_sq A hA s z).isMinOn_of_rightDeriv_eq_zero
    (by simp) (hd.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi 0))
  have hmap : exteriorPower.map s (1 : Module.End ℂ E) = LinearMap.id := map_id
  simpa [hmap] using hm (Set.mem_univ t)

end BostConjecture.Balanced
