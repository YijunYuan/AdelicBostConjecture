/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.InvariantTheory.SpecialLinear.LocalizationDetection
public import Mathlib.LinearAlgebra.Matrix.MvPolynomial
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import BostConjecture.Balanced.PolarLog
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Order.Interval.Set.Infinite

/-!
# Polynomial detection on compact unitary groups

The diagonal step uses polynomial uniqueness on products of unit circles.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.InvariantTheory

/-- The unit circle supplies infinitely many test values for a polynomial. -/
theorem infinite_circle_values : (Set.range ((↑) : Circle → ℂ)).Infinite := by
  have hi := Set.Icc_infinite Real.pi_pos
  have he := Circle.exp_injOn_Icc (a := 0) (b := Real.pi) (by linarith [Real.pi_pos])
  have hc : Function.Injective ((↑) : Circle → ℂ) := Subtype.val_injective
  exact ((hi.image he).image hc.injOn).mono (Set.image_subset_range _ _)

/-- A complex polynomial is determined by its values on a product of unit circles. -/
theorem polynomial_eq_zero_of_eval_circle {σ : Type*} (p : MvPolynomial σ ℂ)
    (hp : ∀ z : σ → Circle, MvPolynomial.eval (fun i => (z i : ℂ)) p = 0) :
    p = 0 := by
  classical
  apply MvPolynomial.funext_set (fun _ => Set.range ((↑) : Circle → ℂ))
    (fun _ => infinite_circle_values)
  intro x hx
  have hx' (i : σ) : ∃ z : Circle, (z : ℂ) = x i := hx i (Set.mem_univ i)
  choose z hz using hx'
  simpa only [hz, map_zero] using hp z

/-- Polar decomposition and the Hermitian spectral theorem give unitary-diagonal-unitary
factorization of every invertible complex square matrix. -/
theorem exists_unitary_diagonal_unitary {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : IsUnit A) :
    ∃ u v : Matrix.unitaryGroup n ℂ, ∃ d : n → ℂ,
      A = (u : Matrix n n ℂ) * Matrix.diagonal d * (v : Matrix n n ℂ) := by
  let e := Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)
  let T := e A
  have hT : Function.Injective T :=
    (ContinuousLinearMap.isUnit_iff_bijective.mp (hA.map e.toMonoidHom)).injective
  let P := e.symm T.polar
  let Q := e.symm T.abs
  have hP : P ∈ Matrix.unitaryGroup n ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    apply e.injective
    change e (star P * P) = e 1
    rw [map_mul, map_star, map_one]
    simpa only [P, e.apply_symm_apply, ContinuousLinearMap.mul_def,
      ContinuousLinearMap.star_eq_adjoint] using
      (T.polar.norm_map_iff_adjoint_comp_self.mp (Balanced.norm_polar_apply T hT))
  have hQ : Q.IsHermitian := by
    change star Q = Q
    apply e.injective
    change e (star Q) = e Q
    rw [map_star]
    simpa only [Q, e.apply_symm_apply] using T.abs_nonneg.isSelfAdjoint.star_eq
  have hPQ : A = P * Q := by
    apply e.injective
    change e A = e (P * Q)
    rw [map_mul]
    simpa only [P, Q, T, e.apply_symm_apply, ContinuousLinearMap.mul_def] using
      T.polar_comp_abs.symm
  let p : Matrix.unitaryGroup n ℂ := ⟨P, hP⟩
  refine ⟨p * hQ.eigenvectorUnitary, star hQ.eigenvectorUnitary,
    RCLike.ofReal ∘ hQ.eigenvalues, ?_⟩
  calc
    A = P * Q := hPQ
    _ = P * Unitary.conjStarAlgAut ℂ _ hQ.eigenvectorUnitary
      (Matrix.diagonal (RCLike.ofReal ∘ hQ.eigenvalues)) :=
      congrArg (P * ·) hQ.spectral_theorem
    _ = _ := by
      simp only [Unitary.conjStarAlgAut_apply, Submonoid.coe_mul, Unitary.coe_star, mul_assoc]
      rfl

/-- Vanishing on the compact unitary group extends along each two-sided unitary
translate of the space of diagonal matrices. -/
theorem eval_eq_zero_unitary_diagonal_unitary {n : Type*} [Fintype n] [DecidableEq n]
    (p : MvPolynomial (n × n) ℂ)
    (hp : ∀ u : Matrix.unitaryGroup n ℂ,
      MvPolynomial.eval (Function.uncurry (u : Matrix n n ℂ)) p = 0)
    (u v : Matrix.unitaryGroup n ℂ) (d : n → ℂ) :
    MvPolynomial.eval (Function.uncurry
      ((u : Matrix n n ℂ) * Matrix.diagonal d * (v : Matrix n n ℂ))) p = 0 := by
  let f : n × n → MvPolynomial n ℂ := fun ij =>
    ∑ k, MvPolynomial.C (u ij.1 k * v k ij.2) * MvPolynomial.X k
  let q := MvPolynomial.eval₂ MvPolynomial.C f p
  have he (z : n → ℂ) : MvPolynomial.eval z q =
      MvPolynomial.eval (Function.uncurry
        ((u : Matrix n n ℂ) * Matrix.diagonal z * (v : Matrix n n ℂ))) p := by
    rw [← MvPolynomial.eval_assoc]
    apply congrArg (fun z => MvPolynomial.eval z p)
    funext ij
    simp only [Function.comp_apply, f, map_sum, map_mul, MvPolynomial.eval_C,
      MvPolynomial.eval_X]
    apply Finset.sum_congr rfl
    intro k _
    change (u : Matrix n n ℂ) ij.1 k * (v : Matrix n n ℂ) k ij.2 * z k =
      ((u : Matrix n n ℂ) * Matrix.diagonal z) ij.1 k * (v : Matrix n n ℂ) k ij.2
    rw [Matrix.mul_diagonal]
    ring
  have hq : q = 0 := polynomial_eq_zero_of_eval_circle q (by
    intro z
    rw [he]
    have hd : Matrix.diagonal (fun i => (z i : ℂ)) ∈ Matrix.unitaryGroup n ℂ := by
      rw [Matrix.diagonal_mem_unitary, Pi.mem_unitary_iff]
      intro i
      constructor <;> simp [← Circle.coe_inv_eq_conj]
    exact hp ⟨_, (Matrix.unitaryGroup n ℂ).mul_mem
      ((Matrix.unitaryGroup n ℂ).mul_mem u.property hd) v.property⟩)
  rw [← he, hq, map_zero]

/-- A polynomial vanishing on all unitary matrices vanishes on every invertible matrix. -/
theorem eval_eq_zero_of_unitary_of_isUnit {n : Type*} [Fintype n] [DecidableEq n]
    (p : MvPolynomial (n × n) ℂ)
    (hp : ∀ u : Matrix.unitaryGroup n ℂ,
      MvPolynomial.eval (Function.uncurry (u : Matrix n n ℂ)) p = 0)
    (A : Matrix n n ℂ) (hA : IsUnit A) :
    MvPolynomial.eval (Function.uncurry A) p = 0 := by
  obtain ⟨u, v, d, rfl⟩ := exists_unitary_diagonal_unitary A hA
  exact eval_eq_zero_unitary_diagonal_unitary p hp u v d

/-- The compact unitary group is polynomially dense in the full matrix space. -/
theorem polynomial_eq_zero_of_eval_unitary {n : Type*} [Fintype n] [DecidableEq n]
    (p : MvPolynomial (n × n) ℂ)
    (hp : ∀ u : Matrix.unitaryGroup n ℂ,
      MvPolynomial.eval (Function.uncurry (u : Matrix n n ℂ)) p = 0) : p = 0 := by
  apply polynomial_eq_zero_of_eval_on_principalOpen (Matrix.det_mvPolynomialX_ne_zero n ℂ)
  intro x hx
  have hd : Matrix.det (Matrix.of fun i j => x (i, j)) ≠ 0 := by
    change MvPolynomial.eval x (Matrix.det (Matrix.mvPolynomialX n n ℂ)) ≠ 0 at hx
    simpa only [Matrix.eval_det_mvPolynomialX] using hx
  exact eval_eq_zero_of_unitary_of_isUnit p hp (Matrix.of fun i j => x (i, j))
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd))

end BostConjecture.InvariantTheory
