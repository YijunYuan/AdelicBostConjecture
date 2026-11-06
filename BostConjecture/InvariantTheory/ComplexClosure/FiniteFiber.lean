/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.InvariantTheory.ComplexClosure.Roots
public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs

/-!
# Finite fibers and polynomial separation

A finite set of coordinate points can be separated from an external point
by a product of coordinate differences. This will isolate the desired
limit in the finite-normalization argument.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.InvariantTheory

/-- Coordinate differences separate a point from a finite set, including the empty set. -/
theorem exists_polynomial_separator {K τ : Type*} [Field K]
    (S : Set (τ → K)) (hS : S.Finite) {p : τ → K} (hp : p ∉ S) :
    ∃ u : MvPolynomial τ K, MvPolynomial.eval p u = 1 ∧
      ∀ q ∈ S, MvPolynomial.eval q u = 0 := by
  classical
  let : Fintype S := hS.fintype
  have hdiff (q : S) : ∃ i, p i ≠ q.val i := by
    by_contra! h
    exact hp ((funext h).symm ▸ q.property)
  choose j hj using hdiff
  let u : MvPolynomial τ K := ∏ q : S,
    MvPolynomial.C ((p (j q) - q.val (j q))⁻¹) *
      (MvPolynomial.X (j q) - MvPolynomial.C (q.val (j q)))
  refine ⟨u, ?_, ?_⟩
  · simp only [u, map_prod, map_mul, map_sub, MvPolynomial.eval_C, MvPolynomial.eval_X]
    exact Finset.prod_eq_one fun q _ => inv_mul_cancel₀ (sub_ne_zero.mpr (hj q))
  · intro q hq
    simp only [u, map_prod, map_mul, map_sub, MvPolynomial.eval_C, MvPolynomial.eval_X]
    apply Finset.prod_eq_zero (Finset.mem_univ (⟨q, hq⟩ : S))
    simp

/-- Integrality supplies monic coordinate equations valid at every point of the zero locus. -/
theorem exists_monic_coordinate_relation {K σ τ : Type*} [Field K]
    (I : Ideal (MvPolynomial τ K)) (q : σ → MvPolynomial τ K)
    (hq : ((Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval q)).toRingHom.IsIntegral)
    (i : τ) :
    ∃ F : Polynomial (MvPolynomial σ K), F.Monic ∧
      ∀ x ∈ MvPolynomial.zeroLocus K I,
        (F.map (MvPolynomial.eval (fun j => MvPolynomial.eval x (q j)))).IsRoot (x i) := by
  let f := (Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval q)
  obtain ⟨F, hF, hroot⟩ := hq (Ideal.Quotient.mk I (MvPolynomial.X i))
  refine ⟨F, hF, fun x hx => ?_⟩
  let a := fun j => MvPolynomial.eval x (q j)
  let χ : (MvPolynomial τ K ⧸ I) →ₐ[K] K :=
    Ideal.Quotient.liftₐ I (MvPolynomial.aeval x) hx
  have hχ (p : MvPolynomial τ K) : χ (Ideal.Quotient.mk I p) = MvPolynomial.eval x p :=
    DFunLike.congr_fun (Ideal.Quotient.liftₐ_comp I (MvPolynomial.aeval x) hx) p
  have hc : χ.comp f = MvPolynomial.aeval a := by
    ext j
    simp only [f, AlgHom.comp_apply, MvPolynomial.aeval_X]
    exact hχ (q j)
  have hc' : χ.toRingHom.comp f.toRingHom = MvPolynomial.eval a :=
    congrArg AlgHom.toRingHom hc
  have hr := congrArg χ hroot
  change χ.toRingHom (F.eval₂ f.toRingHom (Ideal.Quotient.mk I (MvPolynomial.X i))) =
    χ 0 at hr
  rw [map_zero, Polynomial.hom_eval₂, hc'] at hr
  change F.eval₂ (MvPolynomial.eval a) (χ (Ideal.Quotient.mk I (MvPolynomial.X i))) =
    0 at hr
  rw [hχ, MvPolynomial.eval_X] at hr
  simpa only [Polynomial.IsRoot, Polynomial.eval_map] using hr

/-- An integral polynomial map has finite fibers on its algebraic zero locus. -/
theorem finite_zeroLocus_fiber {K σ τ : Type*} [Field K] [Finite τ]
    (I : Ideal (MvPolynomial τ K)) (q : σ → MvPolynomial τ K)
    (hq : ((Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval q)).toRingHom.IsIntegral)
    (a : σ → K) :
    {x : τ → K | x ∈ MvPolynomial.zeroLocus K I ∧
      ∀ i, MvPolynomial.eval x (q i) = a i}.Finite := by
  choose F hF hroot using exists_monic_coordinate_relation I q hq
  refine (Set.Finite.pi' (fun i => Polynomial.finite_setOfPred_isRoot
    ((hF i).map (MvPolynomial.eval a)).ne_zero)).subset ?_
  intro x hx i
  have he : (fun j => MvPolynomial.eval x (q j)) = a := funext hx.2
  simpa only [he, Set.mem_ofPred_eq] using hroot i x hx.1

/-- Coordinates of all lifts of a convergent base sequence are uniformly bounded. -/
theorem exists_bound_zeroLocus_fibers {σ τ : Type*}
    (I : Ideal (MvPolynomial τ ℂ)) (q : σ → MvPolynomial τ ℂ)
    (hq : ((Ideal.Quotient.mkₐ ℂ I).comp (MvPolynomial.aeval q)).toRingHom.IsIntegral)
    {a : ℕ → σ → ℂ} {a₀ : σ → ℂ} (ha : Filter.Tendsto a Filter.atTop (nhds a₀)) :
    ∃ B : τ → NNReal, ∀ k x, x ∈ MvPolynomial.zeroLocus ℂ I →
      (∀ i, MvPolynomial.eval x (q i) = a k i) → ∀ j, ‖x j‖₊ ≤ B j := by
  choose F hF hroot using exists_monic_coordinate_relation I q hq
  choose B hB using fun j => exists_bound_roots_specialization (F j) (hF j) ha
  refine ⟨B, fun k x hx hxa j => hB j k (x j) ?_⟩
  have he : (fun i => MvPolynomial.eval x (q i)) = a k := funext hxa
  simpa only [he] using hroot j x hx

end BostConjecture.InvariantTheory
