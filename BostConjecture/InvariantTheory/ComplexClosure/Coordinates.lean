/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.InvariantTheory.Semistability
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Coordinates for intrinsic polynomial zero loci

The symmetric algebra of the dual is identified with multivariate polynomials
using Mathlib's basis equivalence. Its evaluation agrees with the canonical
intrinsic evaluation, so the intrinsic Zariski closure is exactly the preimage
of the usual zero locus of the coordinate vanishing ideal.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.InvariantTheory

open Module

section Algebra

variable {K E τ : Type*} [Field K] [AddCommGroup E] [Module K E] [Finite τ]

/-- Evaluation in the dual-basis polynomial coordinates is intrinsic evaluation. -/
theorem polynomialEval_equivMvPolynomial_symm [DecidableEq τ] (b : Basis τ K E) (x : E)
    (p : MvPolynomial τ K) :
    polynomialEval x ((SymmetricAlgebra.equivMvPolynomial b.dualBasis).symm p) =
      MvPolynomial.eval (b.equivFun x) p := by
  have h : (polynomialEval x).comp
      (SymmetricAlgebra.equivMvPolynomial b.dualBasis).symm.toAlgHom =
      MvPolynomial.aeval (b.equivFun x) := by
    ext i
    simp
  exact DFunLike.congr_fun h p

theorem polynomialEval_eq_eval_equivMvPolynomial [DecidableEq τ] (b : Basis τ K E) (x : E)
    (p : SymmetricAlgebra K (Module.Dual K E)) :
    polynomialEval x p =
      MvPolynomial.eval (b.equivFun x) (SymmetricAlgebra.equivMvPolynomial b.dualBasis p) := by
  simpa using polynomialEval_equivMvPolynomial_symm b x
    (SymmetricAlgebra.equivMvPolynomial b.dualBasis p)

/-- The canonical intrinsic closure is the usual coordinate zero locus. -/
theorem polynomialZariskiClosure_eq_preimage_zeroLocus (b : Basis τ K E) (S : Set E) :
    polynomialZariskiClosure (K := K) S =
      b.equivFun ⁻¹' MvPolynomial.zeroLocus K
        (MvPolynomial.vanishingIdeal K (b.equivFun '' S)) := by
  classical
  ext x
  constructor
  · intro hx p hp
    change MvPolynomial.eval (b.equivFun x) p = 0
    rw [← polynomialEval_equivMvPolynomial_symm b x p]
    apply hx
    intro y hy
    rw [polynomialEval_equivMvPolynomial_symm]
    exact hp _ ⟨y, hy, rfl⟩
  · intro hx p hp
    rw [polynomialEval_eq_eval_equivMvPolynomial b x p]
    apply hx
    rintro _ ⟨y, hy, rfl⟩
    change MvPolynomial.eval (b.equivFun y)
      (SymmetricAlgebra.equivMvPolynomial b.dualBasis p) = 0
    rw [← polynomialEval_eq_eval_equivMvPolynomial]
    exact hp y hy

end Algebra

section Complex

variable {E τ σ : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [Finite τ]

/-- A coordinate algebraic zero locus is closed for the Euclidean topology. -/
theorem isClosed_zeroLocus (I : Ideal (MvPolynomial σ ℂ)) :
    IsClosed (MvPolynomial.zeroLocus ℂ I) := by
  have h : MvPolynomial.zeroLocus ℂ I =
      ⋂ p ∈ I, {x | MvPolynomial.eval x p = 0} := by
    ext x
    simp [MvPolynomial.mem_zeroLocus_iff, MvPolynomial.aeval_def]
  rw [h]
  exact isClosed_biInter fun p _ => isClosed_eq p.continuous_eval continuous_const

theorem continuous_polynomialEval (b : Basis τ ℂ E)
    (p : SymmetricAlgebra ℂ (Module.Dual ℂ E)) :
    Continuous (fun x : E => polynomialEval x p) := by
  classical
  simp_rw [polynomialEval_eq_eval_equivMvPolynomial b]
  exact (MvPolynomial.continuous_eval _).comp (continuous_equivFun_basis b)

theorem isClosed_polynomialZariskiClosure (b : Basis τ ℂ E) (S : Set E) :
    IsClosed (polynomialZariskiClosure (K := ℂ) S) := by
  rw [polynomialZariskiClosure_eq_preimage_zeroLocus b]
  exact (isClosed_zeroLocus _).preimage (continuous_equivFun_basis b)

theorem closure_subset_polynomialZariskiClosure (b : Basis τ ℂ E) (S : Set E) :
    closure S ⊆ polynomialZariskiClosure (K := ℂ) S :=
  closure_minimal (subset_polynomialZariskiClosure S) (isClosed_polynomialZariskiClosure b S)

end Complex

end BostConjecture.InvariantTheory
