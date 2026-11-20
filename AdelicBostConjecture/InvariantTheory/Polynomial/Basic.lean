/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Finiteness.Subalgebra

/-!
# Intrinsic polynomials on a vector space

Polynomials are elements of the symmetric algebra of the dual. Evaluation,
linear pullback and the homogeneous degree subspaces use the universal property
of that algebra. These are the polynomial objects used by the orbit criterion.
-/

@[expose] public section

noncomputable section

namespace AdelicBostConjecture.InvariantTheory

variable {K X Y Z : Type*} [Field K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
  [AddCommGroup Z] [Module K Z]

/-- Evaluation of an intrinsic polynomial at a vector. -/
def polynomialEval (x : X) : SymmetricAlgebra K (Module.Dual K X) →ₐ[K] K :=
  SymmetricAlgebra.lift (Module.Dual.eval K X x)

@[simp]
theorem polynomialEval_ι (x : X) (ℓ : Module.Dual K X) :
    polynomialEval x (SymmetricAlgebra.ι K _ ℓ) = ℓ x := by
  simp [polynomialEval]

/-- Pullback of polynomials along a linear map. -/
def polynomialPullback (f : X →ₗ[K] Y) :
    SymmetricAlgebra K (Module.Dual K Y) →ₐ[K]
      SymmetricAlgebra K (Module.Dual K X) :=
  SymmetricAlgebra.lift ((SymmetricAlgebra.ι K _).comp f.dualMap)

@[simp]
theorem polynomialPullback_ι (f : X →ₗ[K] Y) (ℓ : Module.Dual K Y) :
    polynomialPullback f (SymmetricAlgebra.ι K _ ℓ) =
      SymmetricAlgebra.ι K _ (ℓ.comp f) := by
  simp only [polynomialPullback, SymmetricAlgebra.lift_ι_apply, LinearMap.comp_apply]
  rfl

@[simp]
theorem polynomialPullback_id : polynomialPullback (LinearMap.id : X →ₗ[K] X) =
    AlgHom.id K _ := by
  apply SymmetricAlgebra.algHom_ext
  ext ℓ
  simp

theorem polynomialPullback_comp (f : X →ₗ[K] Y) (g : Y →ₗ[K] Z) :
    polynomialPullback (g.comp f) = (polynomialPullback f).comp (polynomialPullback g) := by
  apply SymmetricAlgebra.algHom_ext
  ext ℓ
  simp [LinearMap.comp_assoc]

theorem polynomialEval_comp_pullback (f : X →ₗ[K] Y) (x : X) :
    (polynomialEval x).comp (polynomialPullback f) = polynomialEval (f x) := by
  apply SymmetricAlgebra.algHom_ext
  ext ℓ
  simp

@[simp]
theorem polynomialEval_pullback (f : X →ₗ[K] Y) (x : X)
    (p : SymmetricAlgebra K (Module.Dual K Y)) :
    polynomialEval x (polynomialPullback f p) = polynomialEval (f x) p :=
  DFunLike.congr_fun (polynomialEval_comp_pullback f x) p

/-- The subspace spanned by products of exactly `d` linear forms. -/
def homogeneousPolynomials (K X : Type*) [Field K] [AddCommGroup X] [Module K X]
    (d : ℕ) : Submodule K (SymmetricAlgebra K (Module.Dual K X)) :=
  (LinearMap.range (SymmetricAlgebra.ι K (Module.Dual K X))) ^ d

theorem polynomialEval_smul_of_mem_homogeneous {d : ℕ}
    {p : SymmetricAlgebra K (Module.Dual K X)} (hp : p ∈ homogeneousPolynomials K X d)
    (a : K) (x : X) : polynomialEval (a • x) p = a ^ d * polynomialEval x p := by
  induction hp using Submodule.pow_induction_on_left' with
  | algebraMap r => simp
  | add p q d hp hq ihp ihq => simp [ihp, ihq, mul_add]
  | mem_mul m hm d p hp ih =>
    obtain ⟨ℓ, rfl⟩ := hm
    simp only [map_mul, polynomialEval_ι, map_smul, smul_eq_mul, ih, pow_succ]
    ring

theorem polynomialEval_zero_of_mem_homogeneous {d : ℕ} (hd : d ≠ 0)
    {p : SymmetricAlgebra K (Module.Dual K X)} (hp : p ∈ homogeneousPolynomials K X d) :
    polynomialEval (0 : X) p = 0 := by
  simpa [zero_pow hd] using polynomialEval_smul_of_mem_homogeneous hp 0 (0 : X)

theorem polynomialPullback_mem_homogeneous (f : X →ₗ[K] Y) {d : ℕ}
    {p : SymmetricAlgebra K (Module.Dual K Y)} (hp : p ∈ homogeneousPolynomials K Y d) :
    polynomialPullback f p ∈ homogeneousPolynomials K X d := by
  induction hp using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    simpa only [AlgHom.commutes, homogeneousPolynomials, pow_zero] using
      (Submodule.algebraMap_mem (R := K) (A := SymmetricAlgebra K (Module.Dual K X)) r)
  | add p q d hp hq ihp ihq => simpa using (homogeneousPolynomials K X d).add_mem ihp ihq
  | mem_mul m hm d p hp ih =>
    obtain ⟨ℓ, rfl⟩ := hm
    simp only [map_mul, polynomialPullback_ι]
    change _ ∈ (LinearMap.range (SymmetricAlgebra.ι K (Module.Dual K X))) ^ (d + 1)
    rw [pow_succ']
    exact Submodule.mul_mem_mul ⟨ℓ.comp f, rfl⟩ ih

instance finiteDimensional_homogeneousPolynomials [FiniteDimensional K X] (d : ℕ) :
    FiniteDimensional K (homogeneousPolynomials K X d) :=
  Module.Finite.of_fg (((Submodule.fg_iff_finiteDimensional _).mpr inferInstance).pow d)

end AdelicBostConjecture.InvariantTheory
