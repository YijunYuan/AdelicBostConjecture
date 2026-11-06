/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Geometry.Plucker.Polarization
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Rank divisibility of actual special-linear polynomial invariants

Scalar roots of unity define actual special-linear transformations. Their
action on Hom and the nonzero homogeneous evaluation force degree divisibility.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Geometry

open Module InvariantTheory
open scoped TensorProduct

variable {F : Type} [Field F]
  {X : Type*} [AddCommGroup X] [Module F X]

/-- A scalar action at a nonzero evaluation forces its degree power to be one. -/
theorem scalar_pow_eq_one_of_invariant {G : Type*} [Group G]
    (ρ : Representation F G X) {d : ℕ}
    {p : SymmetricAlgebra F (Dual F X)} (hp : p ∈ homogeneousInvariants ρ d)
    {x : X} (hx : polynomialEval x p ≠ 0) (g : G) (a : F)
    (hg : ρ g x = a • x) : a ^ d = 1 := by
  have he := polynomialEval_orbit_of_mem_invariants ρ hp.2 g x
  rw [hg, polynomialEval_smul_of_mem_homogeneous hp.1] at he
  exact (mul_right_cancel₀ hx (he.trans (one_mul _).symm))

variable {U W V : Type*} [AddCommGroup U] [Module F U]
  [AddCommGroup W] [Module F W] [AddCommGroup V] [Module F V]

/-- Scalar units of rank power one are actual special-linear transformations. -/
def scalarSpecialLinear [FiniteDimensional F U] (a : Fˣ)
    (ha : (a : F) ^ finrank F U = 1) : SpecialLinearGroup F U :=
  ⟨LinearEquiv.smulOfUnit a, by
    apply Units.ext
    rw [LinearEquiv.coe_det]
    change LinearMap.det ((a : F) • (LinearMap.id : U →ₗ[F] U)) = 1
    rw [LinearMap.det_smul, LinearMap.det_id, mul_one, ha]⟩

@[simp]
theorem scalarSpecialLinear_apply [FiniteDimensional F U] (a : Fˣ)
    (ha : (a : F) ^ finrank F U = 1) (x : U) :
    scalarSpecialLinear (U := U) a ha x = (a : F) • x := rfl

theorem tensorSpecialLinear_scalar_left [FiniteDimensional F U] (a : Fˣ)
    (ha : (a : F) ^ finrank F U = 1) :
    tensorSpecialLinearRepresentation F U W (scalarSpecialLinear a ha, 1) =
      (a : F) • (LinearMap.id : U ⊗[F] W →ₗ[F] U ⊗[F] W) := by
  ext u w
  simp [scalarSpecialLinear_apply, TensorProduct.smul_tmul']

theorem tensorSpecialLinear_scalar_right [FiniteDimensional F W] (a : Fˣ)
    (ha : (a : F) ^ finrank F W = 1) :
    tensorSpecialLinearRepresentation F U W (1, scalarSpecialLinear a ha) =
      (a : F) • (LinearMap.id : U ⊗[F] W →ₗ[F] U ⊗[F] W) := by
  ext u w
  simp [scalarSpecialLinear_apply]

variable [FiniteDimensional F U] [FiniteDimensional F W]

omit [FiniteDimensional F W] in
/-- The first target rank divides the degree of a nonvanishing Hom invariant. -/
theorem left_rank_dvd_hom_invariant_degree
    [HasEnoughRootsOfUnity F (finrank F U)] (hU : finrank F U ≠ 0) {d : ℕ}
    {p : SymmetricAlgebra F (Dual F (V →ₗ[F] U ⊗[F] W))}
    (hp : p ∈ homogeneousInvariants
      (homSpecialLinearRepresentation (V := V) (tensorSpecialLinearRepresentation F U W)) d)
    {A : V →ₗ[F] U ⊗[F] W} (hA : polynomialEval A p ≠ 0) : finrank F U ∣ d := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot F (finrank F U)
  let a := (hζ.isUnit hU).unit
  have ha : (a : F) = ζ := (hζ.isUnit hU).unit_spec
  have hpow : (a : F) ^ finrank F U = 1 := by rw [ha, hζ.pow_eq_one]
  apply hζ.dvd_of_pow_eq_one
  apply scalar_pow_eq_one_of_invariant _ hp hA ((scalarSpecialLinear a hpow, 1), 1) ζ
  rw [homSpecialLinearRepresentation_apply, tensorSpecialLinear_scalar_left]
  simp [ha, LinearMap.smul_comp]

omit [FiniteDimensional F U] in
/-- The second target rank divides the same actual invariant degree. -/
theorem right_rank_dvd_hom_invariant_degree
    [HasEnoughRootsOfUnity F (finrank F W)] (hW : finrank F W ≠ 0) {d : ℕ}
    {p : SymmetricAlgebra F (Dual F (V →ₗ[F] U ⊗[F] W))}
    (hp : p ∈ homogeneousInvariants
      (homSpecialLinearRepresentation (V := V) (tensorSpecialLinearRepresentation F U W)) d)
    {A : V →ₗ[F] U ⊗[F] W} (hA : polynomialEval A p ≠ 0) : finrank F W ∣ d := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot F (finrank F W)
  let a := (hζ.isUnit hW).unit
  have ha : (a : F) = ζ := (hζ.isUnit hW).unit_spec
  have hpow : (a : F) ^ finrank F W = 1 := by rw [ha, hζ.pow_eq_one]
  apply hζ.dvd_of_pow_eq_one
  apply scalar_pow_eq_one_of_invariant _ hp hA ((1, scalarSpecialLinear a hpow), 1) ζ
  rw [homSpecialLinearRepresentation_apply, tensorSpecialLinear_scalar_right]
  simp [ha, LinearMap.smul_comp]

/-- Over an algebraically closed characteristic-zero field, both target ranks
divide every nonvanishing homogeneous Hom invariant degree. -/
theorem ranks_dvd_hom_invariant_degree [CharZero F] [IsAlgClosed F]
    (hU : finrank F U ≠ 0) (hW : finrank F W ≠ 0) {d : ℕ}
    {p : SymmetricAlgebra F (Dual F (V →ₗ[F] U ⊗[F] W))}
    (hp : p ∈ homogeneousInvariants
      (homSpecialLinearRepresentation (V := V) (tensorSpecialLinearRepresentation F U W)) d)
    {A : V →ₗ[F] U ⊗[F] W} (hA : polynomialEval A p ≠ 0) :
    finrank F U ∣ d ∧ finrank F W ∣ d := by
  let : NeZero ((finrank F U : ℕ) : F) := ⟨Nat.cast_ne_zero.mpr hU⟩
  let : NeZero ((finrank F W : ℕ) : F) := ⟨Nat.cast_ne_zero.mpr hW⟩
  exact ⟨left_rank_dvd_hom_invariant_degree hU hp hA,
    right_rank_dvd_hom_invariant_degree hW hp hA⟩

/-- The actual Plücker pullback has a positive degree divisible by all three
ranks, the arithmetic input needed before rectangular tensor identification. -/
theorem plucker_degree_positive_divisible [CharZero F] [IsAlgClosed F]
    [FiniteDimensional F V] {s m : ℕ} (b : Basis (Fin s) F V)
    (hs : 0 < s) (hm : 0 < m) (hU : finrank F U ≠ 0) (hW : finrank F W ≠ 0)
    {p : SymmetricAlgebra F (Dual F (⋀[F]^s (U ⊗[F] W)))}
    (hp : p ∈ homogeneousInvariants (pluckerRepresentation F U W s) m)
    {A : V →ₗ[F] U ⊗[F] W}
    (hA : polynomialEval (exteriorPower.ιMulti F s (fun i => A (b i))) p ≠ 0) :
    0 < s * m ∧ s ∣ s * m ∧ finrank F U ∣ s * m ∧ finrank F W ∣ s * m := by
  refine ⟨Nat.mul_pos hs hm, dvd_mul_right s m, ?_⟩
  exact ranks_dvd_hom_invariant_degree hU hW
    (pluckerPolynomialPullback_mem_invariants (tensorSpecialLinearRepresentation F U W) b hp.1
      (fun g => (mem_homogeneousInvariants_iff _ _ _).mp hp |>.2 g))
    (polynomialEval_pluckerPolynomialPullback_ne_zero b hA)

end BostConjecture.Geometry
