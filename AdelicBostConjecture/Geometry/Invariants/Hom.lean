/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import AdelicBostConjecture.Geometry.Polynomial.HomTensor
public import AdelicBostConjecture.Geometry.Plucker.Polynomial
public import AdelicBostConjecture.Geometry.Polynomial.Polarization
public import AdelicBostConjecture.Geometry.Invariants.Independent
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Nonzero Hom pairing on independent invariant factors

The actual invariant polynomial is lifted, regrouped, and restricted to the
independent invariant subspaces. No invariant-space equality is assumed.
-/

@[expose] public section

noncomputable section

namespace AdelicBostConjecture.Geometry

open Module PiTensorProduct InvariantTheory
open scoped TensorProduct

variable {F : Type*} {G V W : Type*} [Field F] [Group G]
  [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

/-- The tensor-power action induced by an existing representation. -/
def tensorPowerRepresentation (ρ : Representation F G V) (d : ℕ) :
    Representation F G (⨂[F] (_ : Fin d), V) where
  toFun g := PiTensorProduct.map fun _ => ρ g
  map_one' := by simp
  map_mul' g h := by simp only [map_mul, PiTensorProduct.map_mul]

private theorem exists_nonzero_invariant_pair {H : Type*} [Group H]
    (σ : Representation F G V) (τ : Representation F H W)
    (B : V →ₗ[F] W →ₗ[F] F) (z : V ⊗[F] W)
    (hz : TensorProduct.lift B z ≠ 0)
    (hfix : ∀ g h, TensorProduct.map (σ g) (τ h) z = z) :
    ∃ (v : V) (w : W), (∀ g, σ g v = v) ∧ (∀ h, τ h w = w) ∧ B v w ≠ 0 := by
  obtain ⟨y, hy⟩ := (exists_independent_invariants_iff σ τ z).mpr hfix
  have hex : ∃ (v : σ.invariants) (w : τ.invariants), B v.val w.val ≠ 0 := by
    by_contra! hall
    have hzero : (TensorProduct.lift B).comp
        (TensorProduct.map σ.invariants.subtype τ.invariants.subtype) = 0 := by
      apply TensorProduct.ext
      apply LinearMap.ext
      intro v
      apply LinearMap.ext
      exact fun w => hall v w
    apply hz
    rw [← hy]
    exact LinearMap.congr_fun hzero y
  obtain ⟨v, w, hvw⟩ := hex
  exact ⟨v.val, w.val, v.property, w.property, hvw⟩

variable [FiniteDimensional F V] [FiniteDimensional F W] [CharZero F]

/-- A nonzero invariant Hom polynomial detects a nonzero canonical pairing on
source special-linear invariants and dual-target invariants separately. -/
theorem exists_independent_invariant_pairing
    (ρ : Representation F G W) (A : V →ₗ[F] W) {d : ℕ}
    {p : SymmetricAlgebra F (Dual F (V →ₗ[F] W))}
    (hp : p ∈ homogeneousInvariants (homSpecialLinearRepresentation ρ) d)
    (hpA : polynomialEval A p ≠ 0) :
    ∃ (v : ⨂[F] (_ : Fin d), V) (ℓ : ⨂[F] (_ : Fin d), Dual F W),
      (∀ h : SpecialLinearGroup F V,
        PiTensorProduct.map (fun _ => (h : V →ₗ[F] V)) v = v) ∧
      (∀ g : G, PiTensorProduct.map (fun _ => (ρ g⁻¹).dualMap) ℓ = ℓ) ∧
      Tensor.tensorPowerPairing A v ℓ ≠ 0 := by
  -- Keep the inherited tensor monoid structures definitionally visible.
  let : AddCommGroup (⨂[F] (_ : Fin d), V) :=
    Module.addCommMonoidToAddCommGroup F
  let : AddCommGroup (⨂[F] (_ : Fin d), Dual F W) :=
    Module.addCommMonoidToAddCommGroup F
  obtain ⟨u, hu, hufix, _⟩ := exists_invariant_tensor_evaluation_ne_zero
    (homSpecialLinearRepresentation ρ) hp hpA
  obtain ⟨z, _, hz, hzfix⟩ := exists_regrouped_hom_tensor A u (by rwa [hu])
  let σ : Representation F (SpecialLinearGroup F V) V :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
      SpecialLinearGroup.toLinearEquiv
  let σd := tensorPowerRepresentation σ d
  let τd := tensorPowerRepresentation ρ.dual d
  have hfix (h : SpecialLinearGroup F V) (g : G) :
      TensorProduct.map (σd h) (τd g) z = z := by
    apply hzfix (h : V →ₗ[F] V) (ρ g⁻¹)
    have he : ((ρ g⁻¹).compRight F).comp ((h : V →ₗ[F] V).lcomp F W) =
        homSpecialLinearRepresentation ρ (g, h)⁻¹ := by
      ext A x
      simp [homSpecialLinearRepresentation_apply]
    simpa only [he] using hufix (g, h)
  have hpure : ∃ (v : ⨂[F] (_ : Fin d), V) (ℓ : ⨂[F] (_ : Fin d), Dual F W),
      (∀ h, σd h v = v) ∧ (∀ g, τd g ℓ = ℓ) ∧
      Tensor.tensorPowerPairing A v ℓ ≠ 0 := by
    apply exists_nonzero_invariant_pair σd τd (Tensor.tensorPowerPairing A) z
    · exact hz
    · exact hfix
  obtain ⟨v, ℓ, hv, hℓ, hvℓ⟩ := hpure
  exact ⟨v, ℓ, hv, hℓ, hvℓ⟩

end AdelicBostConjecture.Geometry
