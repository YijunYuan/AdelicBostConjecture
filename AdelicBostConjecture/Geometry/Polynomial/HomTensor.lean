/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import AdelicBostConjecture.Tensor.Dual.Hom
public import AdelicBostConjecture.Geometry.Polynomial.Tensor
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# The Hom polynomial tensor in the canonical pairing grouping

This consumes the finite-projective Hom-dual equivalence. Polynomial evaluation
is exactly the linearized existing tensor-power pairing, and pullback is the
independent source/dual-target action on the regrouped tensor.
-/

@[expose] public section

noncomputable section

namespace AdelicBostConjecture.Geometry

open Module PiTensorProduct InvariantTheory
open scoped TensorProduct

variable {F V W : Type*} [Field F] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [FiniteDimensional F V] [FiniteDimensional F W]
  {d : ℕ}

/-- The actual polynomial quotient evaluates as the canonical tensor pairing. -/
theorem polynomialEval_homDualTensorEquiv (A : V →ₗ[F] W)
    (z : (⨂[F] (_ : Fin d), V) ⊗[F] (⨂[F] (_ : Fin d), Dual F W)) :
    polynomialEval A (polynomialTensorMap F (V →ₗ[F] W) d
      (Tensor.homDualTensorEquiv F V W z)) =
        TensorProduct.lift (Tensor.tensorPowerPairing A) z := by
  induction z using TensorProduct.inductionOn with
  | tmul v ℓ =>
    rw [polynomialEval_tensorMap, TensorProduct.lift.tmul]
    change PiTensorProduct.dualDistrib _ _ = _
    exact Tensor.homDualTensorEquiv_evaluation F V W A v ℓ
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Pullback on every regrouped tensor is the independent factor action. -/
theorem homDualTensorEquiv_naturality (h : V →ₗ[F] V) (g : W →ₗ[F] W)
    (z : (⨂[F] (_ : Fin d), V) ⊗[F] (⨂[F] (_ : Fin d), Dual F W)) :
    Tensor.homDualTensorEquiv F V W
      (TensorProduct.map (PiTensorProduct.map fun _ => h)
        (PiTensorProduct.map fun _ => g.dualMap) z) =
      PiTensorProduct.map (fun _ => ((g.compRight F).comp (h.lcomp F W)).dualMap)
        (Tensor.homDualTensorEquiv F V W z) := by
  induction z using TensorProduct.inductionOn with
  | tmul v ℓ => simpa only [TensorProduct.map_tmul] using
      Tensor.homDualTensorEquiv_map F V W h g v ℓ
  | add x y hx hy => simp only [map_add, hx, hy]

/-- A nonzero evaluation of an actual Hom polynomial supplies a tensor with
nonzero canonical pairing, preserving all independent pullback invariances. -/
theorem exists_regrouped_hom_tensor
    (A : V →ₗ[F] W) (u : ⨂[F] (_ : Fin d), Dual F (V →ₗ[F] W))
    (hu : polynomialEval A (polynomialTensorMap F (V →ₗ[F] W) d u) ≠ 0) :
    ∃ z : (⨂[F] (_ : Fin d), V) ⊗[F] (⨂[F] (_ : Fin d), Dual F W),
      Tensor.homDualTensorEquiv F V W z = u ∧
      TensorProduct.lift (Tensor.tensorPowerPairing A) z ≠ 0 ∧
      ∀ (h : V →ₗ[F] V) (g : W →ₗ[F] W),
        PiTensorProduct.map (fun _ => ((g.compRight F).comp (h.lcomp F W)).dualMap) u = u →
        TensorProduct.map (PiTensorProduct.map fun _ => h)
          (PiTensorProduct.map fun _ => g.dualMap) z = z := by
  obtain ⟨z, rfl⟩ := (Tensor.homDualTensorEquiv F V W).surjective u
  refine ⟨z, rfl, ?_, ?_⟩
  · rwa [polynomialEval_homDualTensorEquiv] at hu
  · intro h g hg
    apply (Tensor.homDualTensorEquiv F V W).injective
    rwa [homDualTensorEquiv_naturality]

end AdelicBostConjecture.Geometry
