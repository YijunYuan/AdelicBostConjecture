/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import AdelicBostConjecture.Specht.Lattice.Covariance
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis

/-!
# Rectangular Specht vectors in tensor powers

The canonical tensor basis transports the word-coordinate matrix action to
the actual tensor-power functor. Rectangular determinant covariance then
holds in tensor powers of any finite free module with a chosen basis.
-/

@[expose] public section

noncomputable section

namespace AdelicBostConjecture.Geometry

open Module PiTensorProduct
open scoped TensorProduct

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {n a k : ℕ}

/-- Coordinates in the canonical tensor basis associated to a finite basis. -/
def tensorCoordinates (n : ℕ) (b : Basis (Fin a) R M) :
    (⨂[R] (_ : Fin n), M) ≃ₗ[R] ((Fin n → Fin a) → R) :=
  (Basis.piTensorProduct (fun _ : Fin n => b)).equivFun

@[simp]
theorem tensorCoordinates_tprod (b : Basis (Fin a) R M) (v : Fin n → M) :
    tensorCoordinates n b (tprod R v) = fun w => ∏ q, b.repr (v q) (w q) := by
  ext w
  exact Basis.piTensorProduct_repr_tprod_apply (fun _ : Fin n => b) v w

/-- The actual tensor-power functor is the checked word action in tensor coordinates. -/
theorem tensorCoordinates_map (b : Basis (Fin a) R M) (c : Basis (Fin a) R N)
    (f : M →ₗ[R] N)
    (z : ⨂[R] (_ : Fin n), M) :
    tensorCoordinates n c (PiTensorProduct.map (fun _ => f) z) =
      Specht.wordTensorAction n (LinearMap.toMatrix b c f) (tensorCoordinates n b z) := by
  classical
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    simp only [map_smul, map_tprod, tensorCoordinates_tprod]
    congr 1
    rw [Specht.wordTensorAction_prod]
    funext w
    apply Finset.prod_congr rfl
    exact fun q hq => congrFun (LinearMap.toMatrix_mulVec_repr b c f (v q)).symm (w q)
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Rectangular orbit-lattice vectors have determinant covariance in actual tensor powers. -/
theorem map_tensorCoordinates_symm_of_mem_span (hk : 0 < k)
    (t : OAI.Saxl.Tableau n (Specht.rectangle a k))
    (b : Basis (Fin a) R M) (c : Basis (Fin a) R N) (f : M →ₗ[R] N)
    {x : (Fin n → Fin a) → R}
    (hx : x ∈ Submodule.span R (Set.range fun y : Specht.orbitLattice t =>
      fun w => (y.val ((Specht.rectangleAlphabetEquiv hk).symm w) : R))) :
    PiTensorProduct.map (fun _ => f) ((tensorCoordinates n b).symm x) =
      (LinearMap.toMatrix b c f).det ^ k • (tensorCoordinates n c).symm x := by
  apply (tensorCoordinates n c).injective
  rw [tensorCoordinates_map, LinearEquiv.apply_symm_apply, map_smul,
    LinearEquiv.apply_symm_apply]
  exact Specht.wordTensorAction_of_mem_span hk t _ hx

end AdelicBostConjecture.Geometry
