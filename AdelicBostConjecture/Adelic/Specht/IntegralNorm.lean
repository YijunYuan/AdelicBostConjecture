/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.Analysis.NormedSpace.CoordinateNorm
public import Mathlib.LinearAlgebra.TensorProduct.Basis

import Mathlib.Analysis.Normed.Ring.Ultra

/-!
# Integral maps contract non-Archimedean lattice norms

The maximum norm defined by an integral basis is independent of that basis.
More generally, scalar extension of every integral linear map contracts these
norms. This includes trivial valuations and supplies the finite-place Specht
action and contraction estimates.
-/

@[expose] public section
noncomputable section

namespace AdelicBostConjecture.Specht

open Module ArakelovGeometry
open scoped TensorProduct

variable {L M N : Type*} [NormedField L] [IsUltrametricDist L]
  [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N]
  {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Every integral linear map contracts the scalar-extended lattice max norms. -/
theorem integralMap_norm_le (b : Basis ι ℤ M) (c : Basis κ ℤ N)
    (f : M →ₗ[ℤ] N) (x : L ⊗[ℤ] M) :
    ‖(c.baseChange L).equivFun (f.baseChange L x)‖ ≤ ‖(b.baseChange L).equivFun x‖ := by
  classical
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro j
  let ℓ := ((c.baseChange L).coord j).comp (f.baseChange L)
  have hb : ‖fun i => ℓ ((b.baseChange L) i)‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    simpa [ℓ, Basis.coord_apply, Basis.baseChange_apply, Basis.baseChange_repr_tmul]
      using (IsUltrametricDist.norm_intCast_le_one (R := L) (c.repr (f (b i)) j))
  exact (norm_linearMap_apply_le_basis_max (b.baseChange L) ℓ x).trans
    (mul_le_of_le_one_left (norm_nonneg _) hb)

/-- Integral isomorphisms preserve the lattice maximum norms at every
non-Archimedean field, including the trivial absolute value. -/
theorem integralEquiv_norm (b : Basis ι ℤ M) (c : Basis κ ℤ N)
    (f : M ≃ₗ[ℤ] N) (x : L ⊗[ℤ] M) :
    ‖(c.baseChange L).equivFun (f.toLinearMap.baseChange L x)‖ =
      ‖(b.baseChange L).equivFun x‖ := by
  apply le_antisymm (integralMap_norm_le b c f.toLinearMap x)
  have h := integralMap_norm_le c b f.symm.toLinearMap (f.toLinearMap.baseChange L x)
  have he : f.symm.toLinearMap.baseChange L (f.toLinearMap.baseChange L x) = x := by
    clear h
    induction x using TensorProduct.inductionOn with
    | tmul r x => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  simpa only [he] using h

/-- This paper, Section 2.6, basis independence of (2.9).

The maximum norm is independent of the chosen integral basis of a lattice. -/
theorem integralBasis_norm_eq (b : Basis ι ℤ M) (c : Basis κ ℤ M)
    (x : L ⊗[ℤ] M) :
    ‖(b.baseChange L).equivFun x‖ = ‖(c.baseChange L).equivFun x‖ := by
  simpa using integralEquiv_norm c b (LinearEquiv.refl ℤ M) x

end AdelicBostConjecture.Specht
