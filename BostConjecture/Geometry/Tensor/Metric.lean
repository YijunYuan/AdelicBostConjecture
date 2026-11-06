/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Geometry.Tensor.Realization
public import BostConjecture.Tensor.Metric.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Orthonormal tensor coordinates

The algebraic tensor coordinates used for the determinant inclusion are
isometric coordinates when the original frame is orthonormal.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Geometry

open Module PiTensorProduct
open scoped TensorProduct

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {a n : ℕ}

/-- The canonical tensor coordinates compute the Hilbert tensor inner product. -/
theorem tensorCoordinates_inner (b : OrthonormalBasis (Fin a) ℂ M)
    (x y : ⨂[ℂ] (_ : Fin n), M) :
    (Tensor.hilbertCore (fun _ : Fin n => M)).inner x y =
      ∑ w, star (tensorCoordinates n b.toBasis x w) * tensorCoordinates n b.toBasis y w := by
  classical
  let : InnerProductSpace.Core ℂ (⨂[ℂ] (_ : Fin n), M) :=
    Tensor.hilbertCore (fun _ : Fin n => M)
  let hnorm := InnerProductSpace.Core.toNormedAddCommGroup
    (𝕜 := ℂ) (F := ⨂[ℂ] (_ : Fin n), M)
  let : SeminormedAddCommGroup (⨂[ℂ] (_ : Fin n), M) := hnorm.toSeminormedAddCommGroup
  let : InnerProductSpace ℂ (⨂[ℂ] (_ : Fin n), M) := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (⨂[ℂ] (_ : Fin n), M))
  let bT := Basis.piTensorProduct (fun _ : Fin n => b.toBasis)
  have hb : Orthonormal ℂ bT := by
    rw [orthonormal_iff_ite]
    intro w v
    change (Tensor.hilbertCore (fun _ : Fin n => M)).inner (bT w) (bT v) = _
    simp only [bT, Basis.piTensorProduct_apply, OrthonormalBasis.coe_toBasis,
      Tensor.hilbertCore_inner_tprod, finprod_eq_prod_of_fintype]
    by_cases h : w = v
    · subst v
      simp
    · rw [ite_eq_right h]
      obtain ⟨q, hq⟩ := Function.ne_iff.mp h
      exact Finset.prod_eq_zero (Finset.mem_univ q) (by simp [hq])
  have h := (bT.toOrthonormalBasis hb).repr.inner_map_map x y
  simpa [bT, tensorCoordinates, PiLp.inner_apply, RCLike.inner_apply, mul_comm] using h.symm

end BostConjecture.Geometry
