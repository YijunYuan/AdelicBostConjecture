/-
Copyright (c) 2026 The AxiomMath/Stacks contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AxiomMath/Stacks contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Determinant covariance of the alternating tensor vector

The alternating vector on `n → n` has the sign of a permutation as its coordinate and vanishes
at non-bijective indices. The Kronecker power of a square matrix acts on it by its determinant.

This is the eight-declaration dependency cone of `Matrix.sum_tensorPow_mul_altVec`, extracted
from AxiomMath/Stacks at revision `012108f61d7f92a6ffc35ec3f263b6da5d438125`:
<https://github.com/AxiomMath/Stacks/tree/012108f61d7f92a6ffc35ec3f263b6da5d438125>

Copyright and license: Apache-2.0; see the preserved Apache-2.0 license and
the accompanying provenance records for the upstream file hash and extraction
details.

## Source

Adapted from <https://github.com/AxiomMath/Stacks>, revision
`012108f61d7f92a6ffc35ec3f263b6da5d438125`.
Original source:
* `StacksFrontier.LinearAlgebra.Matrix.AlternatingTensorPower`.

The original declaration namespaces and license notices are retained, except for
project-specific adaptations documented in the project contribution records.
-/

@[expose] public section

open Equiv Finset

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] (R : Type*) [CommRing R]

/-- The alternating vector of the `#n`-fold tensor power of `R ^ n`, as a function on the index
type `n → n` of that tensor power: its coordinate at `f` is the sign of `f` if `f` is a
permutation, and `0` if it is not. -/
def altVec (f : n → n) : R :=
  ∑ σ : Equiv.Perm n, if (σ : n → n) = f then ((Equiv.Perm.sign σ : ℤ) : R) else 0

variable {R}

/-- A sum of coordinates against `Matrix.altVec` is a sum over the permutations. -/
theorem sum_mul_altVec (F : (n → n) → R) :
    ∑ g, F g * altVec R g = ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : R) * F (σ : n → n) := by
  simp only [altVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [Finset.sum_eq_single_of_mem (σ : n → n) (Finset.mem_univ _)
    (fun g _ hg ↦ by rw [ite_eq_right (Ne.symm hg), mul_zero]), ite_eq_left rfl, mul_comm]

/-- The coordinate of the alternating vector at a permutation `σ` is the sign of `σ`. -/
@[simp]
theorem altVec_coe_perm (σ : Equiv.Perm n) :
    altVec R (σ : n → n) = ((Equiv.Perm.sign σ : ℤ) : R) := by
  rw [altVec, Finset.sum_eq_single_of_mem σ (Finset.mem_univ _)
    (fun τ _ hτ ↦ ite_eq_right fun h ↦ hτ (Equiv.coe_fn_injective h)), ite_eq_left rfl]

/-- The alternating vector vanishes at an index which is not a permutation. -/
theorem altVec_eq_zero_of_not_bijective {f : n → n} (hf : ¬ Function.Bijective f) :
    altVec R f = 0 :=
  Finset.sum_eq_zero fun σ _ ↦ ite_eq_right fun h ↦ hf (by rw [← h]; exact σ.bijective)

/-- **Reading the rows of `u` along `f` multiplies the determinant by the coordinate of the
alternating vector at `f`.** -/
theorem det_submatrix_left (u : Matrix n n R) (f : n → n) :
    (u.submatrix f id).det = altVec R f * u.det := by
  by_cases hf : Function.Bijective f
  · obtain ⟨σ, rfl⟩ : ∃ σ : Equiv.Perm n, (σ : n → n) = f := ⟨Equiv.ofBijective f hf, rfl⟩
    rw [altVec_coe_perm, Matrix.det_permute]
  · rw [altVec_eq_zero_of_not_bijective hf, zero_mul]
    have hinj : ¬ Function.Injective f := fun h ↦ hf ⟨h, Finite.surjective_of_injective h⟩
    rw [Function.not_injective_iff] at hinj
    obtain ⟨i, j, hij, hne⟩ := hinj
    refine Matrix.det_zero_of_row_eq hne ?_
    funext k
    simp [Matrix.submatrix_apply, hij]

/-- The `#n`-fold Kronecker power of a square matrix, as a matrix indexed by the index type
`n → n` of the `#n`-fold tensor power of `R ^ n`. -/
def tensorPow (u : Matrix n n R) : Matrix (n → n) (n → n) R :=
  Matrix.of fun f g ↦ ∏ k, u (f k) (g k)

omit [DecidableEq n] in
/-- The `(f, g)` entry of `Matrix.tensorPow u` is `∏ k, u (f k) (g k)`. -/
@[simp]
theorem tensorPow_apply (u : Matrix n n R) (f g : n → n) :
    tensorPow u f g = ∏ k, u (f k) (g k) :=
  rfl

/-- **The Kronecker power of `u` carries the alternating vector to `det u` times itself**, acting
on coordinates from the left. -/
theorem sum_tensorPow_mul_altVec (u : Matrix n n R) (f : n → n) :
    ∑ g, tensorPow u f g * altVec R g = altVec R f * u.det := by
  rw [sum_mul_altVec, ← det_submatrix_left u f, ← Matrix.det_transpose (u.submatrix f id),
    Matrix.det_apply']
  exact Finset.sum_congr rfl fun σ _ ↦ by
    simp [Matrix.transpose_apply, Matrix.submatrix_apply]

end Matrix

end
