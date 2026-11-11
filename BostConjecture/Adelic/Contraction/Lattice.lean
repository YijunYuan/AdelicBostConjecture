/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Geometry.Tensor.FreeEmbedding
public import ArakelovGeometry.Analysis.Tensor.Basic
import Mathlib.Analysis.Normed.Group.Ultra

/-!
# Integral Specht word estimates

The rectangular orbit lattice is supported on words with the same letter
content. At a finite place, its integral coefficients give the required
epsilon-tensor norm estimate in any integral lattice basis.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Adelic.Contraction

open Module Specht OAI.Saxl
open scoped TensorProduct

variable {n a k : ℕ}

/-- A diagonal change of letters multiplies each word coefficient by its
letter-weight product. -/
theorem wordTensorAction_diagonal_apply (r : Fin a → ℝ)
    (x : (Fin n → Fin a) → ℝ) (w : Fin n → Fin a) :
    wordTensorAction n (Matrix.diagonal r) x w = (∏ q, r (w q)) * x w := by
  classical
  change (∑ v, (∏ q, Matrix.diagonal r (w q) (v q)) * x v) = _
  rw [Finset.sum_eq_single w]
  · simp
  · intro v _ hv
    obtain ⟨q, hq⟩ : ∃ q, w q ≠ v q := by
      by_contra! h
      exact hv (funext fun q ↦ (h q).symm)
    have hp : (∏ q, Matrix.diagonal r (w q) (v q)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ q) (by simp [Matrix.diagonal, hq])
    rw [hp, zero_mul]
  · intro h
    exact (h (Finset.mem_univ w)).elim

/-- Every nonzero coefficient of the actual integral rectangular orbit
lattice has the determinant letter weight. No choice of standard basis or
integral straightening theorem is needed. -/
theorem prod_weights_eq_of_orbitLattice_ne_zero (hk : 0 < k)
    (t : Tableau n (rectangle a k)) (x : orbitLattice t)
    (w : Fin n → Fin a)
    (hx : x.val ((rectangleAlphabetEquiv hk).symm w) ≠ 0) (r : Fin a → ℝ) :
    (∏ q, r (w q)) = (∏ i, r i) ^ k := by
  let y : (Fin n → Fin a) → ℝ :=
    fun v ↦ (x.val ((rectangleAlphabetEquiv hk).symm v) : ℝ)
  have hy : y ∈ Submodule.span ℝ (Set.range fun z : orbitLattice t ↦
      fun v ↦ (z.val ((rectangleAlphabetEquiv hk).symm v) : ℝ)) :=
    Submodule.subset_span ⟨x, rfl⟩
  have h := congrFun (wordTensorAction_of_mem_span hk t (Matrix.diagonal r) hy) w
  rw [wordTensorAction_diagonal_apply, Matrix.det_diagonal] at h
  change (∏ q, r (w q)) * y w = (∏ i, r i) ^ k * y w at h
  exact mul_right_cancel₀ (by dsimp only [y]; exact_mod_cast hx : y w ≠ 0) h

end BostConjecture.Adelic.Contraction
