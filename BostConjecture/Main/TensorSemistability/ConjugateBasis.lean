/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic.Positivity.Finset

/-!
# Orthonormal bases transported by conjugate-linear isometries

A conjugate-linear isometry transports orthonormal bases between conjugate
complex fibers. The resulting formulas compare projections and partial traces.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Balanced

open scoped InnerProductSpace

variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℂ U]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {ι : Type*} [Fintype ι]

/-- Transport an orthonormal basis through an actual conjugate-linear isometry. -/
def conjugateOrthonormalBasis (e : U ≃ₗ⋆[ℂ] V)
    (he : ∀ x y, inner ℂ (e x) (e y) = star (inner ℂ x y))
    (b : OrthonormalBasis ι ℂ U) : OrthonormalBasis ι ℂ V := by
  classical
  refine OrthonormalBasis.mk (v := fun i => e (b i)) ?_ ?_
  · rw [orthonormal_iff_ite]
    intro i j
    rw [he, b.inner_eq_ite]
    split_ifs <;> simp
  · intro y _
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← b.sum_repr' x, map_sum]
    apply Submodule.sum_mem
    intro i _
    rw [map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

@[simp]
theorem conjugateOrthonormalBasis_apply (e : U ≃ₗ⋆[ℂ] V)
    (he : ∀ x y, inner ℂ (e x) (e y) = star (inner ℂ x y))
    (b : OrthonormalBasis ι ℂ U) (i : ι) :
    conjugateOrthonormalBasis e he b i = e (b i) := by
  simp only [conjugateOrthonormalBasis, OrthonormalBasis.coe_mk]

end BostConjecture.Balanced
