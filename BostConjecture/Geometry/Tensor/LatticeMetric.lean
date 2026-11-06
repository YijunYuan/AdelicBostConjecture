/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Geometry.Tensor.Metric
public import BostConjecture.Geometry.Tensor.FreeEmbedding

/-!
# The local lattice realization and its Hermitian form

The complex form is the restriction of the orthonormal word-coordinate form
along the checked integral complexification. The actual tensor realization
preserves it in every orthonormal frame.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Geometry

open Module PiTensorProduct
open scoped TensorProduct

variable {n : ℕ} {μ : YoungDiagram}

/-- The complexified lattice has the restricted orthonormal word metric. -/
@[instance_reducible]
def latticeComplexCore (t : OAI.Saxl.Tableau n μ) :
    InnerProductSpace.Core ℂ (ℂ ⊗[ℤ] Specht.orbitLattice t) := by
  let e := (WithLp.linearEquiv 2 ℂ ((Fin n → Fin (μ.colLen 0)) → ℂ)).symm.toLinearMap ∘ₗ
    Specht.complexification t
  let hnorm := NormedAddCommGroup.induced _ _ e
    ((WithLp.linearEquiv 2 ℂ _).symm.injective.comp (Specht.complexification_injective t))
  let : SeminormedAddCommGroup (ℂ ⊗[ℤ] Specht.orbitLattice t) :=
    hnorm.toSeminormedAddCommGroup
  let := InnerProductSpace.induced e
  exact InnerProductSpace.toCore

/-- The complex lattice form is the usual coefficient Gram sum. -/
theorem latticeComplexCore_inner (t : OAI.Saxl.Tableau n μ)
    (x y : ℂ ⊗[ℤ] Specht.orbitLattice t) :
    (latticeComplexCore t).inner x y =
      ∑ w, star (Specht.complexification t x w) * Specht.complexification t y w := by
  change inner ℂ ((WithLp.linearEquiv 2 ℂ _).symm (Specht.complexification t x))
    ((WithLp.linearEquiv 2 ℂ _).symm (Specht.complexification t y)) = _
  simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]

/-- On integral vectors the complex form is the integer Gram form. -/
theorem latticeComplexCore_inner_integral (t : OAI.Saxl.Tableau n μ)
    (x y : Specht.orbitLattice t) :
    (latticeComplexCore t).inner (1 ⊗ₜ[ℤ] x) (1 ⊗ₜ[ℤ] y) =
      (∑ w, (x.val w * y.val w : ℤ) : ℂ) := by
  simp [latticeComplexCore_inner, Specht.complexification_tmul, Specht.complexCast]

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {a k : ℕ}

/-- The actual lattice realization in an orthonormal frame preserves the Hermitian form. -/
theorem freeLatticeMap_inner (hk : 0 < k) (t : OAI.Saxl.Tableau n (Specht.rectangle a k))
    (b : OrthonormalBasis (Fin a) ℂ M) (x y : ℂ ⊗[ℤ] Specht.orbitLattice t) :
    (Tensor.hilbertCore (fun _ : Fin n => M)).inner
      (freeLatticeMap hk t b.toBasis x) (freeLatticeMap hk t b.toBasis y) =
      (latticeComplexCore t).inner x y := by
  have h (z : ℂ ⊗[ℤ] Specht.orbitLattice t) :
      tensorCoordinates n b.toBasis (freeLatticeMap hk t b.toBasis z) =
        fun w => Specht.complexification t z ((Specht.rectangleAlphabetEquiv hk).symm w) := by
    induction z using TensorProduct.inductionOn with
    | tmul r z =>
      rw [freeLatticeMap_tmul, map_smul, LinearEquiv.apply_symm_apply,
        Specht.complexification_tmul]
      rfl
    | add z w hz hw =>
      ext v
      simp only [map_add, hz, hw, Pi.add_apply]
  rw [tensorCoordinates_inner, h x, h y, latticeComplexCore_inner]
  exact (Specht.rectangleAlphabetEquiv hk).symm.sum_comp
    (fun w => star (Specht.complexification t x w) * Specht.complexification t y w)

end BostConjecture.Geometry
