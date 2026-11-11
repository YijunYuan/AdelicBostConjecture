/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Adelic.Contraction.FiniteDeterminant
public import BostConjecture.Adelic.Specht.Bundle
public import ArakelovGeometry.AdelicVectorBundle.Tensor.Hermitian.InnerProduct

/-!
# Finite-place Specht contractions on completed fibres

The determinant-normalized lattice estimate uses the actual constant Specht
norm after cancelling the intermediate ground field.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Adelic.Contraction

open Module ArakelovGeometry Geometry Specht OAI.Saxl
open scoped TensorProduct

variable {K E : Type*} [Field K] [CharZero K] {S : AdelicStructure K}
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (ξ : NormFamily S E)
  (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
  (hξ : ξ.IsHermitian hN) {n k : ℕ}

set_option backward.isDefEq.respectTransparency false in
/-- The finite-place lattice estimate in the actual completed tensor and
Specht norms, in any frame of the completed vector space. -/
theorem orthogonal_freeLatticeMap_completed_le
    (hk : 0 < k) (t : Tableau n (rectangle (finrank K E) k))
    {ι : Type*} [Fintype ι] (c : Basis ι ℤ (orbitLattice t))
    (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (b : Basis (Fin (finrank K E)) (S.ϕ ω).Completion
      ((S.ϕ ω).Completion ⊗[K] E))
    (x : (S.ϕ ω).Completion ⊗[K] (K ⊗[ℤ] orbitLattice t)) :
    (NormFamily.orthogonalTensor (fun _ : Fin n => ξ) hN (fun _ => hξ)).norm ω
      ((tensorBaseChangeEquiv K (S.ϕ ω).Completion (fun _ : Fin n => E)).symm
        (freeLatticeMap hk t b
          (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ K (S.ϕ ω).Completion
            (S.ϕ ω).Completion (orbitLattice t) x))) ≤
      (ξ.determinant.norm ω
        ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion E (finrank K E)).symm
          (exteriorPower.ιMulti (S.ϕ ω).Completion (finrank K E) b))) ^ k *
        (latticeNormFamily S t c).norm ω x := by
  rw [NormFamily.orthogonalTensor_norm_of_finite _ hN _ ω hω,
    latticeNormFamily_norm_finite S t c ω hω, fibreBasisCoordinates_cancel]
  exact injective_freeLatticeMap_completed_le ξ ω hω hk t b c _

end BostConjecture.Adelic.Contraction
