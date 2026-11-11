/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Adelic.Specht.Bundle
public import BostConjecture.Adelic.Specht.IntegralNorm
public import BostConjecture.Arithmetic.Specht.Representation

/-!
# Isometries of the constant Specht norm family

The integral symmetric-group action preserves the completed norms: it is an
integral lattice automorphism at finite places and permutes the orthonormal
word coordinates at infinite places. The norm family is also independent of
the chosen integral lattice basis.
-/

@[expose] public section
noncomputable section

namespace BostConjecture.Specht

open Module ArakelovGeometry
open scoped TensorProduct

variable {K : Type*} [Field K] [CharZero K] (S : AdelicStructure K)
  {n : ℕ} {μ : YoungDiagram} (t : OAI.Saxl.Tableau n μ)
  {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- All integral bases define the same actual completed Specht norms. -/
theorem latticeNormFamily_basis_independent (b : Basis ι ℤ (orbitLattice t))
    (c : Basis κ ℤ (orbitLattice t)) (ω : S.Ω)
    (x : (S.ϕ ω).Completion ⊗[K] (K ⊗[ℤ] orbitLattice t)) :
    (latticeNormFamily S t b).norm ω x = (latticeNormFamily S t c).norm ω x := by
  by_cases hω : ω ∈ S.Ωinf
  · rw [latticeNormFamily_norm_infinite S t b ω hω,
      latticeNormFamily_norm_infinite S t c ω hω]
  · have hf : ω ∈ S.Ωfin := not_not.mp hω
    letI : IsUltrametricDist (S.ϕ ω).Completion :=
      IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
        (S.norm_add_le_max_of_finite ω hf)
    rw [latticeNormFamily_norm_finite S t b ω hf,
      latticeNormFamily_norm_finite S t c ω hf,
      fibreBasisCoordinates_cancel, fibreBasisCoordinates_cancel]
    exact integralBasis_norm_eq b c _

/-- Position permutations preserve the actual finite and infinite fibre norms. -/
theorem latticeNormFamily_orbitAction (b : Basis ι ℤ (orbitLattice t))
    (g : Equiv.Perm (Fin n)) (ω : S.Ω)
    (x : (S.ϕ ω).Completion ⊗[K] (K ⊗[ℤ] orbitLattice t)) :
    (latticeNormFamily S t b).norm ω
      (((orbitAction t g).baseChange K).baseChange (S.ϕ ω).Completion x) =
      (latticeNormFamily S t b).norm ω x := by
  classical
  by_cases hω : ω ∈ S.Ωinf
  · simp_rw [latticeNormFamily_norm_infinite S t b ω hω,
      fibreWordCoordinates_cancel, fibreOrbitAction_cancel, wordCoordinates_orbitAction]
    congr 1
    exact (Equiv.arrowCongr g.symm (Equiv.refl (Fin (μ.colLen 0)))).sum_comp
      (fun w => ‖wordCoordinates (S.ϕ ω).Completion t
        (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ K
          (S.ϕ ω).Completion (S.ϕ ω).Completion (orbitLattice t) x) w‖ ^ 2)
  · have hf : ω ∈ S.Ωfin := not_not.mp hω
    letI : IsUltrametricDist (S.ϕ ω).Completion :=
      IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
        (S.norm_add_le_max_of_finite ω hf)
    rw [latticeNormFamily_norm_finite S t b ω hf,
      latticeNormFamily_norm_finite S t b ω hf,
      fibreBasisCoordinates_cancel, fibreBasisCoordinates_cancel, fibreOrbitAction_cancel]
    let ρ := Arithmetic.Specht.integralRepresentation t
    exact integralEquiv_norm b b (LinearEquiv.ofBijective (ρ g) (ρ.apply_bijective g)) _

end BostConjecture.Specht
