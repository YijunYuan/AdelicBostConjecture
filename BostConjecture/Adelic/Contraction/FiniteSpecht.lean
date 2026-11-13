/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Adelic.Contraction.FiniteDeterminant
public import BostConjecture.Adelic.Contraction.Archimedean
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

open Module ArakelovGeometry Specht OAI.Saxl
open BostConjecture.Geometry
open scoped TensorProduct

-- Use the canonical integer action when cancelling scalar extensions.
local instance {K : Type*} [Field K] {S : AdelicStructure K} (ω : S.Ω) :
    Algebra ℤ (S.ϕ ω).Completion := Ring.toIntAlgebra _

section Lattice

variable {K E : Type*} [Field K] [CharZero K] {S : AdelicStructure K}
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (ξ : NormFamily S E)
  [hN : S.IsArchimedeanNormalized]
  [hξ : ξ.IsHermitian] {n k : ℕ}

/-- The finite-place lattice estimate in the actual completed tensor and
Specht norms, in any frame of the completed vector space. -/
theorem orthogonal_freeLatticeMap_completed_le
    (hk : 0 < k) (t : Tableau n (rectangle (finrank K E) k))
    {ι : Type*} [Fintype ι] (c : Basis ι ℤ (orbitLattice t))
    (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (b : Basis (Fin (finrank K E)) (S.ϕ ω).Completion
      ((S.ϕ ω).Completion ⊗[K] E))
    (x : (S.ϕ ω).Completion ⊗[K] (K ⊗[ℤ] orbitLattice t)) :
    (NormFamily.orthogonalTensor (fun _ : Fin n => ξ)).norm ω
      ((tensorBaseChangeEquiv K (S.ϕ ω).Completion (fun _ : Fin n => E)).symm
        (freeLatticeMap hk t b
          (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ K (S.ϕ ω).Completion
            (S.ϕ ω).Completion (orbitLattice t) x))) ≤
      (ξ.determinant.norm ω
        ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion E (finrank K E)).symm
          (exteriorPower.ιMulti (S.ϕ ω).Completion (finrank K E) b))) ^ k *
        (latticeNormFamily S t c).norm ω x := by
  rw [NormFamily.orthogonalTensor_norm_of_finite _ ω hω,
    latticeNormFamily_norm_finite S t c ω hω, fibreBasisCoordinates_cancel]
  exact injective_freeLatticeMap_completed_le ξ ω hω hk t b c _

end Lattice

section Bundle

universe u v
variable {K : Type u} [Field K] [CharZero K] {S : AdelicStructure.{u, v} K}
  (V : AdelicVectorBundle S)
  [hN : S.IsArchimedeanNormalized]
  [hcount : S.HasCommonCountableDenseSubfield] [hV : V.IsHermitian]

/-- The existing determinant embedding contracts for the prescribed completed
norms at every non-Archimedean place, including trivial valuations. -/
theorem projectiveDeterminantMap_norm_finite {n k : ℕ} (hk : 0 < k)
    (t : Tableau n (rectangle (finrank K V) k))
    (c : Basis (Fin (finrank K (K ⊗[ℤ] orbitLattice t))) ℤ (orbitLattice t))
    (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (x : (S.ϕ ω).Completion ⊗[K]
      ((⨂[K] (_ : Fin k), ⋀[K]^(finrank K V) V) ⊗[K] (K ⊗[ℤ] orbitLattice t))) :
    (NormFamily.orthogonalTensor (fun _ : Fin n => V.toNormFamily)).norm ω
      ((projectiveDeterminantMap hk t
        (fun p => congrFun (Module.rankAtStalk_eq_finrank_of_free (R := K) (M := V)) p)).baseChange
          (S.ϕ ω).Completion x) ≤ (determinantSpechtBundle V k t c).norm ω x := by
  let b := (Module.finBasis (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] V)).reindex
    (finCongr Module.finrank_baseChange)
  let e := determinantTwistBaseChangeEquiv (R := K) (S := (S.ϕ ω).Completion)
    (M := V) (orbitLattice t) k (finrank K V)
  obtain ⟨z, hz⟩ := exists_determinantPower_tmul b (e x)
  have hx := e.eq_symm_apply.mpr hz
  rw [hx]
  change (NormFamily.orthogonalTensor _).norm ω
    ((projectiveDeterminantMap hk t _).baseChange (S.ϕ ω).Completion
      ((determinantTwistBaseChangeEquiv (R := K) (S := (S.ϕ ω).Completion) (M := V)
        (orbitLattice t) k (finrank K V)).symm _)) ≤ _
  refine (congrArg
    ((NormFamily.orthogonalTensor (fun _ : Fin n ↦ V.toNormFamily)).norm ω)
    (projectiveDeterminantMap_baseChange_generator hk t _ b z)).trans_le ?_
  have hn := orthogonal_freeLatticeMap_completed_le V.toNormFamily hk t c ω hω b
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ K (S.ϕ ω).Completion
      (S.ϕ ω).Completion (orbitLattice t)).symm z)
  rw [LinearEquiv.apply_symm_apply] at hn
  refine hn.trans_eq ?_
  change _ = (determinantSpechtBundle V k t c).norm ω
    ((determinantTwistBaseChangeEquiv (R := K) (S := (S.ϕ ω).Completion) (M := V)
      (orbitLattice t) k (finrank K V)).symm _)
  rw [determinantSpechtBundle_norm_tprod V t c ω]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The actual determinant–Specht embedding contracts at every place. -/
theorem projectiveDeterminantMap_norm_le {n k : ℕ} (hk : 0 < k)
    (t : Tableau n (rectangle (finrank K V) k))
    (c : Basis (Fin (finrank K (K ⊗[ℤ] orbitLattice t))) ℤ (orbitLattice t))
    (ω : S.Ω)
    (x : (S.ϕ ω).Completion ⊗[K]
      ((⨂[K] (_ : Fin k), ⋀[K]^(finrank K V) V) ⊗[K] (K ⊗[ℤ] orbitLattice t))) :
    (NormFamily.orthogonalTensor (fun _ : Fin n => V.toNormFamily)).norm ω
      ((projectiveDeterminantMap hk t
        (fun p => congrFun (Module.rankAtStalk_eq_finrank_of_free (R := K) (M := V)) p)).baseChange
          (S.ϕ ω).Completion x) ≤ (determinantSpechtBundle V k t c).norm ω x := by
  by_cases hω : ω ∈ S.Ωfin
  · exact projectiveDeterminantMap_norm_finite V hk t c ω hω x
  · exact (projectiveDeterminantMap_norm_infinite V hk t c ω hω x).le

end Bundle

end BostConjecture.Adelic.Contraction
