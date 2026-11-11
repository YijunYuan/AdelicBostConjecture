/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Adelic.Contraction.FiniteSpecht
public import BostConjecture.Adelic.Contraction.PairingBaseChange
public import ArakelovGeometry.AdelicVectorBundle.Degree.Supermodular

/-!
# The actual adelic canonical pairing

The determinant embeddings, tensor functoriality, dual regrouping and evaluation
give the local contraction in Section 6 on the prescribed adelic bundles.
-/

@[expose] public section
noncomputable section

namespace BostConjecture.Adelic.Contraction

open Module ArakelovGeometry ArakelovGeometry.AdelicVectorBundle Specht OAI.Saxl
open BostConjecture.Geometry
open scoped TensorProduct

universe u v w

variable {K : Type u} [Field K] [CharZero K] {S : AdelicStructure.{u, v} K}
  {ι : Type w} [Fintype ι]
  {E : ι → Type u} [∀ j, AddCommGroup (E j)] [∀ j, Module K (E j)]
  [∀ j, FiniteDimensional K (E j)]
  (V : ∀ j, AdelicVectorBundle S (E j))
  (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
  (hcount : S.HasCommonCountableDenseSubfield) (hV : ∀ j, (V j).IsHermitian hN)

/-- The independent tensor of the actual determinant embeddings contracts on
every completed fibre. Its Archimedean factor maps are the proved isometries. -/
theorem tensor_projectiveDeterminantMap_norm_le {n : ℕ} {k : ι → ℕ}
    (hk : ∀ j, 0 < k j)
    (t : ∀ j, Tableau n (rectangle (finrank K (E j)) (k j)))
    (b : ∀ j, Basis (Fin (finrank K (K ⊗[ℤ] orbitLattice (t j)))) ℤ (orbitLattice (t j)))
    (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K]
      (⨂[K] j, (⨂[K] (_ : Fin (k j)), ⋀[K]^(finrank K (E j)) (E j)) ⊗[K]
        (K ⊗[ℤ] orbitLattice (t j)))) :
    (NormFamily.orthogonalTensor
      (fun j ↦ NormFamily.orthogonalTensor (fun _ : Fin n ↦ (V j).toNormFamily)
        hN (fun _ ↦ hV j)) hN
      (fun _ ↦ NormFamily.orthogonalTensor_isHermitian _ _ _)).norm ω
      ((PiTensorProduct.map (fun j ↦ projectiveDeterminantMap (hk j) (t j)
        (fun p ↦ congrFun (Module.rankAtStalk_eq_finrank_of_free
          (R := K) (M := E j)) p))).baseChange (S.ϕ ω).Completion z) ≤
    (orthogonalTensorOfMeasurableBase
      (fun j ↦ determinantSpechtBundle (V j) hN hcount (k j) (t j) (b j))
      (Or.inr hcount) hN
      (fun j ↦ determinantSpechtBundle_isHermitian
        (V j) hN hcount (k j) (t j) (b j))).norm ω z := by
  apply orthogonalTensor_map_norm_le_of_finite_le_infinite_eq
    (fun j ↦ (determinantSpechtBundle (V j) hN hcount (k j) (t j) (b j)).toNormFamily)
    (fun j ↦ NormFamily.orthogonalTensor (fun _ : Fin n ↦ (V j).toNormFamily)
      hN (fun _ ↦ hV j)) hN
    (fun j ↦ determinantSpechtBundle_isHermitian (V j) hN hcount (k j) (t j) (b j))
    (fun j ↦ NormFamily.orthogonalTensor_isHermitian _ _ _)
  · exact fun j x ↦ projectiveDeterminantMap_norm_le
      (V j) hN hcount (hV j) (hk j) (t j) (b j) ω x
  · exact fun hω j x ↦ projectiveDeterminantMap_norm_infinite
      (V j) hN hcount (hV j) (hk j) (t j) (b j) ω hω x

end BostConjecture.Adelic.Contraction
