/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import AdelicBostConjecture.Adelic.Contraction.FiniteSpecht
public import AdelicBostConjecture.Adelic.Contraction.PairingBaseChange
public import AdelicBostConjecture.Adelic.Contraction.PairingNorm

/-!
# The actual adelic canonical pairing

The determinant embeddings, tensor functoriality, dual regrouping and evaluation
give the local contraction in Section 6 on the prescribed adelic bundles.
-/

@[expose] public section
noncomputable section

namespace AdelicBostConjecture.Adelic.Contraction

open Module ArakelovGeometry ArakelovGeometry.AdelicVectorBundle Specht OAI.Saxl
open AdelicBostConjecture.Geometry
open scoped TensorProduct

universe u v w wV wU

variable {K : Type u} [Field K] [CharZero K] {S : AdelicStructure.{u, v} K}
  {ι : Type w} [Fintype ι]
  (V : ι → AdelicVectorBundle.{wV} S)
  [hN : S.IsArchimedeanNormalized]
  [hcount : S.HasCommonCountableDenseSubfield] [hV : ∀ j, (V j).IsHermitian]

/-- The independent tensor of the actual determinant embeddings contracts on
every completed fibre. Its Archimedean factor maps are the proved isometries. -/
theorem tensor_projectiveDeterminantMap_norm_le {n : ℕ} {k : ι → ℕ}
    (hk : ∀ j, 0 < k j)
    (t : ∀ j, Tableau n (rectangle (finrank K (V j)) (k j)))
    (b : ∀ j, Basis (Fin (finrank K (K ⊗[ℤ] orbitLattice (t j)))) ℤ (orbitLattice (t j)))
    (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K]
      (⨂[K] j, (⨂[K] (_ : Fin (k j)), ⋀[K]^(finrank K (V j)) (V j)) ⊗[K]
        (K ⊗[ℤ] orbitLattice (t j)))) :
    (NormFamily.orthogonalTensor
      (fun j ↦ NormFamily.orthogonalTensor (fun _ : Fin n ↦ (V j).toNormFamily))).norm ω
      ((PiTensorProduct.map (fun j ↦ projectiveDeterminantMap (R := K) (M := V j) (hk j) (t j)
        (fun p ↦ congrFun (Module.rankAtStalk_eq_finrank_of_free
          (R := K) (M := V j)) p))).baseChange (S.ϕ ω).Completion z) ≤
    (NormFamily.orthogonalTensor
      (E := fun j ↦ (⨂[K] (_ : Fin (k j)), ⋀[K]^(finrank K (V j)) (V j)) ⊗[K]
        (K ⊗[ℤ] orbitLattice (t j)))
      (fun j ↦ (determinantSpechtBundle (V j) (k j) (t j) (b j)).toNormFamily)).norm ω z := by
  exact orthogonalTensor_map_norm_le_of_finite_le_infinite_eq
    (X := fun j ↦ (⨂[K] (_ : Fin (k j)), ⋀[K]^(finrank K (V j)) (V j)) ⊗[K]
      (K ⊗[ℤ] orbitLattice (t j)))
    (fun j ↦ (determinantSpechtBundle (V j) (k j) (t j) (b j)).toNormFamily)
    (fun j ↦ NormFamily.orthogonalTensor (fun _ : Fin n ↦ (V j).toNormFamily))
    (fun j ↦ projectiveDeterminantMap (R := K) (M := V j) (hk j) (t j)
      (fun p ↦ congrFun (Module.rankAtStalk_eq_finrank_of_free
        (R := K) (M := V j)) p)) ω
    (fun j x ↦ projectiveDeterminantMap_norm_le (V j) (hk j) (t j) (b j) ω x)
    (fun hω j x ↦ projectiveDeterminantMap_norm_infinite
      (V j) (hk j) (t j) (b j) ω hω x) z

/-- Dual regrouping carries the independent determinant embeddings into the
orthogonal tensor power of the dual norm without increasing the norm. -/
theorem dualDeterminantMap_norm_le {n : ℕ} {k : ι → ℕ}
    (hk : ∀ j, 0 < k j)
    (t : ∀ j, Tableau n (rectangle (finrank K (Dual K (V j))) (k j)))
    (ha : ∀ j (p : PrimeSpectrum K),
      Module.rankAtStalk (Dual K (V j)) p = finrank K (Dual K (V j)))
    (b : ∀ j, Basis (Fin (finrank K (K ⊗[ℤ] orbitLattice (t j)))) ℤ (orbitLattice (t j)))
    (ω : S.Ω) :
    let D := NormFamily.orthogonalTensor
      (E := fun j ↦ (⨂[K] (_ : Fin (k j)), ⋀[K]^(finrank K (Dual K (V j))) (Dual K (V j))) ⊗[K]
        (K ⊗[ℤ] orbitLattice (t j)))
      (fun j ↦ (determinantSpechtBundle ((V j).dualOfNormMeasurability)
        (k j) (t j) (b j)).toNormFamily)
    ∀ x, (NormFamily.orthogonalTensor (fun _ : Fin n ↦
      (NormFamily.orthogonalTensor (fun j ↦ (V j).toNormFamily)).dual)).norm ω
        ((Geometry.dualDeterminantMap (R := K) (fun j ↦ V j) hk t ha).baseChange
          (S.ϕ ω).Completion x) ≤ D.norm ω x := by
  intro D x
  let VD := fun j ↦ (V j).dualOfNormMeasurability
  let hVD : ∀ j, (VD j).IsHermitian := fun j ↦ (hV j).dual
  simp only [Geometry.dualDeterminantMap, LinearMap.baseChange_comp, LinearMap.comp_apply]
  exact (dualRegroupEquiv_norm_le (fun j ↦ (V j).toNormFamily) ω _).trans
    (tensor_projectiveDeterminantMap_norm_le VD hk t b ω x)

/-- This paper, equation (6.3).

The original-field canonical pairing contracts on every completed fibre
for the actual determinant–Specht source and the dual of the actual auxiliary
orthogonal tensor bundle. The sole metric premise is the induced norm on the inclusion. -/
theorem canonicalPairing_norm_le {n : ℕ} {k : ι → ℕ}
    (hk : ∀ j, 0 < k j)
    (t : ∀ j, Tableau n (rectangle (finrank K (Dual K (V j))) (k j)))
    (ha : ∀ j (p : PrimeSpectrum K),
      Module.rankAtStalk (Dual K (V j)) p = finrank K (Dual K (V j)))
    (b : ∀ j, Basis (Fin (finrank K (K ⊗[ℤ] orbitLattice (t j)))) ℤ (orbitLattice (t j)))
    (U : AdelicVectorBundle.{wU} S) [hU : U.IsHermitian]
    {l : ℕ} (hl : 0 < l) (v : Tableau n (rectangle (finrank K U) l))
    (hs : ∀ p : PrimeSpectrum K, Module.rankAtStalk U p = finrank K U)
    (bV : Basis (Fin (finrank K (K ⊗[ℤ] orbitLattice v))) ℤ (orbitLattice v))
    (i : U →ₗ[K] (⨂[K] j, V j))
    (hi : ∀ ω x, (orthogonalTensorOfNormMeasurability V).norm ω
      (i.baseChange (S.ϕ ω).Completion x) = U.norm ω x)
    (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K]
      ((⨂[K] (_ : Fin l), ⋀[K]^(finrank K U) U) ⊗[K] (K ⊗[ℤ] orbitLattice v))) :
    let D := NormFamily.orthogonalTensor
      (E := fun j ↦ (⨂[K] (_ : Fin (k j)), ⋀[K]^(finrank K (Dual K (V j))) (Dual K (V j))) ⊗[K]
        (K ⊗[ℤ] orbitLattice (t j)))
      (fun j ↦ (determinantSpechtBundle ((V j).dualOfNormMeasurability)
          (k j) (t j) (b j)).toNormFamily)
    D.dual.norm ω
      ((Geometry.canonicalPairing (R := K) (fun i ↦ V i) hk t ha hl v hs i).baseChange
        (S.ϕ ω).Completion z) ≤
        (determinantSpechtBundle U l v bV).norm ω z := by
  intro D
  let W := NormFamily.orthogonalTensor (fun j ↦ (V j).toNormFamily)
  let hW := NormFamily.orthogonalTensor_isHermitian (fun j ↦ (V j).toNormFamily)
  let T := NormFamily.orthogonalTensor (fun _ : Fin n ↦ W.dual)
  have hj := dualDeterminantMap_norm_le V hk t ha b ω
  let gz := (projectiveDeterminantMap (R := K) (M := U) hl v hs).baseChange (S.ϕ ω).Completion z
  have he := tensorPowerPairing_norm_le (ι := Fin n) U.toNormFamily W i ω (hi ω) gz
  have hd := dualMap_norm_le D T (Geometry.dualDeterminantMap (R := K) (fun i ↦ V i) hk t ha)
    ω hj ((Tensor.tensorPowerPairing i).baseChange (S.ϕ ω).Completion gz)
  have hg := projectiveDeterminantMap_norm_le U hl v bV ω z
  simp only [Geometry.canonicalPairing, LinearMap.baseChange_comp, LinearMap.comp_apply]
  exact hd.trans (he.trans hg)

end AdelicBostConjecture.Adelic.Contraction
