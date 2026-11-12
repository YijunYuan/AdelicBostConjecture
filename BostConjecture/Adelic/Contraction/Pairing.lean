/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Adelic.Contraction.FiniteSpecht
public import BostConjecture.Adelic.Contraction.PairingBaseChange
public import BostConjecture.Adelic.Contraction.PairingNorm

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
  [hN : S.IsArchimedeanNormalized]
  [hcount : S.HasCommonCountableDenseSubfield] (hV : ∀ j, (V j).IsHermitian)

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
      (fun j ↦ NormFamily.orthogonalTensor (fun _ : Fin n ↦ (V j).toNormFamily))).norm ω
      ((PiTensorProduct.map (fun j ↦ projectiveDeterminantMap (hk j) (t j)
        (fun p ↦ congrFun (Module.rankAtStalk_eq_finrank_of_free
          (R := K) (M := E j)) p))).baseChange (S.ϕ ω).Completion z) ≤
    (orthogonalTensorOfMeasurableBase
      (fun j ↦ determinantSpechtBundle (V j) (k j) (t j) (b j))).norm ω z := by
  apply orthogonalTensor_map_norm_le_of_finite_le_infinite_eq
    (fun j ↦ (determinantSpechtBundle (V j) (k j) (t j) (b j)).toNormFamily)
    (fun j ↦ NormFamily.orthogonalTensor (fun _ : Fin n ↦ (V j).toNormFamily))
    (fun j ↦ determinantSpechtBundle_isHermitian (V j) (k j) (t j) (b j))
    (fun j ↦ NormFamily.orthogonalTensor_isHermitian _)
  · exact fun j x ↦ projectiveDeterminantMap_norm_le
      (V j) (hV j) (hk j) (t j) (b j) ω x
  · exact fun hω j x ↦ projectiveDeterminantMap_norm_infinite
      (V j) (hV j) (hk j) (t j) (b j) ω hω x

/-- The original-field canonical pairing contracts on every completed fibre
for the actual determinant–Specht source and the dual of the actual auxiliary
orthogonal tensor bundle. The sole metric premise is the induced norm on the inclusion. -/
theorem canonicalPairing_norm_le {n : ℕ} {k : ι → ℕ}
    (hk : ∀ j, 0 < k j)
    (t : ∀ j, Tableau n (rectangle (finrank K (Dual K (E j))) (k j)))
    (ha : ∀ j (p : PrimeSpectrum K),
      Module.rankAtStalk (Dual K (E j)) p = finrank K (Dual K (E j)))
    (b : ∀ j, Basis (Fin (finrank K (K ⊗[ℤ] orbitLattice (t j)))) ℤ (orbitLattice (t j)))
    {F : Type u} [AddCommGroup F] [Module K F] [FiniteDimensional K F]
    (U : AdelicVectorBundle S F) (hU : U.IsHermitian)
    {l : ℕ} (hl : 0 < l) (v : Tableau n (rectangle (finrank K F) l))
    (hs : ∀ p : PrimeSpectrum K, Module.rankAtStalk F p = finrank K F)
    (bV : Basis (Fin (finrank K (K ⊗[ℤ] orbitLattice v))) ℤ (orbitLattice v))
    (i : F →ₗ[K] (⨂[K] j, E j))
    (hi : ∀ ω x, (orthogonalTensorOfMeasurableBase V).norm ω
      (i.baseChange (S.ϕ ω).Completion x) = U.norm ω x)
    (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K]
      ((⨂[K] (_ : Fin l), ⋀[K]^(finrank K F) F) ⊗[K] (K ⊗[ℤ] orbitLattice v))) :
    let D := orthogonalTensorOfMeasurableBase
      (fun j ↦ determinantSpechtBundle ((V j).dualOfMeasurableBase)
          (k j) (t j) (b j))
    (D.dualOfMeasurableBase).norm ω
      ((Geometry.canonicalPairing E hk t ha hl v hs i).baseChange (S.ϕ ω).Completion z) ≤
        (determinantSpechtBundle U l v bV).norm ω z := by
  let VD := fun j ↦ (V j).dualOfMeasurableBase
  let hVD : ∀ j, (VD j).IsHermitian := fun j ↦ (hV j).dual
  let D := orthogonalTensorOfMeasurableBase
    (fun j ↦ determinantSpechtBundle (VD j) (k j) (t j) (b j))
  let W := NormFamily.orthogonalTensor (fun j ↦ (V j).toNormFamily)
  let hW := NormFamily.orthogonalTensor_isHermitian (fun j ↦ (V j).toNormFamily)
  let T := NormFamily.orthogonalTensor (fun _ : Fin n ↦ W.dual)
  have hj (x) : T.norm ω
      ((Geometry.dualDeterminantMap E hk t ha).baseChange (S.ϕ ω).Completion x) ≤
        D.norm ω x := by
    simp only [Geometry.dualDeterminantMap, LinearMap.baseChange_comp, LinearMap.comp_apply]
    exact (dualRegroupEquiv_norm_le (fun j ↦ (V j).toNormFamily) hV ω _).trans
      (tensor_projectiveDeterminantMap_norm_le VD hVD hk t b ω x)
  change D.toNormFamily.dual.norm ω
    ((Geometry.canonicalPairing E hk t ha hl v hs i).baseChange (S.ϕ ω).Completion z) ≤ _
  let gz := (projectiveDeterminantMap hl v hs).baseChange (S.ϕ ω).Completion z
  have he := tensorPowerPairing_norm_le U.toNormFamily W hU hW i ω (hi ω) gz
  have hd := dualMap_norm_le D.toNormFamily T (Geometry.dualDeterminantMap E hk t ha)
    ω hj ((Tensor.tensorPowerPairing i).baseChange (S.ϕ ω).Completion gz)
  have hg := projectiveDeterminantMap_norm_le U hU hl v bV ω z
  simp only [Geometry.canonicalPairing, LinearMap.baseChange_comp, LinearMap.comp_apply]
  exact hd.trans (he.trans hg)

end BostConjecture.Adelic.Contraction
