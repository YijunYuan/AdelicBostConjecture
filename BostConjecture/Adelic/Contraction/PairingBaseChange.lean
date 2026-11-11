/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Geometry.Contraction.BaseChange
public import ArakelovGeometry.AdelicVectorBundle.Tensor.PairMap
public import ArakelovGeometry.AdelicVectorBundle.Tensor.Hermitian.Dual.Basic
public import ArakelovGeometry.AdelicVectorBundle.Dual.Map

/-!
# Completed tensor and evaluation contractions

The canonical tensor pairing is evaluation into the bidual followed by the
transpose of tensor duality. All bounds use the original completed norm families.
-/

@[expose] public section
noncomputable section

namespace BostConjecture.Adelic.Contraction

open Module ArakelovGeometry
open scoped TensorProduct

universe u v w w' wι

section Algebra

variable (K : Type*) [Field K] {ι : Type*} [Finite ι]
  (E : ι → Type*) [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]
  [∀ i, FiniteDimensional K (E i)]

/-- The finite-projective tensor duality used by the canonical pairing has
the same linear map as the tensor duality used by the norm families. -/
theorem dualDistribEquivOfProjective_toLinearMap_eq :
    (PiTensorProduct.dualDistribEquivOfProjective K E).toLinearMap =
      PiTensorProduct.dualDistrib := by
  let := Fintype.ofFinite ι
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro f
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  simp [PiTensorProduct.dualDistribEquivOfProjective_tprod_tprod,
    finprod_eq_prod_of_fintype]

end Algebra

section Maps

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {ι : Type wι} [Fintype ι] {X : ι → Type w} {Y : ι → Type w'}
  [∀ i, AddCommGroup (X i)] [∀ i, Module K (X i)] [∀ i, FiniteDimensional K (X i)]
  [∀ i, AddCommGroup (Y i)] [∀ i, Module K (Y i)] [∀ i, FiniteDimensional K (Y i)]

/-- Tensor maps that contract at finite places and are isometric at infinite
places contract for the actual orthogonal tensor norms. -/
theorem orthogonalTensor_map_norm_le_of_finite_le_infinite_eq
    (ξ : ∀ i, NormFamily S (X i)) (η : ∀ i, NormFamily S (Y i))
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hξ : ∀ i, (ξ i).IsHermitian hN) (hη : ∀ i, (η i).IsHermitian hN)
    (f : ∀ i, X i →ₗ[K] Y i) (ω : S.Ω)
    (hf : ∀ i x, (η i).norm ω ((f i).baseChange (S.ϕ ω).Completion x) ≤ (ξ i).norm ω x)
    (hfi : ω ∈ S.Ωinf → ∀ i x,
      (η i).norm ω ((f i).baseChange (S.ϕ ω).Completion x) = (ξ i).norm ω x)
    (z : (S.ϕ ω).Completion ⊗[K] (⨂[K] i, X i)) :
    (NormFamily.orthogonalTensor η hN hη).norm ω
      ((PiTensorProduct.map f).baseChange (S.ϕ ω).Completion z) ≤
        (NormFamily.orthogonalTensor ξ hN hξ).norm ω z := by
  let L := (S.ϕ ω).Completion
  let : ∀ j, NormedAddCommGroup (L ⊗[K] X j) := fun j ↦ (ξ j).fibreNormedAddCommGroup ω
  let : ∀ j, NormedSpace L (L ⊗[K] X j) := fun j ↦ (ξ j).fibreNormedSpace ω
  let : ∀ j, NormedAddCommGroup (L ⊗[K] Y j) := fun j ↦ (η j).fibreNormedAddCommGroup ω
  let : ∀ j, NormedSpace L (L ⊗[K] Y j) := fun j ↦ (η j).fibreNormedSpace ω
  by_cases hω : ω ∈ S.Ωinf
  · let := hN ω hω
    let := IsRCLikeNormedField.rclike L
    let : ∀ j, InnerProductSpace L (L ⊗[K] X j) :=
      fun j ↦ (hξ j).fibreInnerProductSpace ω hω
    let : ∀ j, InnerProductSpace L (L ⊗[K] Y j) :=
      fun j ↦ (hη j).fibreInnerProductSpace ω hω
    let g : ∀ j, (L ⊗[K] X j) →ₗᵢ[L] (L ⊗[K] Y j) :=
      fun j ↦ ⟨(f j).baseChange L, hfi hω j⟩
    rw [NormFamily.orthogonalTensor_norm_of_infinite _ _ _ ω hω,
      NormFamily.orthogonalTensor_norm_of_infinite _ _ _ ω hω]
    change orthogonalTensorSeminorm (fun j ↦ stdOrthonormalBasis L (L ⊗[K] Y j))
        (tensorBaseChangeEquiv K L Y ((PiTensorProduct.map f).baseChange L z)) ≤
      orthogonalTensorSeminorm (fun j ↦ stdOrthonormalBasis L (L ⊗[K] X j))
        (tensorBaseChangeEquiv K L X z)
    rw [tensorBaseChangeEquiv_map]
    exact (orthogonalTensorSeminorm_map_eq
      (fun j ↦ stdOrthonormalBasis L (L ⊗[K] X j))
      (fun j ↦ stdOrthonormalBasis L (L ⊗[K] Y j)) g _).le
  · rw [NormFamily.orthogonalTensor_norm_of_finite _ _ _ ω (not_not.mp hω),
      NormFamily.orthogonalTensor_norm_of_finite _ _ _ ω (not_not.mp hω)]
    change injectiveTensorSeminorm (tensorBaseChangeEquiv K L Y
      ((PiTensorProduct.map f).baseChange L z)) ≤
        injectiveTensorSeminorm (tensorBaseChangeEquiv K L X z)
    rw [tensorBaseChangeEquiv_map]
    exact injectiveSeminorm_map_le_of_norm_le (fun j ↦ (f j).baseChange L) hf _

end Maps

section Dual

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E : Type w} {F : Type w'} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]

/-- The transpose of a completed contraction contracts for the actual dual norms. -/
theorem dualMap_norm_le (ξ : NormFamily S E) (η : NormFamily S F)
    (f : E →ₗ[K] F) (ω : S.Ω)
    (hf : ∀ x, η.norm ω (f.baseChange (S.ϕ ω).Completion x) ≤ ξ.norm ω x)
    (z : (S.ϕ ω).Completion ⊗[K] Dual K F) :
    ξ.dual.norm ω (f.dualMap.baseChange (S.ϕ ω).Completion z) ≤ η.dual.norm ω z := by
  apply ξ.dual_norm_le ω _ (η.dual.norm_nonneg ω z)
  intro x
  rw [dualBaseChangeEquiv_dualMap, LinearMap.comp_apply]
  exact (η.norm_dual_apply_le ω z _).trans
    (mul_le_mul_of_nonneg_left (hf x) (η.dual.norm_nonneg ω z))

end Dual

section Evaluation

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {ι : Type wι} [Fintype ι]
  {E : Type w} {F : Type w'} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]

omit [FiniteDimensional K E] in
/-- The actual tensor pairing is bidual evaluation followed by the transpose
of the canonical tensor-dual map. -/
theorem tensorPowerPairing_eq {κ : Type*} [Finite κ] (f : E →ₗ[K] F) :
    Tensor.tensorPowerPairing (ι := κ) f =
      (PiTensorProduct.dualDistrib (R := K) (M := fun _ : κ ↦ F)).dualMap ∘ₗ
        (Dual.eval K (⨂[K] (_ : κ), F)) ∘ₗ PiTensorProduct.map (fun _ : κ ↦ f) := by
  rw [Tensor.tensorPowerPairing, dualDistribEquivOfProjective_toLinearMap_eq]
  rfl

/-- Tensor evaluation along a fibrewise isometric inclusion contracts on
every completed vector, for Hilbert norms at infinity and epsilon norms elsewhere. -/
theorem tensorPowerPairing_norm_le
    (ξ : NormFamily S E) (η : NormFamily S F)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hξ : ξ.IsHermitian hN) (hη : η.IsHermitian hN)
    (f : E →ₗ[K] F) (ω : S.Ω)
    (hf : ∀ x, η.norm ω (f.baseChange (S.ϕ ω).Completion x) = ξ.norm ω x)
    (z : (S.ϕ ω).Completion ⊗[K] (⨂[K] (_ : ι), E)) :
    (NormFamily.orthogonalTensor (fun _ : ι ↦ η.dual) hN (fun _ ↦ hη.dual)).dual.norm ω
      ((Tensor.tensorPowerPairing f).baseChange (S.ϕ ω).Completion z) ≤
        (NormFamily.orthogonalTensor (fun _ : ι ↦ ξ) hN (fun _ ↦ hξ)).norm ω z := by
  rw [tensorPowerPairing_eq, LinearMap.baseChange_comp, LinearMap.baseChange_comp,
    LinearMap.comp_apply, LinearMap.comp_apply]
  refine (dualMap_norm_le
    (NormFamily.orthogonalTensor (fun _ : ι ↦ η.dual) hN (fun _ ↦ hη.dual))
    (NormFamily.orthogonalTensor (fun _ : ι ↦ η) hN (fun _ ↦ hη)).dual
    PiTensorProduct.dualDistrib ω
    (fun x ↦ (NormFamily.orthogonalTensor_dual_norm (fun _ : ι ↦ η) hN
      (fun _ ↦ hη) ω x).le) _).trans ?_
  refine ((NormFamily.orthogonalTensor (fun _ : ι ↦ η) hN (fun _ ↦ hη)).dual_dual_norm_eval_le
    ω _).trans ?_
  exact orthogonalTensor_map_norm_le_of_finite_le_infinite_eq
    (fun _ : ι ↦ ξ) (fun _ : ι ↦ η) hN (fun _ ↦ hξ) (fun _ ↦ hη)
    (fun _ ↦ f) ω (fun _ x ↦ (hf x).le) (fun _ _ ↦ hf) z

end Evaluation

end BostConjecture.Adelic.Contraction
