/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Classical.Metric
public import ArakelovGeometry.NumberTheory.NumberField.Archimedean.Diagonal
public import ArakelovGeometry.AdelicVectorBundle.NormFamily.Hermitian.Basic

/-!
# Classical metrics on completed Archimedean fibres

The classical metric is the metric from commit
`81cf08a874039fde5d23c0fbf3970f7d28c3beca`. Its complex fibre receives the
canonical completed real or complex fibre of the generic vector space.
The resulting norm is pulled back from the given metric, including at real places.
-/

@[expose] public section
noncomputable section

open NumberField TensorProduct
open ArakelovGeometry ArakelovGeometry.AdelicStructure
  ArakelovGeometry.NumberFieldArchimedeanDiagonal

namespace BostConjecture.Arithmetic

attribute [local instance 2000] Algebra.toModule Algebra.toSMul

variable {K : Type*} [Field K] [NumberField K]

/-- The literal completion of the standard number-field curve at an infinite place. -/
abbrev ClassicalCompletion (w : InfinitePlace K) :=
  ((normalizedNumberFieldAdelicStructure K).ϕ (normalizedInfinitePlacePoint w)).Completion

/-- The completion embeds in the complex numbers through the chosen place embedding. -/
def classicalCompletionEmbedding (w : InfinitePlace K) : ClassicalCompletion w →+* ℂ :=
  (InfinitePlace.Completion.extensionEmbedding w).comp
    ((InfinitePlace.Completion.equiv w).symm.toRingHom.comp
      (normalizedInfiniteCompletionEquiv w).toRingHom)

@[simp]
theorem classicalCompletionEmbedding_coe (w : InfinitePlace K) (a : K) :
    classicalCompletionEmbedding w (algebraMap K (ClassicalCompletion w) a) =
      w.embedding a := by
  change InfinitePlace.Completion.extensionEmbedding w
    ((InfinitePlace.Completion.equiv w).symm
      (normalizedInfiniteCompletionEquiv w (algebraMap K (ClassicalCompletion w) a))) = _
  rw [normalizedInfiniteCompletionEquiv_coe]
  exact InfinitePlace.Completion.extensionEmbedding_coe w (WithAbs.toAbs w.val a)

theorem norm_classicalCompletionEmbedding (w : InfinitePlace K)
    (a : ClassicalCompletion w) : ‖classicalCompletionEmbedding w a‖ = ‖a‖ := by
  change ‖InfinitePlace.Completion.extensionEmbedding w
    ((InfinitePlace.Completion.equiv w).symm (normalizedInfiniteCompletionEquiv w a))‖ = _
  rw [(InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
    (map_zero _) _]
  exact norm_normalizedInfiniteCompletionEquiv w a

variable (M : Type*) [AddCommGroup M] [Module (𝓞 K) M]

/-- The generic fibre followed by completion, mapped to the original complex fibre. -/
def classicalCompletedFiberMap (w : InfinitePlace K) :
    let : Algebra K ℂ := w.embedding.toAlgebra
    let : Algebra (𝓞 K) ℂ := (w.embedding.comp (algebraMap (𝓞 K) K)).toAlgebra
    let : IsScalarTower (𝓞 K) K ℂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
    ClassicalCompletion w ⊗[K] (K ⊗[𝓞 K] M) →ₗ[K] ComplexFiber M w.embedding := by
  let : Algebra K ℂ := w.embedding.toAlgebra
  let : Algebra (𝓞 K) ℂ := (w.embedding.comp (algebraMap (𝓞 K) K)).toAlgebra
  let : IsScalarTower (𝓞 K) K ℂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let f : ClassicalCompletion w →ₐ[K] ℂ :=
    { classicalCompletionEmbedding w with commutes' := classicalCompletionEmbedding_coe w }
  exact ((AlgebraTensorModule.cancelBaseChange (𝓞 K) K ℂ ℂ M).restrictScalars K).toLinearMap
    ∘ₗ TensorProduct.map f.toLinearMap LinearMap.id

@[simp]
theorem classicalCompletedFiberMap_tmul (w : InfinitePlace K)
    (a : ClassicalCompletion w) (b : K) (x : M) :
    classicalCompletedFiberMap M w (a ⊗ₜ[K] (b ⊗ₜ[𝓞 K] x)) =
      (classicalCompletionEmbedding w a * w.embedding b) • fiberSection M w.embedding x := by
  let : Algebra K ℂ := w.embedding.toAlgebra
  let : Algebra (𝓞 K) ℂ := (w.embedding.comp (algebraMap (𝓞 K) K)).toAlgebra
  let : IsScalarTower (𝓞 K) K ℂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  change (AlgebraTensorModule.cancelBaseChange (𝓞 K) K ℂ ℂ M)
    (classicalCompletionEmbedding w a ⊗ₜ[K] (b ⊗ₜ[𝓞 K] x)) = _
  rw [AlgebraTensorModule.cancelBaseChange_tmul]
  change (w.embedding b * classicalCompletionEmbedding w a) ⊗ₜ[𝓞 K] x = _
  simp only [mul_comm (w.embedding b), fiberSection, smul_tmul', smul_eq_mul, mul_one]

theorem classicalCompletedFiberMap_injective (w : InfinitePlace K) :
    Function.Injective (classicalCompletedFiberMap M w) := by
  let : Algebra K ℂ := w.embedding.toAlgebra
  let : Algebra (𝓞 K) ℂ := (w.embedding.comp (algebraMap (𝓞 K) K)).toAlgebra
  let : IsScalarTower (𝓞 K) K ℂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  apply (AlgebraTensorModule.cancelBaseChange (𝓞 K) K ℂ ℂ M).injective.comp
  exact TensorProduct.map_injective_of_flat_flat _ _
    (classicalCompletionEmbedding w).injective Function.injective_id

theorem classicalCompletedFiberMap_smul (w : InfinitePlace K)
    (a : ClassicalCompletion w) (z : ClassicalCompletion w ⊗[K] (K ⊗[𝓞 K] M)) :
    classicalCompletedFiberMap M w (a • z) =
      classicalCompletionEmbedding w a • classicalCompletedFiberMap M w z := by
  induction z using TensorProduct.inductionOn with
  | tmul b x =>
    induction x using TensorProduct.inductionOn with
    | tmul c x =>
      simp only [smul_tmul', smul_eq_mul, classicalCompletedFiberMap_tmul,
        map_mul, smul_smul, mul_assoc]
    | add x y hx hy => simp only [tmul_add, smul_add, map_add, hx, hy]
  | add z t hz ht => simp only [smul_add, map_add, hz, ht]

namespace HermitianMetric

variable {M}

/-- The prescribed classical metric on the actual completed generic fibre. -/
def completedArchimedeanNorm (h : HermitianMetric K M) (w : InfinitePlace K) :
    Seminorm (ClassicalCompletion w) (ClassicalCompletion w ⊗[K] (K ⊗[𝓞 K] M)) := by
  let : InnerProductSpace.Core ℂ (ComplexFiber M w.embedding) := h.fiber w.embedding
  let := InnerProductSpace.Core.toNormedAddCommGroup
    (𝕜 := ℂ) (F := ComplexFiber M w.embedding)
  let := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M w.embedding))
  exact Seminorm.of (fun z => ‖classicalCompletedFiberMap M w z‖)
    (fun x y => by rw [map_add]; exact norm_add_le _ _)
    (fun a x => by
      rw [classicalCompletedFiberMap_smul, norm_smul, norm_classicalCompletionEmbedding])

theorem completedArchimedeanNorm_eq_zero_iff (h : HermitianMetric K M)
    (w : InfinitePlace K) (z : ClassicalCompletion w ⊗[K] (K ⊗[𝓞 K] M)) :
    h.completedArchimedeanNorm w z = 0 ↔ z = 0 := by
  let : InnerProductSpace.Core ℂ (ComplexFiber M w.embedding) := h.fiber w.embedding
  let := InnerProductSpace.Core.toNormedAddCommGroup
    (𝕜 := ℂ) (F := ComplexFiber M w.embedding)
  change ‖classicalCompletedFiberMap M w z‖ = 0 ↔ z = 0
  rw [norm_eq_zero, (classicalCompletedFiberMap_injective M w).eq_iff' (map_zero _)]

/-- Integral sections retain exactly their original classical norm. -/
@[simp]
theorem completedArchimedeanNorm_section (h : HermitianMetric K M)
    (w : InfinitePlace K) (x : M) :
    h.completedArchimedeanNorm w (1 ⊗ₜ[K] ((1 : K) ⊗ₜ[𝓞 K] x)) =
      h.sectionNorm w.embedding x := by
  let : InnerProductSpace.Core ℂ (ComplexFiber M w.embedding) := h.fiber w.embedding
  let := InnerProductSpace.Core.toNormedAddCommGroup
    (𝕜 := ℂ) (F := ComplexFiber M w.embedding)
  change ‖classicalCompletedFiberMap M w _‖ = ‖fiberSection M w.embedding x‖
  simp only [classicalCompletedFiberMap_tmul, map_one, mul_one, one_smul]

/-- The completed norm is Hermitian, also at real places. -/
theorem completedArchimedeanNorm_parallelogram (h : HermitianMetric K M)
    (w : InfinitePlace K) (x y : ClassicalCompletion w ⊗[K] (K ⊗[𝓞 K] M)) :
    h.completedArchimedeanNorm w (x + y) * h.completedArchimedeanNorm w (x + y) +
      h.completedArchimedeanNorm w (x - y) * h.completedArchimedeanNorm w (x - y) =
      2 * (h.completedArchimedeanNorm w x * h.completedArchimedeanNorm w x +
        h.completedArchimedeanNorm w y * h.completedArchimedeanNorm w y) := by
  let : InnerProductSpace.Core ℂ (ComplexFiber M w.embedding) := h.fiber w.embedding
  let := InnerProductSpace.Core.toNormedAddCommGroup
    (𝕜 := ℂ) (F := ComplexFiber M w.embedding)
  let := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M w.embedding))
  change ‖classicalCompletedFiberMap M w (x + y)‖ *
    ‖classicalCompletedFiberMap M w (x + y)‖ +
    ‖classicalCompletedFiberMap M w (x - y)‖ *
    ‖classicalCompletedFiberMap M w (x - y)‖ =
    2 * (‖classicalCompletedFiberMap M w x‖ * ‖classicalCompletedFiberMap M w x‖ +
      ‖classicalCompletedFiberMap M w y‖ * ‖classicalCompletedFiberMap M w y‖)
  simp only [map_add, map_sub]
  exact parallelogram_law_with_norm_mul ℂ
    (classicalCompletedFiberMap M w x) (classicalCompletedFiberMap M w y)

end HermitianMetric

end BostConjecture.Arithmetic
