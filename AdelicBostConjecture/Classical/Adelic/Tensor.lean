/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import AdelicBostConjecture.Classical.Adelic.Finite
public import AdelicBostConjecture.Classical.Tensor
public import ArakelovGeometry.AdelicVectorBundle.Tensor.Hermitian.Coherence
public import AdelicBostConjecture.Classical.Adelic.ArchimedeanInner

/-!
# Adelization preserves tensor norms

The completed integral tensor lattice gives the finite-place comparison.
At infinite places, the original tensor inner product gives the isometry.
-/

@[expose] public section
noncomputable section

section FiniteTensor

open NumberField TensorProduct IsDedekindDomain
open ArakelovGeometry ArakelovGeometry.AdelicStructure
  ArakelovGeometry.ActualPrimeIndexing ArakelovGeometry.NumberFieldFullLattice

namespace AdelicBostConjecture.Arithmetic
attribute [local instance 2000] Algebra.toModule Algebra.toSMul

universe u
variable {K M N : Type u} [Field K] [NumberField K]
  [AddCommGroup M] [Module (𝓞 K) M] [AddCommGroup N] [Module (𝓞 K) N]

/-- The two canonical tensor scalar extensions, composed. -/
def completedTensorEquiv (F : Type*) [Field F] [Algebra K F] :
    F ⊗[K] (K ⊗[𝓞 K] (M ⊗[𝓞 K] N)) ≃ₗ[F]
      (F ⊗[K] (K ⊗[𝓞 K] M)) ⊗[F] (F ⊗[K] (K ⊗[𝓞 K] N)) :=
  (LinearEquiv.baseChange K F _ _ (AlgebraTensorModule.distribBaseChange (𝓞 K) K M N)) ≪≫ₗ
    AlgebraTensorModule.distribBaseChange K F _ _

omit [NumberField K] in
@[simp]
theorem completedTensorEquiv_tmul (F : Type*) [Field F] [Algebra K F]
    (a : F) (b : K) (x : M) (y : N) :
    completedTensorEquiv (K := K) (M := M) (N := N) F
      (a ⊗ₜ[K] (b ⊗ₜ[𝓞 K] (x ⊗ₜ[𝓞 K] y))) =
      (a ⊗ₜ[K] (b ⊗ₜ[𝓞 K] x)) ⊗ₜ[F] (1 ⊗ₜ[K] ((1 : K) ⊗ₜ[𝓞 K] y)) := by
  simp only [completedTensorEquiv, LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul,
    AlgebraTensorModule.distribBaseChange_tmul]

namespace HermitianMetric
variable [Module.Finite (𝓞 K) M] [Module.Finite (𝓞 K) N]

/-- Tensoring completed integral vectors stays in the completed integral tensor lattice. -/
theorem completedTensor_mem (h : HermitianMetric K M) (g : HermitianMetric K N)
    (p : HeightOneSpectrum (𝓞 K))
    (x : FiniteCompletion p ⊗[K] (K ⊗[𝓞 K] M))
    (y : FiniteCompletion p ⊗[K] (K ⊗[𝓞 K] N))
    (hx : h.toAdelicBundle.norm (normalizedPrimeParameter p) x ≤ 1)
    (hy : g.toAdelicBundle.norm (normalizedPrimeParameter p) y ≤ 1) :
    (completedTensorEquiv (K := K) (M := M) (N := N) (FiniteCompletion p)).symm
      (x ⊗ₜ[FiniteCompletion p] y) ∈
      NumberFieldModel.completedLatticeSpan (genericLattice (K := K) (M ⊗[𝓞 K] N)) p := by
  let e := completedTensorEquiv (K := K) (M := M) (N := N) (FiniteCompletion p)
  let P := NumberFieldModel.completedLatticeSpan (genericLattice (K := K) (M ⊗[𝓞 K] N)) p
  have hx' := (h.finite_norm_le_one_iff p x).mp hx
  have hy' := (g.finite_norm_le_one_iff p y).mp hy
  have H : ∀ x ∈ NumberFieldModel.completedLatticeSpan (genericLattice (K := K) M) p,
      ∀ y ∈ NumberFieldModel.completedLatticeSpan (genericLattice (K := K) N) p,
        e.symm (x ⊗ₜ[FiniteCompletion p] y) ∈ P := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨_, m, rfl⟩, rfl⟩ := hx
      change ∀ y ∈ NumberFieldModel.completedLatticeSpan (genericLattice (K := K) N) p,
        e.symm ((1 ⊗ₜ[K] ((1 : K) ⊗ₜ[𝓞 K] m)) ⊗ₜ[FiniteCompletion p] y) ∈ P
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨⟨_, n, rfl⟩, rfl⟩ := hy
        have he : e.symm ((1 ⊗ₜ[K] ((1 : K) ⊗ₜ[𝓞 K] m)) ⊗ₜ[FiniteCompletion p]
            (1 ⊗ₜ[K] ((1 : K) ⊗ₜ[𝓞 K] n))) =
            1 ⊗ₜ[K] ((1 : K) ⊗ₜ[𝓞 K] (m ⊗ₜ[𝓞 K] n)) := by
          apply e.injective
          rw [LinearEquiv.apply_symm_apply, completedTensorEquiv_tmul]
        change e.symm ((1 ⊗ₜ[K] ((1 : K) ⊗ₜ[𝓞 K] m)) ⊗ₜ[FiniteCompletion p]
          (1 ⊗ₜ[K] ((1 : K) ⊗ₜ[𝓞 K] n))) ∈ P
        rw [he]
        exact Submodule.subset_span ⟨⟨_, m ⊗ₜ[𝓞 K] n, rfl⟩, rfl⟩
      | zero => rw [tmul_zero, e.symm.map_zero]; exact P.zero_mem
      | add y z _ _ hy hz =>
        simpa only [tmul_add, map_add] using P.add_mem hy hz
      | smul a y _ hy =>
        change e.symm (_ ⊗ₜ[FiniteCompletion p] ((a : FiniteCompletion p) • y)) ∈ P
        rw [tmul_smul, e.symm.map_smul]
        exact P.smul_mem a hy
    | zero => intro y _; rw [zero_tmul, e.symm.map_zero]; exact P.zero_mem
    | add x z _ _ hx hz =>
      intro y hy
      simpa only [add_tmul, map_add] using P.add_mem (hx y hy) (hz y hy)
    | smul a x _ hx =>
      intro y hy
      change e.symm (((a : FiniteCompletion p) • x) ⊗ₜ[FiniteCompletion p] y) ∈ P
      rw [← smul_tmul', e.symm.map_smul]
      exact P.smul_mem a (hx y hy)
  exact H x hx' y hy'

/-- The finite tensor gauge has the product bound on all completed pure tensors. -/
theorem finite_norm_completedTensor_le (h : HermitianMetric K M) (g : HermitianMetric K N)
    (p : HeightOneSpectrum (𝓞 K))
    (x : FiniteCompletion p ⊗[K] (K ⊗[𝓞 K] M))
    (y : FiniteCompletion p ⊗[K] (K ⊗[𝓞 K] N)) :
    (h ⊗[𝓞 K] g).toAdelicBundle.norm (normalizedPrimeParameter p)
      ((completedTensorEquiv (K := K) (M := M) (N := N) (FiniteCompletion p)).symm
        (x ⊗ₜ[FiniteCompletion p] y)) ≤
      h.toAdelicBundle.norm (normalizedPrimeParameter p) x *
        g.toAdelicBundle.norm (normalizedPrimeParameter p) y := by
  let e := completedTensorEquiv (K := K) (M := M) (N := N) (FiniteCompletion p)
  let q : Seminorm (FiniteCompletion p)
      (FiniteCompletion p ⊗[K] (K ⊗[𝓞 K] (M ⊗[𝓞 K] N))) :=
    (h ⊗[𝓞 K] g).toAdelicBundle.norm (normalizedPrimeParameter p)
  change q (e.symm (x ⊗ₜ[FiniteCompletion p] y)) ≤ _
  by_cases hx : x = 0
  · subst x
    rw [zero_tmul, e.symm.map_zero, map_zero q,
      h.toAdelicBundle.toNormFamily.norm_zero, zero_mul]
  by_cases hy : y = 0
  · subst y
    rw [tmul_zero, e.symm.map_zero, map_zero q,
      g.toAdelicBundle.toNormFamily.norm_zero, mul_zero]
  obtain ⟨a, ha, hax, hna⟩ := h.finite_norm_exists_scalar p x hx
  obtain ⟨b, hb, hby, hnb⟩ := g.finite_norm_exists_scalar p y hy
  have hu : q (e.symm ((a⁻¹ • x) ⊗ₜ[FiniteCompletion p] (b⁻¹ • y))) ≤ 1 :=
    ((h ⊗[𝓞 K] g).finite_norm_le_one_iff p _).mpr
      (h.completedTensor_mem g p _ _ hax hby)
  have he : x ⊗ₜ[FiniteCompletion p] y =
      (a * b) • ((a⁻¹ • x) ⊗ₜ[FiniteCompletion p] (b⁻¹ • y)) := by
    rw [smul_tmul_smul, smul_smul]
    rw [show a * b * (a⁻¹ * b⁻¹) = 1 by field_simp, one_smul]
  change q (e.symm (x ⊗ₜ[FiniteCompletion p] y)) ≤ _
  rw [he, map_smul, map_smul_eq_mul]
  exact (mul_le_mul_of_nonneg_left hu (norm_nonneg _)).trans_eq
    (by rw [mul_one, norm_mul, hna, hnb])

/-- The canonical generic tensor equivalence preserves all finite norms. -/
theorem finite_norm_tensor (h : HermitianMetric K M) (g : HermitianMetric K N)
    (p : HeightOneSpectrum (𝓞 K))
    (z : FiniteCompletion p ⊗[K] (K ⊗[𝓞 K] (M ⊗[𝓞 K] N))) :
    (h.toAdelicBundle.toNormFamily ⊗ʰ g.toAdelicBundle.toNormFamily).norm
      (normalizedPrimeParameter p)
      ((AlgebraTensorModule.distribBaseChange (𝓞 K) K M N).toLinearMap.baseChange
        (FiniteCompletion p) z) =
      (h ⊗[𝓞 K] g).toAdelicBundle.norm (normalizedPrimeParameter p) z := by
  -- Keep the place explicit so the dependent completion instances match directly.
  let e := LinearEquiv.baseChange K (FiniteCompletion p) _ _
    (AlgebraTensorModule.distribBaseChange (𝓞 K) K M N)
  let τ := h.toAdelicBundle.toNormFamily ⊗ʰ g.toAdelicBundle.toNormFamily
  have hτ := NormFamily.orthogonalTensorPair_isHermitian
    h.toAdelicBundle.toNormFamily g.toAdelicBundle.toNormFamily
  have hq := hτ.1 (normalizedPrimeParameter p) (normalizedPrimeParameter_mem_fin p)
  apply le_antisymm
  · have hL : ∀ x : M ⊗[𝓞 K] N,
        τ.norm (normalizedPrimeParameter p) (e (1 ⊗ₜ[K] ((1 : K) ⊗ₜ[𝓞 K] x))) ≤ 1 := by
      intro x
      induction x using TensorProduct.inductionOn with
      | add x y hx hy =>
        simpa only [tmul_add, e.map_add] using (hq (e (1 ⊗ₜ[K] ((1 : K) ⊗ₜ[𝓞 K] x)))
          (e (1 ⊗ₜ[K] ((1 : K) ⊗ₜ[𝓞 K] y)))).trans (max_le hx hy)
      | tmul x y =>
        have he : e (1 ⊗ₜ[K] ((1 : K) ⊗ₜ[𝓞 K] (x ⊗ₜ[𝓞 K] y))) =
            (AlgebraTensorModule.distribBaseChange K (FiniteCompletion p)
              (K ⊗[𝓞 K] M) (K ⊗[𝓞 K] N)).symm
              ((1 ⊗ₜ[K] ((1 : K) ⊗ₜ[𝓞 K] x)) ⊗ₜ[FiniteCompletion p]
                (1 ⊗ₜ[K] ((1 : K) ⊗ₜ[𝓞 K] y))) := by
          apply (AlgebraTensorModule.distribBaseChange K (FiniteCompletion p)
            (K ⊗[𝓞 K] M) (K ⊗[𝓞 K] N)).injective
          rw [LinearEquiv.apply_symm_apply]
          exact completedTensorEquiv_tmul (FiniteCompletion p) 1 1 x y
        rw [he, NormFamily.orthogonalTensorPair_norm_tmul_completed]
        exact (mul_le_mul (h.finite_norm_section_le_one p x)
          (g.finite_norm_section_le_one p y)
          (g.toAdelicBundle.toNormFamily.norm_nonneg (normalizedPrimeParameter p) _)
          zero_le_one).trans_eq (mul_one _)
    exact (h ⊗[𝓞 K] g).finite_seminorm_le p (τ.norm (normalizedPrimeParameter p))
      e.toLinearMap hq hL z
  · let := (h ⊗[𝓞 K] g).adelicNormFamily.fibreNormedAddCommGroup (normalizedPrimeParameter p)
    let := (h ⊗[𝓞 K] g).adelicNormFamily.fibreNormedSpace (normalizedPrimeParameter p)
    have hb := NormFamily.norm_linearMap_le_orthogonalTensorPair_of_finite
      h.toAdelicBundle.toNormFamily g.toAdelicBundle.toNormFamily (normalizedPrimeParameter p)
      (normalizedPrimeParameter_mem_fin p) e.symm.toLinearMap
      ((h ⊗[𝓞 K] g).toAdelicBundle_isHermitian.1 (normalizedPrimeParameter p)
        (normalizedPrimeParameter_mem_fin p))
      (C := 1) zero_le_one
      (fun x y => by
        change (h ⊗[𝓞 K] g).adelicNormFamily.norm (normalizedPrimeParameter p) _ ≤ _
        rw [one_mul]
        exact h.finite_norm_completedTensor_le g p x y)
      (e z)
    change (h ⊗[𝓞 K] g).adelicNormFamily.norm (normalizedPrimeParameter p) (e.symm (e z)) ≤
      1 * τ.norm (normalizedPrimeParameter p) (e z) at hb
    rw [LinearEquiv.symm_apply_apply, one_mul] at hb
    exact hb

end HermitianMetric
end AdelicBostConjecture.Arithmetic

end FiniteTensor

section TensorComparison

open NumberField TensorProduct
open scoped InnerProductSpace
open ArakelovGeometry ArakelovGeometry.AdelicStructure
  ArakelovGeometry.ActualPrimeIndexing ArakelovGeometry.NumberFieldArchimedeanDiagonal

namespace AdelicBostConjecture.Arithmetic.HermitianMetric
attribute [local instance 2000] Algebra.toModule Algebra.toSMul

universe u
variable {K M N : Type u} [Field K] [NumberField K]
  [AddCommGroup M] [Module (𝓞 K) M] [AddCommGroup N] [Module (𝓞 K) N]
  [Module.Finite (𝓞 K) M] [Module.Finite (𝓞 K) N]

/-- The original tensor metric and the adelic Hilbert tensor agree at infinity. -/
theorem infinite_norm_tensor (h : HermitianMetric K M) (g : HermitianMetric K N)
    (w : InfinitePlace K)
    (z : ClassicalCompletion w ⊗[K] (K ⊗[𝓞 K] (M ⊗[𝓞 K] N))) :
    (h.toAdelicBundle.toNormFamily ⊗ʰ g.toAdelicBundle.toNormFamily).norm
      (normalizedInfinitePlacePoint w)
      ((AlgebraTensorModule.distribBaseChange (𝓞 K) K M N).toLinearMap.baseChange
        (ClassicalCompletion w) z) =
      (h ⊗[𝓞 K] g).toAdelicBundle.norm (normalizedInfinitePlacePoint w) z := by
  let := (inferInstance : (normalizedNumberFieldAdelicStructure K).IsArchimedeanNormalized)
    (normalizedInfinitePlacePoint w) (normalizedInfinitePlacePoint_mem_inf w)
  let := IsRCLikeNormedField.rclike (ClassicalCompletion w)
  let := h.adelicNormFamily.fibreNormedAddCommGroup (normalizedInfinitePlacePoint w)
  let := h.adelicNormFamily.fibreNormedSpace (normalizedInfinitePlacePoint w)
  let := h.adelicNormFamily.fiberInnerProductSpace
    (normalizedInfinitePlacePoint w) (normalizedInfinitePlacePoint_mem_inf w)
  let := g.adelicNormFamily.fibreNormedAddCommGroup (normalizedInfinitePlacePoint w)
  let := g.adelicNormFamily.fibreNormedSpace (normalizedInfinitePlacePoint w)
  let := g.adelicNormFamily.fiberInnerProductSpace
    (normalizedInfinitePlacePoint w) (normalizedInfinitePlacePoint_mem_inf w)
  let : Algebra K ℂ := w.embedding.toAlgebra
  let : Algebra (𝓞 K) ℂ := (w.embedding.comp (algebraMap (𝓞 K) K)).toAlgebra
  let : InnerProductSpace.Core ℂ (ComplexFiber (M ⊗[𝓞 K] N) w.embedding) :=
    (h ⊗[𝓞 K] g).fiber w.embedding
  let := InnerProductSpace.Core.toNormedAddCommGroup
    (𝕜 := ℂ) (F := ComplexFiber (M ⊗[𝓞 K] N) w.embedding)
  let := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber (M ⊗[𝓞 K] N) w.embedding))
  let e := completedTensorEquiv (K := K) (M := M) (N := N) (ClassicalCompletion w)
  have hip (x y : ClassicalCompletion w ⊗[K] (K ⊗[𝓞 K] (M ⊗[𝓞 K] N))) :
      classicalCompletionEmbedding w (inner (ClassicalCompletion w) (e x) (e y)) =
        ((h ⊗[𝓞 K] g).fiber w.embedding).inner
          (classicalCompletedFiberMap (M ⊗[𝓞 K] N) w x)
          (classicalCompletedFiberMap (M ⊗[𝓞 K] N) w y) := by
    induction x using TensorProduct.inductionOn with
    | add x t hx ht =>
      simp only [map_add, inner_add_left, hx, ht]
    | tmul a x =>
      induction x using TensorProduct.inductionOn with
      | add x t hx ht =>
        simp only [tmul_add, map_add, inner_add_left, hx, ht]
      | tmul b x =>
        induction x using TensorProduct.inductionOn with
        | add x t hx ht =>
          simp only [tmul_add, map_add, inner_add_left, hx, ht]
        | tmul m n =>
          induction y using TensorProduct.inductionOn with
          | add y t hy ht =>
            simp only [map_add, inner_add_right, hy, ht]
          | tmul c y =>
            induction y using TensorProduct.inductionOn with
            | add y t hy ht =>
              simp only [tmul_add, map_add, inner_add_right, hy, ht]
            | tmul d y =>
              induction y using TensorProduct.inductionOn with
              | add y t hy ht =>
                simp only [tmul_add, map_add, inner_add_right, hy, ht]
              | tmul m' n' =>
                simp only [e, completedTensorEquiv_tmul, TensorProduct.inner_tmul, map_mul,
                  h.completedFiber_inner, g.completedFiber_inner,
                  classicalCompletedFiberMap_tmul, map_one, mul_one, one_smul,
                  InnerProductSpace.Core.inner_smul_left, InnerProductSpace.Core.inner_smul_right,
                  tensor_inner_section]
                ring
  rw [NormFamily.orthogonalTensorPair_norm_eq_hilbert _ _ _
    (normalizedInfinitePlacePoint_mem_inf w)]
  change ‖e z‖ = (h ⊗[𝓞 K] g).adelicNormFamily.norm _ _
  rw [adelicNormFamily_norm_infinite_point]
  change ‖e z‖ = ‖classicalCompletedFiberMap (M ⊗[𝓞 K] N) w z‖
  have hi := congrArg Complex.re (hip z z)
  rw [complexEmbedding_re _ (norm_classicalCompletionEmbedding w)] at hi
  change RCLike.re (inner (ClassicalCompletion w) (e z) (e z)) =
    RCLike.re (inner ℂ (classicalCompletedFiberMap (M ⊗[𝓞 K] N) w z)
      (classicalCompletedFiberMap (M ⊗[𝓞 K] N) w z)) at hi
  simp only [inner_self_eq_norm_sq] at hi
  nlinarith [norm_nonneg (e z), norm_nonneg (classicalCompletedFiberMap (M ⊗[𝓞 K] N) w z)]

/-- Adelization commutes isometrically with the original tensor product. -/
theorem toAdelicBundle_norm_tensor (h : HermitianMetric K M) (g : HermitianMetric K N)
    (ω : (normalizedNumberFieldAdelicStructure K).Ω)
    (z : ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion ⊗[K]
      (K ⊗[𝓞 K] (M ⊗[𝓞 K] N))) :
    (h.toAdelicBundle.toNormFamily ⊗ʰ g.toAdelicBundle.toNormFamily).norm ω
      ((AlgebraTensorModule.distribBaseChange (𝓞 K) K M N).toLinearMap.baseChange
        ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion z) =
      (h ⊗[𝓞 K] g).toAdelicBundle.norm ω z := by
  by_cases hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin
  · obtain ⟨p, rfl⟩ := exists_normalizedPrimeParameter_eq ω hω
    exact h.finite_norm_tensor g p z
  · have hi : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωinf := hω
    obtain ⟨w, rfl⟩ : ∃ w : InfinitePlace K, normalizedInfinitePlacePoint w = ω := by
      simpa only [normalizedNumberFieldAdelicStructure_Ωinf_eq_range, Set.mem_range] using hi
    exact h.infinite_norm_tensor g w z

end AdelicBostConjecture.Arithmetic.HermitianMetric

end TensorComparison
