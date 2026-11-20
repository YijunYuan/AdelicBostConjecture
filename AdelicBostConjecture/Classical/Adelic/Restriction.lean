/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import AdelicBostConjecture.Classical.Adelic.Finite
public import AdelicBostConjecture.Classical.Submodule
public import ArakelovGeometry.AdelicVectorBundle.Degree.Isometry

/-! # Adelization preserves the original saturated subspace metrics -/

@[expose] public section
noncomputable section

open NumberField TensorProduct IsDedekindDomain
open ArakelovGeometry ArakelovGeometry.AdelicStructure
  ArakelovGeometry.ActualPrimeIndexing ArakelovGeometry.NumberFieldFullLattice

namespace AdelicBostConjecture.Arithmetic

attribute [local instance 2000] Algebra.toModule Algebra.toSMul

variable {K : Type*} [Field K] [NumberField K]
variable {M N : Type*} [AddCommGroup M] [Module (𝓞 K) M]
  [AddCommGroup N] [Module (𝓞 K) N]

/-- The completed complex fibre map is natural in the original integral module. -/
theorem classicalCompletedFiberMap_natural (f : N →ₗ[𝓞 K] M) (w : InfinitePlace K)
    (z : ClassicalCompletion w ⊗[K] (K ⊗[𝓞 K] N)) :
    classicalCompletedFiberMap M w ((f.baseChange K).baseChange (ClassicalCompletion w) z) =
      fiberMap f w.embedding (classicalCompletedFiberMap N w z) := by
  let : Algebra K ℂ := w.embedding.toAlgebra
  induction z using TensorProduct.inductionOn with
  | tmul a z =>
    induction z using TensorProduct.inductionOn with
    | tmul b x =>
      simp only [LinearMap.baseChange_tmul, classicalCompletedFiberMap_tmul, map_smul]
      rfl
    | add x y hx hy => simp only [tmul_add, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

omit [NumberField K] in
/-- A saturated integral submodule is a direct summand. -/
theorem exists_retraction_of_projective_quotient (P : Submodule (𝓞 K) M)
    [Module.Projective (𝓞 K) (M ⧸ P)] :
    ∃ r : M →ₗ[𝓞 K] P, r.comp P.subtype = LinearMap.id := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property P.mkQ
    (LinearMap.id : (M ⧸ P) →ₗ[𝓞 K] (M ⧸ P)) P.mkQ_surjective
  let r : M →ₗ[𝓞 K] P := (LinearMap.id - s.comp P.mkQ).codRestrict P (by
    intro x
    apply (Submodule.Quotient.mk_eq_zero P).mp
    change P.mkQ (x - s (P.mkQ x)) = 0
    rw [map_sub]
    have he := DFunLike.congr_fun hs (P.mkQ x)
    change P.mkQ (s (P.mkQ x)) = P.mkQ x at he
    rw [he, sub_self])
  refine ⟨r, ?_⟩
  ext x
  change (x : M) - s (P.mkQ (x : M)) = x
  rw [show P.mkQ (x : M) = 0 from (Submodule.Quotient.mk_eq_zero P).mpr x.property,
    map_zero, sub_zero]

/-- The generic-fibre identification is compatible with the actual inclusion. -/
theorem integralPartGenericEquiv_subtype (X : Submodule K (K ⊗[𝓞 K] M)) :
    X.subtype.comp (integralPartGenericEquiv X).toLinearMap =
      (integralPart X).subtype.baseChange K := by
  ext a
  rfl

namespace HermitianMetric

/-- Pullback of the original metric commutes with completion at infinity. -/
theorem completedArchimedeanNorm_pullback (h : HermitianMetric K M)
    (f : N →ₗ[𝓞 K] M) (hf : Function.Injective f) (w : InfinitePlace K)
    (z : ClassicalCompletion w ⊗[K] (K ⊗[𝓞 K] N)) :
    (h.pullback f hf).completedArchimedeanNorm w z =
      h.completedArchimedeanNorm w
        ((f.baseChange K).baseChange (ClassicalCompletion w) z) := by
  change Real.sqrt ((h.fiber w.embedding).inner
      (fiberMap f w.embedding (classicalCompletedFiberMap N w z))
      (fiberMap f w.embedding (classicalCompletedFiberMap N w z))).re =
    Real.sqrt ((h.fiber w.embedding).inner
      (classicalCompletedFiberMap M w _)
      (classicalCompletedFiberMap M w _)).re
  rw [classicalCompletedFiberMap_natural]

variable [Module.Finite (𝓞 K) M] [Module.Finite (𝓞 K) N]

/-- Split integral injections preserve the induced finite lattice norms. -/
theorem finite_norm_of_retraction (h : HermitianMetric K M) (g : HermitianMetric K N)
    (f : N →ₗ[𝓞 K] M) (r : M →ₗ[𝓞 K] N) (hr : r.comp f = LinearMap.id)
    (p : HeightOneSpectrum (𝓞 K))
    (z : FiniteCompletion p ⊗[K] (K ⊗[𝓞 K] N)) :
    h.toAdelicBundle.norm (normalizedPrimeParameter p)
      ((f.baseChange K).baseChange (FiniteCompletion p) z) =
        g.toAdelicBundle.norm (normalizedPrimeParameter p) z := by
  apply le_antisymm (g.finite_norm_baseChange_le h f p z)
  have hb := h.finite_norm_baseChange_le g r p
    ((f.baseChange K).baseChange (FiniteCompletion p) z)
  have he : ((r.baseChange K).baseChange (FiniteCompletion p)).comp
      ((f.baseChange K).baseChange (FiniteCompletion p)) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, hr,
      LinearMap.baseChange_id, LinearMap.baseChange_id]
  simpa only [← LinearMap.comp_apply, he, LinearMap.id_apply] using hb

/-- The original pullback norm and the adelic restriction agree at every place
for an integral split injection. -/
theorem toAdelicBundle_norm_pullback (h : HermitianMetric K M)
    (f : N →ₗ[𝓞 K] M) (hf : Function.Injective f)
    (r : M →ₗ[𝓞 K] N) (hr : r.comp f = LinearMap.id)
    (ω : (normalizedNumberFieldAdelicStructure K).Ω)
    (z : ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion ⊗[K]
      (K ⊗[𝓞 K] N)) :
    (h.pullback f hf).toAdelicBundle.norm ω z =
      h.toAdelicBundle.norm ω
        ((f.baseChange K).baseChange
          ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion z) := by
  by_cases hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin
  · obtain ⟨p, rfl⟩ := exists_normalizedPrimeParameter_eq ω hω
    exact (h.finite_norm_of_retraction (h.pullback f hf) f r hr p z).symm
  · have hi : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωinf := hω
    obtain ⟨w, rfl⟩ : ∃ w : InfinitePlace K, normalizedInfinitePlacePoint w = ω := by
      simpa only [normalizedNumberFieldAdelicStructure_Ωinf_eq_range, Set.mem_range] using hi
    change (h.pullback f hf).adelicNormFamily.norm _ _ = h.adelicNormFamily.norm _ _
    rw [adelicNormFamily, adelicNormFamily,
      fullLatticeGaugeFamily_norm_not_finite _ _ _ _ _ hi,
      fullLatticeGaugeFamily_norm_not_finite _ _ _ _ _ hi,
      archimedeanNormFamily_norm_infinite _ _ hi,
      archimedeanNormFamily_norm_infinite _ _ hi,
      infiniteNormAt_point, infiniteNormAt_point]
    exact h.completedArchimedeanNorm_pullback f hf w z

/-- The saturated integral part, with its original metric, adelizes to the
actual restricted bundle under its canonical generic-fibre equivalence. -/
theorem toAdelicBundle_restrict_norm (h : HermitianMetric K M)
    (X : Submodule K (K ⊗[𝓞 K] M))
    (ω : (normalizedNumberFieldAdelicStructure K).Ω)
    (z : ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion ⊗[K]
      (K ⊗[𝓞 K] integralPart X)) :
    (h.toAdelicBundle.restrictOfNormMeasurability X).norm ω
      ((integralPartGenericEquiv X).toLinearMap.baseChange
        ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion z) =
      (h.submodule (integralPart X)).toAdelicBundle.norm ω z := by
  obtain ⟨r, hr⟩ := exists_retraction_of_projective_quotient (integralPart X)
  have hp := h.toAdelicBundle_norm_pullback (integralPart X).subtype
    (integralPart X).injective_subtype r hr ω z
  change (h.toAdelicBundle.toNormFamily.restrict X).norm ω _ = _
  rw [NormFamily.restrict_norm, ← LinearMap.comp_apply,
    ← LinearMap.baseChange_comp, integralPartGenericEquiv_subtype]
  exact hp.symm

/-- Degree is invariant under the proved restriction identification. -/
theorem degree_toAdelicBundle_restrict (h : HermitianMetric K M)
    (X : Submodule K (K ⊗[𝓞 K] M)) :
    (h.toAdelicBundle.restrictOfNormMeasurability X).degree =
      (h.submodule (integralPart X)).toAdelicBundle.degree := by
  symm
  exact AdelicVectorBundle.degree_eq_of_completed_isometry
    (h.submodule (integralPart X)).toAdelicBundle
    (h.toAdelicBundle.restrictOfNormMeasurability X)
    (integralPartGenericEquiv X) (h.toAdelicBundle_restrict_norm X)

end HermitianMetric
end AdelicBostConjecture.Arithmetic
