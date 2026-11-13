/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Classical.Adelic.ArchimedeanInner
public import ArakelovGeometry.AdelicVectorBundle.Determinant.HermitianBasis
public import ArakelovGeometry.Analysis.Determinant.ExactSequence
public import ArakelovGeometry.AdelicVectorBundle.Degree.LineVector
public import ArakelovGeometry.NumberTheory.NumberField.Lattice.Line.Index
public import ArakelovGeometry.NumberTheory.NumberField.Covolume.Degree
public import ArakelovGeometry.NumberTheory.NumberField.Lattice.Line.FullLatticeIndex
public import ArakelovGeometry.NumberTheory.NumberField.Archimedean.DeterminantIntegral
public import ArakelovGeometry.AdelicCurve.Basic
public import ArakelovGeometry.NumberTheory.NumberField.Lattice.Index.BoundedElement
public import BostConjecture.Classical.Adelic.Determinant
public import BostConjecture.Classical.Adelic.Restriction

/-!
# Comparing the original and adelic degrees

The Gram determinant identifies archimedean determinant norms. The library's
cyclic quotient index formula compares line degrees; the determinant then
gives the degree comparison in every rank.
-/

@[expose] public section
noncomputable section

section GramDeterminant

open TensorProduct
open scoped InnerProductSpace

namespace ArakelovGeometry.NormFamily

variable {K E : Type*} [Field K] {S : AdelicStructure K}
  [S.IsArchimedeanNormalized] [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- The square of the completed determinant norm is the real Gram determinant. -/
theorem determinant_norm_sq_eq_gram (ξ : NormFamily S E) (hξ : ξ.IsHermitian)
    (ω : S.Ω) (hω : ω ∈ S.Ωinf) :
    letI := (inferInstance : S.IsArchimedeanNormalized) ω hω
    letI := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
    letI := ξ.fibreNormedAddCommGroup ω
    letI := ξ.fibreNormedSpace ω
    letI := ξ.fiberInnerProductSpace ω hω
    ∀ x : Fin (Module.finrank K E) → (S.ϕ ω).Completion ⊗[K] E,
      (ξ.determinant.norm ω
        ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion E _).symm
          (exteriorPower.ιMulti (S.ϕ ω).Completion _ x))) ^ 2 =
        RCLike.re ((Matrix.of fun i j => inner (S.ϕ ω).Completion (x i) (x j)).det) := by
  let := (inferInstance : S.IsArchimedeanNormalized) ω hω
  let := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
  let := ξ.fibreNormedAddCommGroup ω
  let := ξ.fibreNormedSpace ω
  let := ξ.fiberInnerProductSpace ω hω
  intro x
  obtain ⟨b, hb⟩ := hξ.exists_completedOrthonormalBasis_determinant_norm_eq_one ξ ω hω
  have hw : exteriorPower.ιMulti (S.ϕ ω).Completion (Module.finrank K E) x =
      b.toBasis.det x • exteriorPower.ιMulti (S.ϕ ω).Completion (Module.finrank K E) b := by
    apply (determinantCoordinateEquiv b.toBasis).injective
    rw [map_smul, determinantCoordinateEquiv_ιMulti, determinantCoordinateEquiv_ιMulti,
      ← OrthonormalBasis.coe_toBasis, Module.Basis.det_self, smul_eq_mul, mul_one]
  rw [hw, map_smul, ξ.determinant.norm_smul, hb, mul_one]
  have hgram : (Matrix.of fun i j => inner (S.ϕ ω).Completion (x i) (x j)) =
      (b.toBasis.toMatrix x).conjTranspose * b.toBasis.toMatrix x := by
    ext i j
    simp [Matrix.mul_apply, Module.Basis.toMatrix_apply, b.repr_apply_apply,
      b.sum_inner_mul_inner]
  rw [hgram, Matrix.det_mul, Matrix.det_conjTranspose, Module.Basis.det_apply]
  simp only [RCLike.star_def, RCLike.mul_re, RCLike.conj_re, RCLike.conj_im,
    neg_mul, sub_neg_eq_add, RCLike.norm_sq_eq_def]

end ArakelovGeometry.NormFamily

end GramDeterminant

section LineDegree

set_option backward.isDefEq.respectTransparency false

open NumberField TensorProduct MeasureTheory
open ArakelovGeometry ArakelovGeometry.AdelicStructure
  ArakelovGeometry.ActualPrimeIndexing ArakelovGeometry.NumberFieldFullLattice

namespace BostConjecture.Arithmetic.HermitianMetric

attribute [local instance 2000] Algebra.toModule Algebra.toSMul

variable {K M : Type*} [Field K] [NumberField K]
  [AddCommGroup M] [Module (𝓞 K) M]
  [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]

/-- The section formula uses the library's cyclic quotient index for fractional ideals. -/
theorem lineDegree_eq [Nontrivial M] (h : HermitianMetric K M)
    (hrank : Module.finrank K (K ⊗[𝓞 K] M) = 1) {x : M} (hx : x ≠ 0) :
    h.lineDegree hrank =
      (Real.log (Nat.card (M ⧸ (𝓞 K ∙ x))) -
        archLog (fun v => h.sectionNorm v.embedding x)) / (Module.finrank ℚ K : ℝ) := by
  let f := lineCoordinate (M := M) hrank
  have hf := lineCoordinate_injective (M := M) hrank
  let e : M ≃ₗ[𝓞 K] (coordinateIdeal f).val := LinearEquiv.ofInjective f hf
  have hc := NumberFieldLineIndex.fractionalIdeal_cyclicQuotient_log_card
    (coordinateIdeal f) (coordinateIdeal_ne_zero f hf) (e x)
    (e.map_ne_zero_iff.mpr hx)
  rw [← NumberFieldBoundedIndex.cyclicQuotient_card_eq e x] at hc
  rw [h.lineDegree_eq_normRatio hrank f hf hx, Real.log_div
    (ne_of_gt (idealNorm_pos (FractionalIdeal.spanSingleton_ne_zero_iff.mpr
      (fun he => hx (hf (by simpa using he))))))
    (ne_of_gt (idealNorm_pos (coordinateIdeal_ne_zero f hf))), hc]
  rfl

/-- The finite integral of the original lattice gauge is its actual cyclic index. -/
theorem toAdelicBundle_finite_integral (h : HermitianMetric K M)
    (hr : Module.finrank K (K ⊗[𝓞 K] M) = 1) (x : M) (hx : x ≠ 0) :
    (∫ ω in (normalizedNumberFieldAdelicStructure K).Ωfin,
      -h.toAdelicBundle.toNormFamily.logNorm ((1 : K) ⊗ₜ[𝓞 K] x) ω
        ∂(normalizedNumberFieldAdelicStructure K).v) =
      Real.log (Nat.card (M ⧸ (𝓞 K ∙ x))) := by
  have hf : IntegrableOn (fun ω =>
      -h.toAdelicBundle.toNormFamily.logNorm ((1 : K) ⊗ₜ[𝓞 K] x) ω)
      (normalizedNumberFieldAdelicStructure K).Ωfin
      (normalizedNumberFieldAdelicStructure K).v :=
    ((h.toAdelicBundle.integrable_logNorm _).neg.integrableOn)
  rw [normalized_finite_integral_eq_tsum _ hf]
  have hi := line_completedGauge_finite_log_index (genericLattice (K := K) M)
    (genericLattice_fg (K := K) M) (genericLattice_span (K := K) M) hr
    (genericLatticeEquiv (K := K) M x)
    ((genericLatticeEquiv (K := K) M).map_ne_zero_iff.mpr hx)
  rw [← NumberFieldBoundedIndex.cyclicQuotient_card_eq
    (genericLatticeEquiv (K := K) M) x] at hi
  convert hi using 1
  apply tsum_congr
  intro p
  change _ * -Real.log (h.adelicNormFamily.norm (normalizedPrimeParameter p) _) = _
  rw [adelicNormFamily, fullLatticeGaugeFamily_norm_prime]
  rfl

omit [Module.Projective (𝓞 K) M] in
/-- The infinite integral counts precisely the original infinite-place multiplicities. -/
theorem toAdelicBundle_infinite_integral (h : HermitianMetric K M) (x : M) :
    (∫ ω in (normalizedNumberFieldAdelicStructure K).Ωinf,
      h.toAdelicBundle.toNormFamily.logNorm ((1 : K) ⊗ₜ[𝓞 K] x) ω
        ∂(normalizedNumberFieldAdelicStructure K).v) =
      archLog (fun w => h.sectionNorm w.embedding x) := by
  rw [normalized_infinite_integral_eq_sum]
  change (∑ w : InfinitePlace K, (w.mult : ℝ) *
    Real.log (h.toAdelicBundle.norm (normalizedInfinitePlacePoint w)
      (1 ⊗ₜ[K] ((1 : K) ⊗ₜ[𝓞 K] x)))) = _
  apply Finset.sum_congr rfl
  intro w _
  exact congrArg (fun r : ℝ => (w.mult : ℝ) * Real.log r)
    (h.toAdelicBundle_norm_section w x)

/-- The actual line degree differs from the old normalized degree by `[K : ℚ]`. -/
theorem degree_toAdelicBundle_of_rank_one [Nontrivial M] (h : HermitianMetric K M)
    (hr : Module.finrank K (K ⊗[𝓞 K] M) = 1) :
    h.toAdelicBundle.degree = (Module.finrank ℚ K : ℝ) * h.lineDegree hr := by
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  have hxK : (1 : K) ⊗ₜ[𝓞 K] x ≠ 0 := by
    intro he
    apply hx
    apply Module.Flat.tensorProduct_mk_injective (𝓞 K) M K
    simpa only [TensorProduct.mk_apply, tmul_zero] using he
  rw [h.toAdelicBundle.degree_eq_vectorDegree_of_finrank_one hr ⟨_, hxK⟩,
    AdelicVectorBundle.vectorDegree, NormFamily.vectorDegree_eq_neg_integral,
    h.lineDegree_eq hr hx]
  have hd : (Module.finrank ℚ K : ℝ) ≠ 0 :=
    (Nat.cast_pos.mpr (Module.finrank_pos (R := ℚ) (M := K)) :
      (0 : ℝ) < Module.finrank ℚ K).ne'
  rw [mul_div_cancel₀ _ hd]
  have hsplit := integral_add_compl
    (normalizedNumberFieldAdelicStructure K).measurableSet_Ωinf
    (h.toAdelicBundle.integrable_logNorm ((1 : K) ⊗ₜ[𝓞 K] x))
  have hcompl : (normalizedNumberFieldAdelicStructure K).Ωinfᶜ =
      (normalizedNumberFieldAdelicStructure K).Ωfin := by
    simp only [Ωinf, Ωfin, Set.compl_ofPred, not_not]
  rw [hcompl, h.toAdelicBundle_infinite_integral x] at hsplit
  have hfin := h.toAdelicBundle_finite_integral hr x hx
  rw [integral_neg] at hfin
  linarith

end BostConjecture.Arithmetic.HermitianMetric

end LineDegree

section DegreeComparison

set_option backward.isDefEq.respectTransparency false

open NumberField TensorProduct MeasureTheory exteriorPower
open scoped InnerProductSpace
open ArakelovGeometry ArakelovGeometry.AdelicStructure
  ArakelovGeometry.ActualPrimeIndexing ArakelovGeometry.NumberFieldArchimedeanDiagonal

namespace BostConjecture.Arithmetic.HermitianMetric
attribute [local instance 2000] Algebra.toModule Algebra.toSMul

variable {K M : Type*} [Field K] [NumberField K]
  [AddCommGroup M] [Module (𝓞 K) M] [Module.Finite (𝓞 K) M]

/-- The adelic determinant norm of an integral wedge is its original Gram norm. -/
theorem infinite_norm_determinant_wedge (h : HermitianMetric K M) (w : InfinitePlace K)
    (x : Fin (Module.finrank K (K ⊗[𝓞 K] M)) → M) :
    h.adelicNormFamily.determinant.norm (normalizedInfinitePlacePoint w)
      (1 ⊗ₜ[K] (determinantGenericEquiv (K := K) M
        ((1 : K) ⊗ₜ[𝓞 K] ιMulti (𝓞 K) _ x))) =
      h.determinant.sectionNorm w.embedding (ιMulti (𝓞 K) _ x) := by
  let := (inferInstance : (normalizedNumberFieldAdelicStructure K).IsArchimedeanNormalized)
    (normalizedInfinitePlacePoint w) (normalizedInfinitePlacePoint_mem_inf w)
  let := IsRCLikeNormedField.rclike (ClassicalCompletion w)
  let := h.adelicNormFamily.fibreNormedAddCommGroup (normalizedInfinitePlacePoint w)
  let := h.adelicNormFamily.fibreNormedSpace (normalizedInfinitePlacePoint w)
  let := h.adelicNormFamily.fiberInnerProductSpace
    (normalizedInfinitePlacePoint w) (normalizedInfinitePlacePoint_mem_inf w)
  let v (i : Fin (Module.finrank K (K ⊗[𝓞 K] M))) :=
    (1 : ClassicalCompletion w) ⊗ₜ[K] ((1 : K) ⊗ₜ[𝓞 K] x i)
  have hg := h.adelicNormFamily.determinant_norm_sq_eq_gram
    h.toAdelicBundle_isHermitian (normalizedInfinitePlacePoint w)
    (normalizedInfinitePlacePoint_mem_inf w) v
  have he : (exteriorBaseChangeEquiv K (ClassicalCompletion w) (K ⊗[𝓞 K] M) _).symm
      (ιMulti (ClassicalCompletion w) _ v) =
      1 ⊗ₜ[K] (determinantGenericEquiv (K := K) M
        ((1 : K) ⊗ₜ[𝓞 K] ιMulti (𝓞 K) _ x)) := by
    simp only [v, determinantGenericEquiv, exteriorPower.baseChangeEquiv_apply_tmul,
      exteriorBaseChangeEquiv_symm_ιMulti_tmul, Finset.prod_const_one]
    rfl
  rw [he] at hg
  have hm : (Matrix.of fun i j => inner (ClassicalCompletion w) (v i) (v j)).map
      (classicalCompletionEmbedding w) =
      (Matrix.of fun i j => (h.fiber w.embedding).inner
        (fiberSection M w.embedding (x i)) (fiberSection M w.embedding (x j))) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.of_apply, h.completedFiber_inner, v,
      classicalCompletedFiberMap_tmul, map_one, mul_one, one_smul]
  have hd := h.determinant_sectionNorm_wedge_sq w.embedding x
  rw [← hm] at hd
  have hmap := (classicalCompletionEmbedding w).map_det
    (Matrix.of fun i j => inner (ClassicalCompletion w) (v i) (v j))
  change classicalCompletionEmbedding w _ =
    ((Matrix.of fun i j => inner (ClassicalCompletion w) (v i) (v j)).map
      (classicalCompletionEmbedding w)).det at hmap
  rw [← hmap, complexEmbedding_re _ (norm_classicalCompletionEmbedding w)] at hd
  have hn := h.adelicNormFamily.determinant.norm_nonneg
    (normalizedInfinitePlacePoint w)
    (1 ⊗ₜ[K] determinantGenericEquiv (K := K) M ((1 : K) ⊗ₜ[𝓞 K] ιMulti (𝓞 K) _ x))
  have hn' : 0 ≤ h.determinant.sectionNorm w.embedding (ιMulti (𝓞 K) _ x) := Real.sqrt_nonneg _
  nlinarith

omit [NumberField K] in
/-- A top exterior power has a nonzero integral wedge. -/
theorem exists_integral_determinant_wedge :
    ∃ x : Fin (Module.finrank K (K ⊗[𝓞 K] M)) → M, ιMulti (𝓞 K) _ x ≠ 0 := by
  classical
  by_contra! hx
  have ht : (⊤ : Submodule (𝓞 K) (DeterminantLine (K := K) M)) ≤ ⊥ := by
    rw [← ιMulti_span]
    apply Submodule.span_le.mpr
    rintro z ⟨x, rfl⟩
    change ιMulti (𝓞 K) _ x = 0
    exact hx x
  exact top_ne_bot (le_antisymm ht bot_le)

variable [Module.Projective (𝓞 K) M]

/-- Adelization preserves the old degree, with exactly its original normalization. -/
theorem degree_toAdelicBundle (h : HermitianMetric K M) :
    h.toAdelicBundle.degree = (Module.finrank ℚ K : ℝ) * h.degree := by
  obtain ⟨x, hx⟩ := exists_integral_determinant_wedge (K := K) (M := M)
  let ξ := ιMulti (𝓞 K) (Module.finrank K (K ⊗[𝓞 K] M)) x
  have hξ : (1 : K) ⊗ₜ[𝓞 K] ξ ≠ 0 := by
    intro he
    apply hx
    apply Module.Flat.tensorProduct_mk_injective (𝓞 K) (DeterminantLine (K := K) M) K
    simpa only [TensorProduct.mk_apply, tmul_zero] using he
  let e := determinantGenericEquiv (K := K) M
  have he : e ((1 : K) ⊗ₜ[𝓞 K] ξ) ≠ 0 := e.map_ne_zero_iff.mpr hξ
  have hn (ω : (normalizedNumberFieldAdelicStructure K).Ω) :
      h.adelicNormFamily.determinant.norm ω
        (1 ⊗ₜ[K] e ((1 : K) ⊗ₜ[𝓞 K] ξ)) =
      h.determinant.toAdelicBundle.norm ω (1 ⊗ₜ[K] ((1 : K) ⊗ₜ[𝓞 K] ξ)) := by
    by_cases hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωfin
    · obtain ⟨p, rfl⟩ := exists_normalizedPrimeParameter_eq ω hω
      simpa only [LinearEquiv.baseChange_tmul] using
        h.finite_norm_determinant p (1 ⊗ₜ[K] ((1 : K) ⊗ₜ[𝓞 K] ξ))
    · have hi : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωinf := hω
      obtain ⟨w, rfl⟩ : ∃ w : InfinitePlace K, normalizedInfinitePlacePoint w = ω := by
        simpa only [normalizedNumberFieldAdelicStructure_Ωinf_eq_range, Set.mem_range] using hi
      rw [h.determinant.toAdelicBundle_norm_section]
      exact h.infinite_norm_determinant_wedge w x
  calc
    h.toAdelicBundle.degree = h.determinant.toAdelicBundle.degree := by
      rw [h.toAdelicBundle.degree_eq_neg_integral ⟨_, he⟩,
        h.determinant.toAdelicBundle.degree_eq_vectorDegree_of_finrank_one
          (determinant_generic_finrank (K := K) M) ⟨_, hξ⟩,
        AdelicVectorBundle.vectorDegree, NormFamily.vectorDegree_eq_neg_integral]
      congr 1
      apply integral_congr_ae
      filter_upwards [] with ω
      exact congrArg Real.log (hn ω)
    _ = (Module.finrank ℚ K : ℝ) * h.degree :=
      h.determinant.degree_toAdelicBundle_of_rank_one (determinant_generic_finrank M)

end BostConjecture.Arithmetic.HermitianMetric

end DegreeComparison
