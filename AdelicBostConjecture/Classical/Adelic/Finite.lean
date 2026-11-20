/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import AdelicBostConjecture.Classical.Adelic.Bundle

/-! # Finite-place comparisons for the original integral lattice -/

@[expose] public section
noncomputable section

open NumberField TensorProduct IsDedekindDomain
open ArakelovGeometry ArakelovGeometry.AdelicStructure
  ArakelovGeometry.ActualPrimeIndexing ArakelovGeometry.NumberFieldFullLattice

namespace AdelicBostConjecture.Arithmetic

attribute [local instance 2000] Algebra.toModule Algebra.toSMul

variable {K : Type*} [Field K] [NumberField K]

abbrev FiniteCompletion (p : HeightOneSpectrum (𝓞 K)) :=
  ((normalizedNumberFieldAdelicStructure K).ϕ (normalizedPrimeParameter p)).Completion

abbrev FiniteIntegers (p : HeightOneSpectrum (𝓞 K)) :=
  (normalizedNumberFieldAdelicStructure K).completedLocalRing
    (normalizedPrimeParameter p) (normalizedPrimeParameter_mem_fin p)

section Gauge

variable {E : Type*} [AddCommGroup E] [Module K E]

/-- An ultrametric seminorm bounded on integral generators is bounded on their
completed integral span. -/
theorem seminorm_le_one_on_completedSpan (L : Submodule (𝓞 K) E)
    (p : HeightOneSpectrum (𝓞 K))
    (q : Seminorm (FiniteCompletion p) (FiniteCompletion p ⊗[K] E))
    (hq : ∀ x y, q (x + y) ≤ max (q x) (q y))
    (hL : ∀ x : L, q (1 ⊗ₜ[K] (x : E)) ≤ 1)
    {z : FiniteCompletion p ⊗[K] E}
    (hz : z ∈ NumberFieldModel.completedLatticeSpan L p) : q z ≤ 1 := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨x, rfl⟩ := hx
    exact hL x
  | zero => simp
  | add x y _ _ hx hy => exact (hq x y).trans (max_le hx hy)
  | smul a x _ hx =>
    change q ((a : FiniteCompletion p) • x) ≤ 1
    rw [map_smul_eq_mul]
    have ha : ‖(a : FiniteCompletion p)‖ ≤ 1 :=
      ((normalizedNumberFieldAdelicStructure K).mem_completedLocalRing _ _ _).mp a.property
    exact (mul_le_mul_of_nonneg_left hx (norm_nonneg _)).trans (by simpa using ha)

/-- A full integral lattice has an admissible scalar at every completed vector. -/
theorem completedGaugeValues_nonempty (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤) (p : HeightOneSpectrum (𝓞 K))
    (z : FiniteCompletion p ⊗[K] E) :
    (scalarLatticeGaugeValues (F := FiniteCompletion p)
      (NumberFieldModel.completedLatticeSpan L p : Set _) z).Nonempty := by
  rw [completedLatticeSpan_eq_localBasis L hfg hspan p]
  exact scalarLatticeGaugeValues_basisCoordinateLattice_nonempty (FiniteIntegers p)
    (fun a => (normalizedNumberFieldAdelicStructure K).mem_completedLocalRing _ _ a)
    ((rationalLocalGenericBasis L hfg hspan p).baseChange (FiniteCompletion p)) z

/-- The lattice gauge is maximal among ultrametric seminorms bounded by one on
the original integral sections. -/
theorem seminorm_le_completedGauge (L : Submodule (𝓞 K) E) (hfg : L.FG)
    (hspan : Submodule.span K (L : Set E) = ⊤) (p : HeightOneSpectrum (𝓞 K))
    (q : Seminorm (FiniteCompletion p) (FiniteCompletion p ⊗[K] E))
    (hq : ∀ x y, q (x + y) ≤ max (q x) (q y))
    (hL : ∀ x : L, q (1 ⊗ₜ[K] (x : E)) ≤ 1)
    (z : FiniteCompletion p ⊗[K] E) :
    q z ≤ scalarLatticeGauge (F := FiniteCompletion p)
      (NumberFieldModel.completedLatticeSpan L p : Set _) z := by
  apply le_csInf (completedGaugeValues_nonempty L hfg hspan p z)
  rintro r ⟨a, ha, haz, rfl⟩
  have hb := seminorm_le_one_on_completedSpan L p q hq hL haz
  rw [map_smul_eq_mul, norm_inv] at hb
  exact (inv_mul_le_iff₀ (norm_pos_iff.mpr ha)).mp hb |>.trans_eq (mul_one _)

end Gauge

/-- A bound on integral generators extends to their integral span. -/
theorem seminorm_le_one_on_integral_span {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]
    (p : HeightOneSpectrum (𝓞 K))
    (q : Seminorm (FiniteCompletion p) (FiniteCompletion p ⊗[K] (K ⊗[𝓞 K] M)))
    (hq : ∀ x y, q (x + y) ≤ max (q x) (q y)) (s : Set M)
    (hs : ∀ x ∈ s, q (1 ⊗ₜ[K] ((1 : K) ⊗ₜ[𝓞 K] x)) ≤ 1)
    {x : M} (hx : x ∈ Submodule.span (𝓞 K) s) :
    q (1 ⊗ₜ[K] ((1 : K) ⊗ₜ[𝓞 K] x)) ≤ 1 := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero => simp
  | add x y _ _ hx hy =>
    simpa only [tmul_add] using (hq (1 ⊗ₜ[K] ((1 : K) ⊗ₜ[𝓞 K] x))
      (1 ⊗ₜ[K] ((1 : K) ⊗ₜ[𝓞 K] y))).trans (max_le hx hy)
  | smul a x _ hx =>
    let c := (normalizedNumberFieldAdelicStructure K).integralCompletedLocalCoefficientMap
      (normalizedPrimeParameter p) (normalizedPrimeParameter_mem_fin p) a
    have hc : ‖(c : FiniteCompletion p)‖ ≤ 1 :=
      ((normalizedNumberFieldAdelicStructure K).mem_completedLocalRing _ _ _).mp c.property
    have he : (1 : FiniteCompletion p) ⊗ₜ[K] ((1 : K) ⊗ₜ[𝓞 K] (a • x)) =
        (c : FiniteCompletion p) • (1 ⊗ₜ[K] ((1 : K) ⊗ₜ[𝓞 K] x)) := by
      change _ = (algebraMap K (FiniteCompletion p) (algebraMap (𝓞 K) K a)) • _
      rw [IsScalarTower.algebraMap_smul, ← tmul_smul]
      congr 1
      rw [tmul_smul, smul_tmul']
      simp only [Algebra.smul_def, smul_tmul', mul_one, Algebra.algebraMap_self, RingHom.id_apply]
    rw [he, map_smul_eq_mul]
    exact (mul_le_mul hc hx (apply_nonneg q _) zero_le_one).trans_eq (mul_one _)

namespace HermitianMetric

variable {M N : Type*} [AddCommGroup M] [Module (𝓞 K) M]
  [AddCommGroup N] [Module (𝓞 K) N]
  [Module.Finite (𝓞 K) M] [Module.Finite (𝓞 K) N]

/-- The adelic norm at a prime is the gauge of the completed integral lattice. -/
theorem finite_norm_eq_gauge (h : HermitianMetric K M)
    (p : HeightOneSpectrum (𝓞 K)) (z : FiniteCompletion p ⊗[K] (K ⊗[𝓞 K] M)) :
    h.toAdelicBundle.norm (normalizedPrimeParameter p) z =
      scalarLatticeGauge (F := FiniteCompletion p)
        (X := FiniteCompletion p ⊗[K] (K ⊗[𝓞 K] M))
        (NumberFieldModel.completedLatticeSpan (K := K) (E := K ⊗[𝓞 K] M)
          (genericLattice (K := K) M) p).carrier z :=
  @fullLatticeGaugeFamily_norm_prime K inferInstance inferInstance
    (K ⊗[𝓞 K] M) inferInstance inferInstance
    (genericLattice (K := K) M) (genericLattice_fg (K := K) M)
    (genericLattice_span (K := K) M) h.archimedeanNormFamily p z

/-- The finite unit ball is the completed span of the original integral sections. -/
theorem finite_norm_le_one_iff (h : HermitianMetric K M)
    (p : HeightOneSpectrum (𝓞 K)) (z : FiniteCompletion p ⊗[K] (K ⊗[𝓞 K] M)) :
    h.toAdelicBundle.norm (normalizedPrimeParameter p) z ≤ 1 ↔
      z ∈ NumberFieldModel.completedLatticeSpan (K := K) (E := K ⊗[𝓞 K] M)
          (genericLattice (K := K) M) p := by
  rw [h.finite_norm_eq_gauge]
  exact @scalarLatticeGauge_le_one_iff_completedLatticeSpan K inferInstance inferInstance
    (K ⊗[𝓞 K] M) inferInstance inferInstance
    (genericLattice (K := K) M) (genericLattice_fg (K := K) M)
    (genericLattice_span (K := K) M) p z

/-- Every original integral section belongs to the finite unit ball. -/
theorem finite_norm_section_le_one (h : HermitianMetric K M)
    (p : HeightOneSpectrum (𝓞 K)) (x : M) :
    h.toAdelicBundle.norm (normalizedPrimeParameter p)
      (1 ⊗ₜ[K] ((1 : K) ⊗ₜ[𝓞 K] x)) ≤ 1 := by
  apply (h.finite_norm_le_one_iff p _).mpr
  change (1 : FiniteCompletion p) ⊗ₜ[K] ((1 : K) ⊗ₜ[𝓞 K] x) ∈
    Submodule.span (FiniteIntegers p) (Set.range fun v : genericLattice (K := K) M =>
      (1 : FiniteCompletion p) ⊗ₜ[K] (show K ⊗[𝓞 K] M from v.val))
  exact Submodule.subset_span ⟨⟨_, x, rfl⟩, rfl⟩

/-- A linear map bounded on integral sections contracts the finite norm into an
ultrametric seminorm. -/
theorem finite_seminorm_le (h : HermitianMetric K M) (p : HeightOneSpectrum (𝓞 K))
    {E : Type*} [AddCommGroup E] [Module (FiniteCompletion p) E]
    (q : Seminorm (FiniteCompletion p) E)
    (f : (FiniteCompletion p ⊗[K] (K ⊗[𝓞 K] M)) →ₗ[FiniteCompletion p] E)
    (hq : ∀ x y, q (x + y) ≤ max (q x) (q y))
    (hM : ∀ x : M, q (f (1 ⊗ₜ[K] ((1 : K) ⊗ₜ[𝓞 K] x))) ≤ 1)
    (z : FiniteCompletion p ⊗[K] (K ⊗[𝓞 K] M)) :
    q (f z) ≤ h.toAdelicBundle.norm (normalizedPrimeParameter p) z := by
  rw [h.finite_norm_eq_gauge]
  exact seminorm_le_completedGauge (K := K) (E := K ⊗[𝓞 K] M) (genericLattice (K := K) M)
    (genericLattice_fg (K := K) M) (genericLattice_span (K := K) M) p (q.comp f)
    (fun x y => by simpa only [Seminorm.comp_apply, map_add] using hq (f x) (f y))
    (by rintro ⟨_, x, rfl⟩; exact hM x) z

/-- Finite lattice norms admit exact scalar normalization. -/
theorem finite_norm_exists_scalar (h : HermitianMetric K M)
    (p : HeightOneSpectrum (𝓞 K)) (z : FiniteCompletion p ⊗[K] (K ⊗[𝓞 K] M))
    (hz : z ≠ 0) : ∃ a : FiniteCompletion p, a ≠ 0 ∧
      h.toAdelicBundle.norm (normalizedPrimeParameter p) (a⁻¹ • z) ≤ 1 ∧
      ‖a‖ = h.toAdelicBundle.norm (normalizedPrimeParameter p) z := by
  let L := genericLattice (K := K) M
  let b := rationalLocalGenericBasis (K := K) (E := K ⊗[𝓞 K] M) L (genericLattice_fg (K := K) M)
    (genericLattice_span (K := K) M) p
  obtain ⟨a, ha, hb, hc⟩ := exists_attaining_basisCoordinateLattice_scalar
    (FiniteIntegers p)
    (fun a => (normalizedNumberFieldAdelicStructure K).mem_completedLocalRing _ _ a)
    (b.baseChange (FiniteCompletion p)) hz
  refine ⟨a, ha, ?_, ?_⟩
  · rw [finite_norm_le_one_iff, completedLatticeSpan_eq_localBasis (K := K) (E := K ⊗[𝓞 K] M) L
      (genericLattice_fg (K := K) M) (genericLattice_span (K := K) M)]
    exact hb
  · rw [h.finite_norm_eq_gauge]
    exact hc.trans (scalarLatticeGauge_eq_localBasisNorm (K := K) (E := K ⊗[𝓞 K] M) L
      (genericLattice_fg (K := K) M) (genericLattice_span (K := K) M) p z).symm

/-- Integral linear maps contract all finite norms. -/
theorem finite_norm_baseChange_le (h : HermitianMetric K M) (g : HermitianMetric K N)
    (f : M →ₗ[𝓞 K] N) (p : HeightOneSpectrum (𝓞 K))
    (z : FiniteCompletion p ⊗[K] (K ⊗[𝓞 K] M)) :
    g.toAdelicBundle.norm (normalizedPrimeParameter p)
      ((f.baseChange K).baseChange (FiniteCompletion p) z) ≤
        h.toAdelicBundle.norm (normalizedPrimeParameter p) z := by
  let F := (f.baseChange K).baseChange (FiniteCompletion p)
  exact h.finite_seminorm_le p (g.toAdelicBundle.norm (normalizedPrimeParameter p)) F
    (g.toAdelicBundle_isHermitian.1 _ (normalizedPrimeParameter_mem_fin p))
    (fun x => g.finite_norm_section_le_one p (f x)) z

end HermitianMetric
end AdelicBostConjecture.Arithmetic
