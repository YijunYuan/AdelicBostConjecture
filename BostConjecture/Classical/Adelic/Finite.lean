/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Classical.Adelic.Bundle

/-! # Finite-place comparisons for the original integral lattice -/

@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false

open NumberField TensorProduct IsDedekindDomain
open ArakelovGeometry ArakelovGeometry.AdelicStructure
  ArakelovGeometry.ActualPrimeIndexing ArakelovGeometry.NumberFieldFullLattice

namespace BostConjecture.Arithmetic

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

namespace HermitianMetric

variable {M N : Type*} [AddCommGroup M] [Module (𝓞 K) M]
  [AddCommGroup N] [Module (𝓞 K) N]
  [Module.Finite (𝓞 K) M] [Module.Finite (𝓞 K) N]

/-- Every original integral section belongs to the finite unit ball. -/
theorem finite_norm_section_le_one (h : HermitianMetric K M)
    (p : HeightOneSpectrum (𝓞 K)) (x : M) :
    h.toAdelicBundle.norm (normalizedPrimeParameter p)
      (1 ⊗ₜ[K] ((1 : K) ⊗ₜ[𝓞 K] x)) ≤ 1 := by
  change h.adelicNormFamily.norm _ _ ≤ _
  rw [adelicNormFamily, fullLatticeGaugeFamily_norm_prime,
    scalarLatticeGauge_le_one_iff_completedLatticeSpan (genericLattice (K := K) M)
      (genericLattice_fg (K := K) M) (genericLattice_span (K := K) M)]
  exact Submodule.subset_span ⟨⟨_, x, rfl⟩, rfl⟩

/-- The finite unit ball is the completed span of the original integral sections. -/
theorem finite_norm_le_one_iff (h : HermitianMetric K M)
    (p : HeightOneSpectrum (𝓞 K)) (z : FiniteCompletion p ⊗[K] (K ⊗[𝓞 K] M)) :
    h.toAdelicBundle.norm (normalizedPrimeParameter p) z ≤ 1 ↔
      z ∈ NumberFieldModel.completedLatticeSpan (genericLattice (K := K) M) p := by
  change h.adelicNormFamily.norm _ _ ≤ 1 ↔ _
  rw [adelicNormFamily, fullLatticeGaugeFamily_norm_prime]
  exact scalarLatticeGauge_le_one_iff_completedLatticeSpan _
    (genericLattice_fg (K := K) M) (genericLattice_span (K := K) M) p z

/-- Finite lattice norms admit exact scalar normalization. -/
theorem finite_norm_exists_scalar (h : HermitianMetric K M)
    (p : HeightOneSpectrum (𝓞 K)) (z : FiniteCompletion p ⊗[K] (K ⊗[𝓞 K] M))
    (hz : z ≠ 0) : ∃ a : FiniteCompletion p, a ≠ 0 ∧
      h.toAdelicBundle.norm (normalizedPrimeParameter p) (a⁻¹ • z) ≤ 1 ∧
      ‖a‖ = h.toAdelicBundle.norm (normalizedPrimeParameter p) z := by
  let L := genericLattice (K := K) M
  let b := rationalLocalGenericBasis L (genericLattice_fg (K := K) M)
    (genericLattice_span (K := K) M) p
  obtain ⟨a, ha, hb, hc⟩ := exists_attaining_basisCoordinateLattice_scalar
    (FiniteIntegers p)
    (fun a => (normalizedNumberFieldAdelicStructure K).mem_completedLocalRing _ _ a)
    (b.baseChange (FiniteCompletion p)) hz
  refine ⟨a, ha, ?_, ?_⟩
  · rw [finite_norm_le_one_iff, completedLatticeSpan_eq_localBasis L
      (genericLattice_fg (K := K) M) (genericLattice_span (K := K) M)]
    exact hb
  · change ‖a‖ = h.adelicNormFamily.norm _ _
    rw [adelicNormFamily, fullLatticeGaugeFamily_norm_prime,
      scalarLatticeGauge_eq_localBasisNorm L (genericLattice_fg (K := K) M)
        (genericLattice_span (K := K) M)]
    exact hc

/-- Integral linear maps contract all finite norms. -/
theorem finite_norm_baseChange_le (h : HermitianMetric K M) (g : HermitianMetric K N)
    (f : M →ₗ[𝓞 K] N) (p : HeightOneSpectrum (𝓞 K))
    (z : FiniteCompletion p ⊗[K] (K ⊗[𝓞 K] M)) :
    g.toAdelicBundle.norm (normalizedPrimeParameter p)
      ((f.baseChange K).baseChange (FiniteCompletion p) z) ≤
        h.toAdelicBundle.norm (normalizedPrimeParameter p) z := by
  let F := (f.baseChange K).baseChange (FiniteCompletion p)
  let q := (g.toAdelicBundle.norm (normalizedPrimeParameter p)).comp F
  have hq : ∀ x y, q (x + y) ≤ max (q x) (q y) := by
    intro x y
    change g.toAdelicBundle.norm _ (F (x + y)) ≤ _
    rw [map_add]
    exact g.toAdelicBundle_isHermitian.1 _ (normalizedPrimeParameter_mem_fin p) _ _
  have hL : ∀ x : genericLattice (K := K) M, q (1 ⊗ₜ[K] (x : K ⊗[𝓞 K] M)) ≤ 1 := by
    rintro ⟨_, x, rfl⟩
    exact g.finite_norm_section_le_one p (f x)
  have hb := seminorm_le_completedGauge (genericLattice (K := K) M)
    (genericLattice_fg (K := K) M) (genericLattice_span (K := K) M) p q hq hL z
  change q z ≤ h.adelicNormFamily.norm _ _
  rw [adelicNormFamily, fullLatticeGaugeFamily_norm_prime]
  exact hb

end HermitianMetric
end BostConjecture.Arithmetic
