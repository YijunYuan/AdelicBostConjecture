/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Line.Hermitian
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody

/-!
# Short integral sections of intrinsic Hermitian lines

The canonical mixed-embedding Minkowski theorem applied to a weighted box
gives a uniform section bound in terms of the actual intrinsic line degree.
No principal ideal or integral freeness assumption is made.
-/

@[expose] public section

noncomputable section

open NumberField NumberField.mixedEmbedding MeasureTheory TensorProduct
open scoped nonZeroDivisors NNReal ENNReal

namespace BostConjecture.Arithmetic

variable {K : Type*} [Field K] [NumberField K]

lemma minkowskiBound_eq_norm_mul (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    minkowskiBound K I = ENNReal.ofReal (FractionalIdeal.absNorm I.val : ℝ) *
      minkowskiBound K 1 := by
  rw [minkowskiBound, volume_fundamentalDomain_fractionalIdealLatticeBasis,
    minkowskiBound, volume_fundamentalDomain_fractionalIdealLatticeBasis]
  simp [mul_assoc]

/-- A positive constant depending only on the number field. -/
def lineMinkowskiConstant (K : Type*) [Field K] [NumberField K] : ℝ :=
  Real.exp ((Real.log (minkowskiBound K 1).toReal + 1) / Module.finrank ℚ K)

lemma lineMinkowskiConstant_pos : 0 < lineMinkowskiConstant K := Real.exp_pos _

/-- The weighted archimedean box has the exponential product prescribed by degree. -/
lemma prod_exp_weighted (t : ℝ) (ρ : InfinitePlace K → ℝ) :
    (∏ v : InfinitePlace K, Real.exp (t - Real.log (ρ v)) ^ v.mult) =
      Real.exp ((Module.finrank ℚ K : ℝ) * t - archLog ρ) := by
  simp_rw [← Real.exp_nat_mul]
  rw [← Real.exp_sum]
  congr 1
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, archLog]
  congr 2
  exact_mod_cast InfinitePlace.sum_mult_eq (K := K)

/-- Minkowski supplies a small element of every nonzero fractional ideal with
arbitrary positive archimedean weights. -/
theorem exists_small_ideal_element (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0)
    (ρ : InfinitePlace K → ℝ) (hρ : ∀ v, 0 < ρ v) :
    ∃ a ∈ I, a ≠ 0 ∧ ∀ v : InfinitePlace K,
      v a * ρ v < lineMinkowskiConstant K * Real.exp (-lineDegree I ρ) := by
  classical
  let J : (FractionalIdeal (𝓞 K)⁰ K)ˣ := Units.mk0 I hI
  let B := (minkowskiBound K 1).toReal
  have hB : 0 < B := ENNReal.toReal_pos (minkowskiBound_pos K 1).ne'
    (minkowskiBound_lt_top K 1).ne
  have hD : (Module.finrank ℚ K : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'
  let t := (Real.log B + 1) / (Module.finrank ℚ K : ℝ) - lineDegree I ρ
  let f (v : InfinitePlace K) : ℝ≥0 := ⟨Real.exp (t - Real.log (ρ v)), (Real.exp_pos _).le⟩
  have ht : (Module.finrank ℚ K : ℝ) * t - archLog ρ =
      Real.log B + 1 + Real.log (FractionalIdeal.absNorm I : ℝ) := by
    dsimp [t, lineDegree, logIdealNorm]
    field_simp
    ring
  have hprod : (∏ v : InfinitePlace K, (f v : ℝ) ^ v.mult) =
      B * Real.exp 1 * (FractionalIdeal.absNorm I : ℝ) := by
    change (∏ v : InfinitePlace K, Real.exp (t - Real.log (ρ v)) ^ v.mult) = _
    rw [prod_exp_weighted, ht, Real.exp_add, Real.exp_add,
      Real.exp_log hB, Real.exp_log (idealNorm_pos hI)]
  have hbound : minkowskiBound K J < volume (convexBodyLT K f) := by
    rw [convexBodyLT_volume]
    apply lt_of_lt_of_le (b := ∏ v : InfinitePlace K, (f v : ℝ≥0∞) ^ v.mult)
    · rw [minkowskiBound_eq_norm_mul]
      have he : (∏ v : InfinitePlace K, (f v : ℝ≥0∞) ^ v.mult) =
          ENNReal.ofReal (B * Real.exp 1 * (FractionalIdeal.absNorm I : ℝ)) := by
        rw [← hprod]
        simp [ENNReal.ofReal_prod_of_nonneg, ENNReal.ofReal_pow]
      rw [he, ← ENNReal.ofReal_toReal (minkowskiBound_lt_top K 1).ne]
      change ENNReal.ofReal (FractionalIdeal.absNorm I : ℝ) * ENNReal.ofReal B < _
      rw [← ENNReal.ofReal_mul (idealNorm_pos hI).le]
      apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg
        (mul_nonneg (idealNorm_pos hI).le hB.le)).mpr
      have he1 : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
      calc
        (FractionalIdeal.absNorm I : ℝ) * B = B * 1 * (FractionalIdeal.absNorm I : ℝ) := by ring
        _ < B * Real.exp 1 * (FractionalIdeal.absNorm I : ℝ) :=
          mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left he1 hB) (idealNorm_pos hI)
    · simp only [ENNReal.ofNNReal_finsetProd, ENNReal.coe_pow]
      exact le_mul_of_one_le_left' (by exact_mod_cast one_le_convexBodyLTFactor K)
  obtain ⟨a, ha, ha0, hab⟩ := exists_ne_zero_mem_ideal_lt K J hbound
  refine ⟨a, ha, ha0, fun v => ?_⟩
  have hv := mul_lt_mul_of_pos_right (hab v) (hρ v)
  change v a * ρ v < Real.exp (t - Real.log (ρ v)) * ρ v at hv
  rw [Real.exp_sub, Real.exp_log (hρ v), div_mul_cancel₀ _ (hρ v).ne'] at hv
  simpa only [t, lineMinkowskiConstant, Real.exp_sub, Real.exp_neg, div_eq_mul_inv] using hv

namespace HermitianMetric

variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]
variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M] [Nontrivial M]

/-- Every intrinsic Hermitian line admits a nonzero section bounded at all
embeddings by its normalized degree and a field-only constant. -/
theorem exists_small_section (h : HermitianMetric K M)
    (hr : Module.finrank K (K ⊗[𝓞 K] M) = 1) :
    ∃ y : M, y ≠ 0 ∧ ∀ σ : K →+* ℂ,
      h.sectionNorm σ y < lineMinkowskiConstant K * Real.exp (-h.lineDegree hr) := by
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  let f := lineCoordinate (M := M) hr
  have hf := lineCoordinate_injective (M := M) hr
  obtain ⟨a, ha, ha0, hab⟩ := exists_small_ideal_element
    (coordinateIdeal f) (coordinateIdeal_ne_zero f hf)
    (h.coordinateLength f x) (h.coordinateLength_pos f hf hx)
  obtain ⟨y, hy⟩ := (mem_coordinateIdeal f a).mp ha
  have hy0 : y ≠ 0 := fun he => ha0 (by simpa [he] using hy.symm)
  refine ⟨y, hy0, fun σ => ?_⟩
  let v := InfinitePlace.mk σ
  have he : h.sectionNorm σ y = h.sectionNorm v.embedding y :=
    h.sectionNorm_eq_of_place_eq (by simp [v]) y
  rw [he, h.lineDegree_eq_degreeInCoordinate hr f hf hx]
  change h.sectionNorm v.embedding y < lineMinkowskiConstant K *
    Real.exp (-BostConjecture.Arithmetic.lineDegree (coordinateIdeal f) (h.coordinateLength f x))
  have hlength := congrFun (h.coordinateLength_eq f hf hy0 hx) v
  change h.sectionNorm v.embedding y / v (f y) = h.coordinateLength f x v at hlength
  have hv : v (f y) ≠ 0 := (InfinitePlace.pos_iff.mpr (hy ▸ ha0)).ne'
  rw [(div_eq_iff hv).mp hlength, mul_comm, hy]
  exact hab v

end HermitianMetric
end BostConjecture.Arithmetic
