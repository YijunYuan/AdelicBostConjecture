/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.RestrictionCovolume.TraceSpace
public import BostConjecture.Arithmetic.HN.Semistable

/-!
# The systole of a normalized semistable arithmetic trace lattice

Semistability on the saturated generic line through a nonzero section gives
a nonnegative sum of logarithms of its actual fiber norms. The elementary
logarithm inequality then bounds the squared trace norm below by the degree
of the number field.

Reference: this paper, page 11, Lemma 7.1.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace BostConjecture.Arithmetic.HermitianMetric

variable {K : Type*} [Field K] [NumberField K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]
variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]

/-- A nonzero integral section of a normalized semistable module has
nonnegative logarithmic archimedean norm product. -/
theorem IsSemistable.sum_log_sectionNorm_nonneg {h : HermitianMetric K M}
    (hs : h.IsSemistable) (h0 : h.degree = 0) {x : M} (hx : x ≠ 0) :
    0 ≤ ∑ σ : K →+* ℂ, Real.log (h.sectionNorm σ x) := by
  have hgen : (1 : K) ⊗ₜ[𝓞 K] x ≠ 0 := by
    intro hz
    apply hx
    apply Module.Flat.tensorProduct_mk_injective (𝓞 K) M K
    change (1 : K) ⊗ₜ[𝓞 K] x = (1 : K) ⊗ₜ[𝓞 K] 0
    simpa only [TensorProduct.tmul_zero] using hz
  let X : Submodule K (K ⊗[𝓞 K] M) := K ∙ ((1 : K) ⊗ₜ[𝓞 K] x)
  let P := integralPart X
  let y : P := ⟨x, Submodule.subset_span (Set.mem_singleton _)⟩
  have hy : y ≠ 0 := fun hy => hx (congrArg Subtype.val hy)
  let : Nontrivial P := nontrivial_of_ne y 0 hy
  have hr : Module.finrank K (K ⊗[𝓞 K] P) = 1 := by
    rw [integralPart_generic_finrank]
    exact finrank_span_singleton hgen
  have hd := hs P (by rw [hr]; exact Nat.zero_lt_one)
  simp only [slope, hr, Nat.cast_one, div_one, h0, zero_div] at hd
  rw [(h.submodule P).degree_eq_lineDegree hr,
    (h.submodule P).lineDegree_eq_sum_embeddings hr hy] at hd
  let := line_quotient_finite hr hy
  have hcard : (1 : ℝ) ≤ Nat.card (P ⧸ (𝓞 K ∙ y)) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.card_pos.ne'))
  have hlog := Real.log_nonneg hcard
  have hD : (0 : ℝ) < Module.finrank ℚ K := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K))
  have hnum := (div_le_iff₀ hD).mp hd
  have hsum : (∑ σ : K →+* ℂ, Real.log ((h.submodule P).sectionNorm σ y)) =
      ∑ σ : K →+* ℂ, Real.log (h.sectionNorm σ x) := by
    simp only [sectionNorm_submodule, y]
  rw [hsum] at hnum
  linarith

/-- The squared actual trace norm is at least the field degree. -/
theorem IsSemistable.traceSection_norm_sq_ge {h : HermitianMetric K M}
    (hs : h.IsSemistable) (h0 : h.degree = 0) {x : M} (hx : x ≠ 0) :
    (Module.finrank ℚ K : ℝ) ≤ ‖h.traceSection x‖ ^ 2 := by
  have hlog := hs.sum_log_sectionNorm_nonneg h0 hx
  have hb := Finset.sum_le_sum (s := Finset.univ) (fun (σ : K →+* ℂ) _ =>
    Real.log_le_sub_one_of_pos (sq_pos_of_pos (h.sectionNorm_pos σ hx)))
  simp only [Real.log_pow, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    NumberField.Embeddings.card] at hb
  rw [← Finset.mul_sum] at hb
  norm_num only [Nat.cast_ofNat] at hb
  rw [h.traceSection_norm_sq]
  linarith

/-- Every nonzero point of the actual integral trace lattice has the uniform systole. -/
theorem IsSemistable.traceLattice_systole {h : HermitianMetric K M}
    (hs : h.IsSemistable) (h0 : h.degree = 0) (z : h.TraceSpace)
    (hz : z ∈ h.traceLattice) (hz0 : z ≠ 0) :
    Real.sqrt (Module.finrank ℚ K : ℝ) ≤ ‖z‖ := by
  obtain ⟨x, rfl⟩ := hz
  have hx : x ≠ 0 := fun hx => hz0 (by rw [hx, map_zero])
  have hb := hs.traceSection_norm_sq_ge h0 hx
  have hsqrt := Real.sq_sqrt (show (0 : ℝ) ≤ Module.finrank ℚ K from Nat.cast_nonneg _)
  nlinarith [norm_nonneg (h.traceSection x), Real.sqrt_nonneg (Module.finrank ℚ K : ℝ)]

end BostConjecture.Arithmetic.HermitianMetric
