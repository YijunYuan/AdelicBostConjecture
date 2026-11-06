/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Dual.Metric
public import BostConjecture.Arithmetic.Line.DualCoordinate
public import BostConjecture.Arithmetic.Degree.Normalization

/-!
# Degree of the intrinsic Hermitian dual line

The inverse coefficient ideal and reciprocal operator norm prove sign
reversal of degree for nonfree projective lines over every number field.
-/

@[expose] public section

noncomputable section

open NumberField Module TensorProduct

namespace BostConjecture.Arithmetic

variable {K : Type*} [Field K] [NumberField K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]
    [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]

omit [NumberField K] in
/-- Generic rank is preserved by the actual integral dual. -/
lemma dual_generic_finrank :
    finrank K (K ⊗[𝓞 K] Dual (𝓞 K) M) = finrank K (K ⊗[𝓞 K] M) := by
  rw [(dualBaseChangeEquiv (𝓞 K) K M).finrank_eq, Subspace.dual_finrank_eq]

namespace HermitianMetric

omit [NumberField K] in
/-- On a Hermitian line every nonzero vector attains the dual evaluation norm. -/
lemma dual_sectionNorm_mul_of_rank_one (h : HermitianMetric (K := K) M)
    (hr : finrank K (K ⊗[𝓞 K] M) = 1) (σ : K →+* ℂ)
    (f : Dual (𝓞 K) M) {x : M} (hx : x ≠ 0) :
    h.dual.sectionNorm σ f * h.sectionNorm σ x = ‖σ (f x)‖ := by
  let : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
  let := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
  have hx' : fiberSection M σ x ≠ 0 := by
    intro he
    exact hx (fiberSection_injective M σ (by simpa [fiberSection] using he))
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one
    ((complexFiber_finrank M σ).trans hr) hx' (h.dualRiesz σ (fiberSection _ σ f))
  rw [← dualFiberEquiv_section M σ f x, ← h.dualRiesz_inner]
  change ‖h.dualRiesz σ (fiberSection _ σ f)‖ * ‖fiberSection M σ x‖ =
    ‖inner ℂ (h.dualRiesz σ (fiberSection _ σ f)) (fiberSection M σ x)‖
  rw [← hc, norm_smul, inner_smul_left, norm_mul, starRingEnd_apply, norm_star,
    ← inner_self_re_eq_norm, inner_self_eq_norm_mul_norm]
  ring

/-- The dual coordinate length is the reciprocal of the original coordinate length. -/
lemma coordinateLength_dual (h : HermitianMetric (K := K) M)
    (hr : finrank K (K ⊗[𝓞 K] M) = 1)
    (q : M →ₗ[𝓞 K] K) (hq : Function.Injective q)
    {x : M} (hx : x ≠ 0) {f : Dual (𝓞 K) M} (hf : f ≠ 0) (v : InfinitePlace K) :
    h.dual.coordinateLength (dualCoordinate q x) f v = (h.coordinateLength q x v)⁻¹ := by
  have hd : v (dualCoordinate q x f) ≠ 0 := by
    apply ne_of_gt
    apply InfinitePlace.pos_iff.mpr
    intro he
    apply hf
    exact dualCoordinate_injective q hq hx (by simpa using he)
  rw [coordinateLength, coordinateLength, inv_div,
    div_eq_div_iff hd (ne_of_gt (h.sectionNorm_pos v.embedding hx)),
    h.dual_sectionNorm_mul_of_rank_one hr v.embedding f hx]
  rw [← map_mul, mul_comm (q x), dualCoordinate_mul q hq hx]
  exact v.norm_embedding_eq _

variable [Nontrivial M]

/-- Inversion of the coefficient ideal and coordinate norm negates the actual degree formula. -/
lemma degreeInCoordinate_dual (h : HermitianMetric (K := K) M)
    (hr : finrank K (K ⊗[𝓞 K] M) = 1)
    (q : M →ₗ[𝓞 K] K) (hq : Function.Injective q)
    {x : M} (hx : x ≠ 0) {f : Dual (𝓞 K) M} (hf : f ≠ 0) :
    h.dual.degreeInCoordinate (dualCoordinate q x) f = -h.degreeInCoordinate q x := by
  have he : h.dual.coordinateLength (dualCoordinate q x) f =
      fun v => (h.coordinateLength q x v)⁻¹ := by
    funext v
    exact h.coordinateLength_dual hr q hq hx hf v
  rw [degreeInCoordinate, degreeInCoordinate, BostConjecture.Arithmetic.lineDegree,
    BostConjecture.Arithmetic.lineDegree, logIdealNorm_dualCoordinate q hq hx, he, archLog_inv]
  ring

/-- Intrinsic normalized degree changes sign on the dual of any projective Hermitian line. -/
theorem degree_dual_of_rank_one (h : HermitianMetric (K := K) M)
    (hr : finrank K (K ⊗[𝓞 K] M) = 1) : h.dual.degree = -h.degree := by
  have hrd : finrank K (K ⊗[𝓞 K] Dual (𝓞 K) M) = 1 := dual_generic_finrank.trans hr
  let : Nontrivial (Dual (𝓞 K) M) := by
    by_contra hn
    have : Subsingleton (Dual (𝓞 K) M) := not_nontrivial_iff_subsingleton.mp hn
    rw [Module.finrank_zero_of_subsingleton] at hrd
    exact Nat.zero_ne_one hrd
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  obtain ⟨f, hf⟩ := exists_ne (0 : Dual (𝓞 K) M)
  let q := lineCoordinate (M := M) hr
  have hq := lineCoordinate_injective (M := M) hr
  rw [h.dual.degree_eq_lineDegree hrd, h.degree_eq_lineDegree hr,
    h.dual.lineDegree_eq_degreeInCoordinate hrd (dualCoordinate q x)
      (dualCoordinate_injective q hq hx) hf,
    h.lineDegree_eq_degreeInCoordinate hr q hq hx]
  exact h.degreeInCoordinate_dual hr q hq hx hf

end HermitianMetric
end BostConjecture.Arithmetic
