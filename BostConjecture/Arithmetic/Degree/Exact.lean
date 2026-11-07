/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Determinant.ExactMetric
public import BostConjecture.Arithmetic.Line.TensorDegree

/-!
# Degree additivity for intrinsic Hermitian exact sequences

The canonical exact determinant preserves all integral section norms for
the induced and quotient metrics. Rank-one degree invariance and actual
Hilbert tensor additivity then prove the normalized degree identity.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace BostConjecture.Arithmetic.HermitianMetric

universe u

variable {K : Type*} [Field K] [NumberField K]
variable {M N P : Type u} [AddCommGroup M] [Module (𝓞 K) M]
    [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
    [AddCommGroup N] [Module (𝓞 K) N] [Module.Finite (𝓞 K) N]
    [Module.Projective (𝓞 K) N] [AddCommGroup P] [Module (𝓞 K) P]
    [Module.Finite (𝓞 K) P] [Module.Projective (𝓞 K) P]

omit [Module.Projective (𝓞 K) P] in
/-- The canonical exact determinant preserves every integral section norm. -/
lemma determinantExactEquiv_isometry (H : HermitianMetric K P)
    (i : M →ₗ[𝓞 K] P) (q : P →ₗ[𝓞 K] N)
    (h : Function.Exact i q) (hi : Function.Injective i) (hq : Function.Surjective q)
    (σ : K →+* ℂ) (z : DeterminantLine (K := K) M ⊗[𝓞 K] DeterminantLine (K := K) N) :
    H.determinant.sectionNorm σ (determinantExactEquiv i q h hi hq z) =
      ((H.pullback i hi).determinant.tensor (H.pushforward q hq).determinant).sectionNorm σ z := by
  let A := (H.pullback i hi).determinant
  let C := (H.pushforward q hq).determinant
  let e := determinantExactEquiv i q h hi hq
  obtain ⟨x, hx⟩ := exists_ne (0 : DeterminantLine (K := K) M)
  obtain ⟨y, hy⟩ := exists_ne (0 : DeterminantLine (K := K) N)
  let f := lineCoordinate (M := DeterminantLine (K := K) M) (determinant_generic_finrank M)
  let g := lineCoordinate (M := DeterminantLine (K := K) N) (determinant_generic_finrank N)
  have hf := lineCoordinate_injective (M := DeterminantLine (K := K) M)
    (determinant_generic_finrank M)
  have hg := lineCoordinate_injective (M := DeterminantLine (K := K) N)
    (determinant_generic_finrank N)
  have hxy : x ⊗ₜ[𝓞 K] y ≠ 0 := by
    intro hz
    have hz' := congrArg (tensorCoordinate f g) hz
    simp only [tensorCoordinate_tmul, map_zero] at hz'
    exact (mul_ne_zero (fun hz => hx (hf (by simpa using hz)))
      (fun hz => hy (hg (by simpa using hz)))) hz'
  have hn : H.determinant.sectionNorm σ (e (x ⊗ₜ[𝓞 K] y)) =
      (A.tensor C).sectionNorm σ (x ⊗ₜ[𝓞 K] y) := by
    rw [sectionNorm_tensor_tmul]
    exact H.determinantExactEquiv_sectionNorm i q h hi hq σ x y
  obtain ⟨a, b, hb, hab⟩ := exists_smul_eq_of_injective (tensorCoordinate f g)
    (tensorCoordinate_injective f g hf hg) hxy z
  have h₁ := congrArg (fun w => H.determinant.sectionNorm σ (e w)) hab
  have h₂ := congrArg ((A.tensor C).sectionNorm σ) hab
  simp only [map_smul, sectionNorm_smul] at h₁ h₂
  have hbσ : ‖σ (b : K)‖ ≠ 0 := norm_ne_zero_iff.mpr
    (fun hz => (RingOfIntegers.coe_ne_zero_iff.mpr hb) (σ.injective (by simpa using hz)))
  exact mul_left_cancel₀ hbσ (h₁.symm.trans ((congrArg (_ * ·) hn).trans h₂))

omit [Module.Projective (𝓞 K) P] in
/-- The canonical exact determinant is an isometry on the entire complex
fiber, not only on integral generators. -/
lemma determinantExactEquiv_fiber_isometry (H : HermitianMetric K P)
    (i : M →ₗ[𝓞 K] P) (q : P →ₗ[𝓞 K] N)
    (h : Function.Exact i q) (hi : Function.Injective i) (hq : Function.Surjective q)
    (σ : K →+* ℂ)
    (z : ComplexFiber (DeterminantLine (K := K) M ⊗[𝓞 K] DeterminantLine (K := K) N) σ) :
    Real.sqrt (((H.determinant.fiber σ).inner
      (fiberMap (determinantExactEquiv i q h hi hq).toLinearMap σ z)
      (fiberMap (determinantExactEquiv i q h hi hq).toLinearMap σ z)).re) =
    Real.sqrt (((((H.pullback i hi).determinant.tensor
      (H.pushforward q hq).determinant).fiber σ).inner z z).re) := by
  let T := DeterminantLine (K := K) M ⊗[𝓞 K] DeterminantLine (K := K) N
  let A := (H.pullback i hi).determinant.tensor (H.pushforward q hq).determinant
  let e := determinantExactEquiv i q h hi hq
  let : Nontrivial T := e.symm.injective.nontrivial
  let : InnerProductSpace.Core ℂ (ComplexFiber T σ) := A.fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber T σ)
  let := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber T σ))
  let : InnerProductSpace.Core ℂ (ComplexFiber (DeterminantLine (K := K) P) σ) :=
    H.determinant.fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
    (F := ComplexFiber (DeterminantLine (K := K) P) σ)
  let := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ
    (ComplexFiber (DeterminantLine (K := K) P) σ))
  obtain ⟨w, hw⟩ := exists_ne (0 : T)
  have hws : fiberSection T σ w ≠ 0 := fun hz =>
    hw (fiberSection_injective T σ (by simpa only [fiberSection, tmul_zero] using hz))
  have hr : Module.finrank ℂ (ComplexFiber T σ) = 1 := by
    rw [complexFiber_finrank, tensor_generic_finrank, determinant_generic_finrank,
      determinant_generic_finrank, mul_one]
  obtain ⟨a, rfl⟩ := (finrank_eq_one_iff_of_nonzero' (fiberSection T σ w) hws).mp hr z
  change ‖fiberMap e.toLinearMap σ (a • fiberSection T σ w)‖ = ‖a • fiberSection T σ w‖
  rw [map_smul, norm_smul, norm_smul, fiberMap_section]
  exact congrArg (‖a‖ * ·) (H.determinantExactEquiv_isometry i q h hi hq σ w)

/-- Normalized arithmetic degree is additive for every finite projective
exact sequence with its induced and quotient Hermitian metrics. -/
theorem degree_exact (H : HermitianMetric K P)
    (i : M →ₗ[𝓞 K] P) (q : P →ₗ[𝓞 K] N)
    (h : Function.Exact i q) (hi : Function.Injective i) (hq : Function.Surjective q) :
    H.degree = (H.pullback i hi).degree + (H.pushforward q hq).degree := by
  let A := (H.pullback i hi).determinant
  let C := (H.pushforward q hq).determinant
  let e := determinantExactEquiv i q h hi hq
  let : Nontrivial (DeterminantLine (K := K) M ⊗[𝓞 K] DeterminantLine (K := K) N) :=
    e.symm.injective.nontrivial
  have hr : Module.finrank K
      (K ⊗[𝓞 K] (DeterminantLine (K := K) M ⊗[𝓞 K] DeterminantLine (K := K) N)) = 1 := by
    rw [tensor_generic_finrank, determinant_generic_finrank, determinant_generic_finrank, mul_one]
  have he := (A.tensor C).lineDegree_eq_of_equiv H.determinant e hr
    (determinant_generic_finrank P)
    (fun σ z => (H.determinantExactEquiv_isometry i q h hi hq σ z).symm)
  change H.determinant.lineDegree _ = A.lineDegree _ + C.lineDegree _
  rw [← he, ← (A.tensor C).degree_eq_lineDegree hr,
    A.degree_tensor_of_rank_one C (determinant_generic_finrank M) (determinant_generic_finrank N),
    A.degree_eq_lineDegree (determinant_generic_finrank M),
    C.degree_eq_lineDegree (determinant_generic_finrank N)]

end BostConjecture.Arithmetic.HermitianMetric
