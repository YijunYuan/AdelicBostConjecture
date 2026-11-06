/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Determinant.IntegralExact
public import BostConjecture.Arithmetic.Determinant.ExactBaseChange
public import BostConjecture.Arithmetic.Determinant.Orthogonal
public import BostConjecture.Arithmetic.Submodule.QuotientMetric

/-!
# Complex fibers of the intrinsic exact determinant

The canonical integral determinant map is computed using any complex
section, and in particular the orthogonal section defining the quotient
metric. Rank transports use the existing intrinsic determinant lines.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct exteriorPower
open scoped InnerProductSpace

namespace BostConjecture.Arithmetic

variable {K : Type*} [Field K] [NumberField K]
variable {M N P : Type*} [AddCommGroup M] [Module (𝓞 K) M]
    [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
    [AddCommGroup N] [Module (𝓞 K) N] [Module.Finite (𝓞 K) N]
    [Module.Projective (𝓞 K) N] [AddCommGroup P] [Module (𝓞 K) P]
    [Module.Finite (𝓞 K) P]

omit [Module.Finite (𝓞 K) P] in
/-- The intrinsic determinant map on integral pure tensors can be evaluated
using any section of the complex quotient map. -/
lemma determinantExactEquiv_section (i : M →ₗ[𝓞 K] P) (q : P →ₗ[𝓞 K] N)
    (h : Function.Exact i q) (hi : Function.Injective i) (hq : Function.Surjective q)
    (σ : K →+* ℂ) (t : ComplexFiber N σ →ₗ[ℂ] ComplexFiber P σ)
    (ht : (fiberMap q σ).comp t = LinearMap.id)
    (x : DeterminantLine (K := K) M) (y : DeterminantLine (K := K) N) :
    determinantComplexEquiv P σ (fiberSection _ σ (determinantExactEquiv i q h hi hq
      (x ⊗ₜ[𝓞 K] y))) =
    degreeCongr ((exteriorPower.finrank_exact i q h hi hq).symm.trans
      (TensorProduct.isBaseChange (𝓞 K) P K).finrank_eq.symm)
      (map (Module.finrank (𝓞 K) M + Module.finrank (𝓞 K) N) ((fiberMap i σ).coprod t)
        (prodMap ℂ (ComplexFiber M σ) (ComplexFiber N σ) _ _
          (degreeCongr (TensorProduct.isBaseChange (𝓞 K) M K).finrank_eq
              (determinantComplexEquiv M σ (fiberSection _ σ x)) ⊗ₜ[ℂ]
            degreeCongr (TensorProduct.isBaseChange (𝓞 K) N K).finrank_eq
              (determinantComplexEquiv N σ (fiberSection _ σ y))))) := by
  let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  let : FaithfulSMul (𝓞 K) ℂ := (faithfulSMul_iff_algebraMap_injective (𝓞 K) ℂ).mpr
    (σ.injective.comp (IsFractionRing.injective (𝓞 K) K))
  change baseChangeEquiv (𝓞 K) P ℂ _ (fiberSection _ σ
    (degreeCongr _ (exactEquiv i q h hi hq
      (degreeCongr _ x ⊗ₜ[𝓞 K] degreeCongr _ y)))) = _
  rw [exteriorDegreeCongr_section]
  simp only [fiberSection]
  rw [exactEquiv_baseChange_field_section i q h hi hq ℂ t ht]
  rw [show baseChangeEquiv (𝓞 K) M ℂ _ (1 ⊗ₜ[𝓞 K] degreeCongr
      (TensorProduct.isBaseChange (𝓞 K) M K).finrank_eq x) = _ from
    exteriorDegreeCongr_section σ _ x]
  rw [show baseChangeEquiv (𝓞 K) N ℂ _ (1 ⊗ₜ[𝓞 K] degreeCongr
      (TensorProduct.isBaseChange (𝓞 K) N K).finrank_eq y) = _ from
    exteriorDegreeCongr_section σ _ y]
  rfl

namespace HermitianMetric

/-- Exact determinant norms multiply for the actual induced and quotient
metrics, on every integral pure determinant tensor. -/
lemma determinantExactEquiv_sectionNorm (H : HermitianMetric (K := K) P)
    (i : M →ₗ[𝓞 K] P) (q : P →ₗ[𝓞 K] N)
    (h : Function.Exact i q) (hi : Function.Injective i) (hq : Function.Surjective q)
    (σ : K →+* ℂ) (x : DeterminantLine (K := K) M) (y : DeterminantLine (K := K) N) :
    H.determinant.sectionNorm σ (determinantExactEquiv i q h hi hq (x ⊗ₜ[𝓞 K] y)) =
      (H.pullback i hi).determinant.sectionNorm σ x *
        (H.pushforward q hq).determinant.sectionNorm σ y := by
  let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  let : InnerProductSpace.Core ℂ (ComplexFiber P σ) := H.fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber P σ)
  let := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber P σ))
  let : InnerProductSpace.Core ℂ (ComplexFiber M σ) := (H.pullback i hi).fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
  let := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
  let : InnerProductSpace.Core ℂ (ComplexFiber N σ) := (H.pushforward q hq).fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber N σ)
  let := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber N σ))
  let p := (stdOrthonormalBasis ℂ (ComplexFiber M σ)).reindex
    (finCongr (complexFiber_finrank M σ))
  let r := (stdOrthonormalBasis ℂ (ComplexFiber N σ)).reindex
    (finCongr (complexFiber_finrank N σ))
  let c := (stdOrthonormalBasis ℂ (ComplexFiber P σ)).reindex
    (finCongr (complexFiber_finrank P σ))
  have hM := (TensorProduct.isBaseChange (𝓞 K) M K).finrank_eq
  have hN := (TensorProduct.isBaseChange (𝓞 K) N K).finrank_eq
  have hP := (exteriorPower.finrank_exact i q h hi hq).symm.trans
    (TensorProduct.isBaseChange (𝓞 K) P K).finrank_eq.symm
  let p' := p.reindex (finCongr hM)
  let r' := r.reindex (finCongr hN)
  let c' := c.reindex (finCongr hP.symm)
  have ht : (fiberMap q σ).comp (H.fiberLift q hq σ) = LinearMap.id := by
    apply LinearMap.ext
    intro z
    exact H.fiberMap_fiberLift q hq σ z
  change Real.sqrt (((H.determinantFiber σ).inner _ _).re) =
    Real.sqrt ((((H.pullback i hi).determinantFiber σ).inner _ _).re) *
      Real.sqrt ((((H.pushforward q hq).determinantFiber σ).inner _ _).re)
  rw [H.determinantFiber_norm_eq σ c, (H.pullback i hi).determinantFiber_norm_eq σ p,
    (H.pushforward q hq).determinantFiber_norm_eq σ r,
    determinantExactEquiv_section i q h hi hq σ (H.fiberLift q hq σ) ht,
    ComplexDeterminant.norm_degreeCongr hP c' c]
  rw [ComplexDeterminant.norm_prodMap p' r' c' (fiberMap i σ) (H.fiberLift q hq σ)
    (fun _ _ => rfl) (fun _ _ => rfl) ?_]
  · rw [ComplexDeterminant.norm_degreeCongr hM p p',
      ComplexDeterminant.norm_degreeCongr hN r r']
  · intro u v
    have hz : q.comp i = 0 := LinearMap.ext (fun z => congr_fun h.comp_eq_zero z)
    have hz' : (fiberMap q σ).comp (fiberMap i σ) = 0 := by
      change (q.baseChange ℂ).comp (i.baseChange ℂ) = 0
      rw [← LinearMap.baseChange_comp, hz, LinearMap.baseChange_zero]
    exact (Submodule.mem_orthogonal _ _).mp
      (ComplexQuotient.lift_mem (fiberMap q σ) (fiberMap_surjective q hq σ) v)
      (fiberMap i σ u) (show fiberMap q σ (fiberMap i σ u) = 0 from
        LinearMap.congr_fun hz' u)

end HermitianMetric
end BostConjecture.Arithmetic
