/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Main.TensorSemistability.GramDegree
public import BostConjecture.Balanced.GramDerivative
public import BostConjecture.Main.TensorSemistability.MetricVariation

/-!
# Projection-trace derivative of an actual induced arithmetic degree

The intrinsic Gram formula converts differentiation of archimedean
automorphisms into the degree derivative of a fixed integral submodule.
Reference: this paper, Proposition 7.3, page 13.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Arithmetic

section Fiber

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Gram derivative for an isometrically embedded fiber uses the actual
orthogonal projection onto its range. -/
theorem hasDerivAt_re_gramDet_isometry (f : E →ₗᵢ[ℂ] F)
    (v : OrthonormalBasis ι ℂ E) (A : Module.End ℂ F) (g : ℝ → F → F)
    (h0 : ∀ x, g 0 x = x) (hg : ∀ x, HasDerivAt (fun t => g t x) (A x) 0) :
    HasDerivAt (fun t => (Matrix.of fun i j => inner ℂ (g t (f (v i)))
      (g t (f (v j)))).det.re)
      (2 * (LinearMap.trace ℂ F
        (f.toLinearMap.range.starProjection.toLinearMap.comp A)).re) 0 := by
  let e : E ≃ₗᵢ[ℂ] f.toLinearMap.range :=
    (LinearEquiv.ofInjective f.toLinearMap f.injective).isometryOfInner
      (fun x y => f.inner_map_map x y)
  exact Balanced.hasDerivAt_re_gramDet f.toLinearMap.range (v.map e) A
    (fun t i => g t (f (v i))) (fun i => h0 _) (fun i => hg _)

end Fiber

namespace HermitianMetric

open NumberField TensorProduct

variable {K : Type*} [Field K] [NumberField K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]
    [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]

/-- Real trace of an endomorphism compressed to the actual submodule fiber. -/
def fiberProjectionTrace (h : HermitianMetric K M)
    (P : Submodule (𝓞 K) M) (σ : K →+* ℂ)
    (A : Module.End ℂ (ComplexFiber M σ)) : ℝ := by
  letI : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  letI := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
  letI := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
  exact (LinearMap.trace ℂ (ComplexFiber M σ)
    ((fiberMap P.subtype σ).range.starProjection.toLinearMap.comp A)).re

/-- Differentiation of actual induced arithmetic degree under a compatible
archimedean automorphism curve. -/
theorem hasDerivAt_submodule_degree_archimedeanPullback
    (h : HermitianMetric K M) (P : Submodule (𝓞 K) M)
    (g : ℝ → ∀ σ : K →+* ℂ, ComplexFiber M σ ≃ₗ[ℂ] ComplexFiber M σ)
    (hc : ∀ t σ x, g t (ComplexEmbedding.conjugate σ) (fiberConjugate M σ x) =
      fiberConjugate M σ (g t σ x))
    (A : ∀ σ : K →+* ℂ, Module.End ℂ (ComplexFiber M σ))
    (h0 : ∀ σ x, g 0 σ x = x)
    (hg : ∀ σ x,
      letI : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
      letI := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
      letI := InnerProductSpace.ofCore
        (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
      letI : NormedSpace ℂ (ComplexFiber M σ) := inferInstance
      letI : Module ℝ (ComplexFiber M σ) := (NormedSpace.restrictScalars ℝ ℂ _).toModule
      letI : NormedSpace ℝ (ComplexFiber M σ) := NormedSpace.restrictScalars ℝ ℂ _
      HasDerivAt (fun t => g t σ x) (A σ x) 0) :
    HasDerivAt (fun t => ((h.archimedeanPullback (g t) (hc t)).submodule P).degree)
      (-(∑ σ, h.fiberProjectionTrace P σ (A σ)) / (Module.finrank ℚ K : ℝ)) 0 := by
  let (σ : K →+* ℂ) : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  let (σ : K →+* ℂ) :=
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
  let (σ : K →+* ℂ) := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
  let (σ : K →+* ℂ) : NormedSpace ℂ (ComplexFiber M σ) := inferInstance
  let (σ : K →+* ℂ) : Module ℝ (ComplexFiber M σ) :=
    (NormedSpace.restrictScalars ℝ ℂ _).toModule
  let (σ : K →+* ℂ) : NormedSpace ℝ (ComplexFiber M σ) := NormedSpace.restrictScalars ℝ ℂ _
  let (σ : K →+* ℂ) : InnerProductSpace.Core ℂ (ComplexFiber P σ) := (h.submodule P).fiber σ
  let (σ : K →+* ℂ) :=
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber P σ)
  let (σ : K →+* ℂ) := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber P σ))
  let v (σ : K →+* ℂ) := (stdOrthonormalBasis ℂ (ComplexFiber P σ)).reindex
    (finCongr (complexFiber_finrank P σ))
  let f (σ : K →+* ℂ) : ComplexFiber P σ →ₗᵢ[ℂ] ComplexFiber M σ :=
    (fiberMap P.subtype σ).isometryOfInner (fun _ _ => rfl)
  have hb (σ : K →+* ℂ) : (Matrix.of fun i j =>
      (((h.archimedeanPullback (g 0) (hc 0)).submodule P).fiber σ).inner
        (v σ i) (v σ j)) = 1 := by
    ext i j
    change (h.fiber σ).inner (g 0 σ (f σ (v σ i))) (g 0 σ (f σ (v σ j))) = _
    rw [h0, h0]
    change inner ℂ (f σ (v σ i)) (f σ (v σ j)) = _
    rw [(f σ).inner_map_map, (v σ).inner_eq_ite]
    rfl
  have hd (σ : K →+* ℂ) := hasDerivAt_re_gramDet_isometry (f σ) (v σ) (A σ)
    (fun t x => g t σ x) (h0 σ) (hg σ)
  have hh := hasDerivAt_degree_of_gram
    (fun t => (h.archimedeanPullback (g t) (hc t)).submodule P)
    (fun σ => (v σ).toBasis) hb (fun σ => 2 * h.fiberProjectionTrace P σ (A σ)) hd
  convert hh using 1
  rw [← Finset.mul_sum]
  ring

end HermitianMetric

end BostConjecture.Arithmetic
