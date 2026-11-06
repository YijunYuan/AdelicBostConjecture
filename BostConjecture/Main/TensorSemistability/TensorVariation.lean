module

public import BostConjecture.Main.TensorSemistability.SubmoduleVariation
public import BostConjecture.Arithmetic.TensorCompatibility

/-!
# Tensor products of actual archimedean metric variations

The canonical scalar-extension equivalence transports tensor products of
fiber automorphisms to the actual arithmetic tensor fiber. Conjugation and
the actual Hilbert metric are preserved by this transport.
Reference: bost_specht_manuscript.pdf, Proposition 7.3, page 13.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace BostConjecture.Arithmetic

universe u
variable {K : Type*} [Field K] [NumberField K]
variable {M N : Type u} [AddCommGroup M] [Module (𝓞 K) M]
    [AddCommGroup N] [Module (𝓞 K) N]

omit [NumberField K] in
/-- Binary scalar extension intertwines the canonical conjugations. -/
lemma binaryTensorFiberEquiv_conjugate (σ : K →+* ℂ)
    (z : ComplexFiber (M ⊗[𝓞 K] N) σ) :
    binaryTensorFiberEquiv (ComplexEmbedding.conjugate σ)
      (fiberConjugate (M ⊗[𝓞 K] N) σ z) =
    TensorProduct.congr (fiberConjugate M σ) (fiberConjugate N σ)
      (binaryTensorFiberEquiv σ z) := by
  let : Module ℂ (ComplexFiber M (ComplexEmbedding.conjugate σ)) := inferInstance
  let : Module ℂ (ComplexFiber N (ComplexEmbedding.conjugate σ)) := inferInstance
  let : Module ℂ (ComplexFiber (M ⊗[𝓞 K] N) (ComplexEmbedding.conjugate σ)) := inferInstance
  let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  induction z using TensorProduct.inductionOn with
  | tmul c z =>
    have hz : binaryTensorFiberEquiv (ComplexEmbedding.conjugate σ)
        (fiberConjugate (M ⊗[𝓞 K] N) σ (fiberSection _ σ z)) =
        TensorProduct.congr (fiberConjugate M σ) (fiberConjugate N σ)
          (binaryTensorFiberEquiv σ (fiberSection _ σ z)) := by
      induction z using TensorProduct.inductionOn with
      | tmul x y => simp
      | add x y hx hy =>
        simpa only [fiberSection, tmul_add, map_add] using congrArg₂ (· + ·) hx hy
    have he : c ⊗ₜ[𝓞 K] z = c • fiberSection _ σ z := by
      simp [fiberSection, smul_tmul']
    simpa only [he, map_smulₛₗ, RingHom.id_apply] using congrArg ((starRingEnd ℂ) c • ·) hz
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Tensor two archimedean automorphisms on the actual arithmetic tensor fiber. -/
def tensorFiberAutomorphism
    (g : ∀ σ : K →+* ℂ, ComplexFiber M σ ≃ₗ[ℂ] ComplexFiber M σ)
    (j : ∀ σ : K →+* ℂ, ComplexFiber N σ ≃ₗ[ℂ] ComplexFiber N σ)
    (σ : K →+* ℂ) : ComplexFiber (M ⊗[𝓞 K] N) σ ≃ₗ[ℂ]
      ComplexFiber (M ⊗[𝓞 K] N) σ :=
  (binaryTensorFiberEquiv σ).trans
    ((TensorProduct.congr (g σ) (j σ)).trans (binaryTensorFiberEquiv σ).symm)

omit [NumberField K] in
lemma tensorFiberAutomorphism_conjugate
    (g : ∀ σ : K →+* ℂ, ComplexFiber M σ ≃ₗ[ℂ] ComplexFiber M σ)
    (j : ∀ σ : K →+* ℂ, ComplexFiber N σ ≃ₗ[ℂ] ComplexFiber N σ)
    (hg : ∀ σ x, g (ComplexEmbedding.conjugate σ) (fiberConjugate M σ x) =
      fiberConjugate M σ (g σ x))
    (hj : ∀ σ x, j (ComplexEmbedding.conjugate σ) (fiberConjugate N σ x) =
      fiberConjugate N σ (j σ x))
    (σ : K →+* ℂ) (z : ComplexFiber (M ⊗[𝓞 K] N) σ) :
    tensorFiberAutomorphism g j (ComplexEmbedding.conjugate σ)
      (fiberConjugate (M ⊗[𝓞 K] N) σ z) =
    fiberConjugate (M ⊗[𝓞 K] N) σ (tensorFiberAutomorphism g j σ z) := by
  apply (binaryTensorFiberEquiv (ComplexEmbedding.conjugate σ)).injective
  simp only [tensorFiberAutomorphism, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, binaryTensorFiberEquiv_conjugate]
  induction binaryTensorFiberEquiv σ z using TensorProduct.inductionOn with
  | tmul x y => simp only [TensorProduct.congr_tmul, hg, hj]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The infinitesimal tensor action, transported to the actual arithmetic fiber. -/
def tensorFiberGenerator
    (A : ∀ σ : K →+* ℂ, Module.End ℂ (ComplexFiber M σ))
    (B : ∀ σ : K →+* ℂ, Module.End ℂ (ComplexFiber N σ))
    (σ : K →+* ℂ) : Module.End ℂ (ComplexFiber (M ⊗[𝓞 K] N) σ) :=
  (binaryTensorFiberEquiv σ).symm.toLinearMap.comp
    ((TensorProduct.map (A σ) LinearMap.id + TensorProduct.map LinearMap.id (B σ)).comp
      (binaryTensorFiberEquiv σ).toLinearMap)

namespace HermitianMetric

/-- Pulling back both factors tensors to the pullback of the actual tensor metric. -/
theorem tensor_archimedeanPullback
    (h : HermitianMetric (K := K) M) (k : HermitianMetric (K := K) N)
    (g : ∀ σ : K →+* ℂ, ComplexFiber M σ ≃ₗ[ℂ] ComplexFiber M σ)
    (j : ∀ σ : K →+* ℂ, ComplexFiber N σ ≃ₗ[ℂ] ComplexFiber N σ)
    (hg : ∀ σ x, g (ComplexEmbedding.conjugate σ) (fiberConjugate M σ x) =
      fiberConjugate M σ (g σ x))
    (hj : ∀ σ x, j (ComplexEmbedding.conjugate σ) (fiberConjugate N σ x) =
      fiberConjugate N σ (j σ x)) :
    (h.archimedeanPullback g hg).tensor (k.archimedeanPullback j hj) =
      (h.tensor k).archimedeanPullback (tensorFiberAutomorphism g j)
        (tensorFiberAutomorphism_conjugate g j hg hj) := by
  apply ext_inner
  intro σ x y
  rw [tensor_inner, archimedeanPullback_inner, tensor_inner]
  simp only [tensorFiberAutomorphism, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  apply Tensor.inner_ext_of_span (fun z : ComplexFiber M σ × ComplexFiber N σ =>
      z.1 ⊗ₜ[ℂ] z.2)
    (by simpa only [Set.range, Prod.exists] using
      TensorProduct.span_tmul_eq_top ℂ (ComplexFiber M σ) (ComplexFiber N σ))
    (Tensor.binaryCore ((h.archimedeanPullback g hg).fiber σ)
      ((k.archimedeanPullback j hj).fiber σ))
    (Tensor.binaryCore (h.fiber σ) (k.fiber σ))
    LinearMap.id (TensorProduct.congr (g σ) (j σ)).toLinearMap _
  intro a b
  simp only [LinearMap.id_apply, LinearEquiv.coe_coe, TensorProduct.congr_tmul,
    Tensor.binaryCore_inner_tmul, archimedeanPullback_inner]

variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
    [Module.Finite (𝓞 K) N] [Module.Projective (𝓞 K) N]

/-- Differentiate an actual tensor submodule degree along independent compatible
exponential variations of the two factor metrics. -/
theorem hasDerivAt_submodule_degree_tensor_exponentialVariation
    (h : HermitianMetric (K := K) M) (k : HermitianMetric (K := K) N)
    (P : Submodule (𝓞 K) (M ⊗[𝓞 K] N))
    (A : ∀ σ : K →+* ℂ, Module.End ℂ (ComplexFiber M σ))
    (B : ∀ σ : K →+* ℂ, Module.End ℂ (ComplexFiber N σ))
    (hs : ∀ σ x y, (h.fiber σ).inner (A σ x) y = (h.fiber σ).inner x (A σ y))
    (ks : ∀ σ x y, (k.fiber σ).inner (B σ x) y = (k.fiber σ).inner x (B σ y))
    (hc : ∀ σ x, A (ComplexEmbedding.conjugate σ) (fiberConjugate M σ x) =
      fiberConjugate M σ (A σ x))
    (kc : ∀ σ x, B (ComplexEmbedding.conjugate σ) (fiberConjugate N σ x) =
      fiberConjugate N σ (B σ x)) :
    HasDerivAt (fun t => (((h.exponentialVariation A hs hc t).tensor
      (k.exponentialVariation B ks kc t)).submodule P).degree)
      (-(∑ σ, (h.tensor k).fiberProjectionTrace P σ (tensorFiberGenerator A B σ)) /
        (Module.finrank ℚ K : ℝ)) 0 := by
  simp only [exponentialVariation, tensor_archimedeanPullback]
  apply hasDerivAt_submodule_degree_archimedeanPullback
  · intro σ x
    let : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
    let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
    let := InnerProductSpace.ofCore
      (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
    let : InnerProductSpace.Core ℂ (ComplexFiber N σ) := k.fiber σ
    let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber N σ)
    let := InnerProductSpace.ofCore
      (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber N σ))
    have hA := expLinearEquiv_zero_apply (LinearMap.toContinuousLinearMap (A σ))
    have hB := expLinearEquiv_zero_apply (LinearMap.toContinuousLinearMap (B σ))
    apply (binaryTensorFiberEquiv σ).injective
    simp only [tensorFiberAutomorphism, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    induction binaryTensorFiberEquiv σ x using TensorProduct.inductionOn with
    | tmul u v => simp only [TensorProduct.congr_tmul, fiberExp, hA, hB]
    | add u v hu hv => simp only [map_add, hu, hv]
  · intro σ x
    let : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
    let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
    let := InnerProductSpace.ofCore
      (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
    let : InnerProductSpace.Core ℂ (ComplexFiber N σ) := k.fiber σ
    let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber N σ)
    let := InnerProductSpace.ofCore
      (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber N σ))
    let : InnerProductSpace.Core ℂ (ComplexFiber (M ⊗[𝓞 K] N) σ) := (h.tensor k).fiber σ
    let := InnerProductSpace.Core.toNormedAddCommGroup
      (𝕜 := ℂ) (F := ComplexFiber (M ⊗[𝓞 K] N) σ)
    let := InnerProductSpace.ofCore
      (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber (M ⊗[𝓞 K] N) σ))
    let : NormedSpace ℂ (ComplexFiber (M ⊗[𝓞 K] N) σ) := inferInstance
    let : Module ℝ (ComplexFiber (M ⊗[𝓞 K] N) σ) :=
      (NormedSpace.restrictScalars ℝ ℂ _).toModule
    let : NormedSpace ℝ (ComplexFiber (M ⊗[𝓞 K] N) σ) := NormedSpace.restrictScalars ℝ ℂ _
    let : Module ℝ (ComplexFiber M σ ⊗[ℂ] ComplexFiber N σ) :=
      (NormedSpace.restrictScalars ℝ ℂ _).toModule
    let : NormedSpace ℝ (ComplexFiber M σ ⊗[ℂ] ComplexFiber N σ) :=
      NormedSpace.restrictScalars ℝ ℂ _
    let e := (binaryTensorFiberEquiv (M := M) (N := N) σ).symm.toLinearMap.toContinuousLinearMap
    have hd := (e.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
      (Balanced.hasDerivAt_tensor_exp_zero (LinearMap.toContinuousLinearMap (A σ))
        (LinearMap.toContinuousLinearMap (B σ)) (binaryTensorFiberEquiv σ x))
    convert hd using 1
    · funext t
      change (binaryTensorFiberEquiv σ).symm _ = (binaryTensorFiberEquiv σ).symm _
      congr 1
      induction binaryTensorFiberEquiv σ x using TensorProduct.inductionOn with
      | tmul u v => rfl
      | add u v hu hv => simp only [map_add, hu, hv]
    · rfl

/-- A local maximum of the actual tensor submodule degree forces stationarity
against both tensor-factor generators. -/
theorem sum_tensorFiberProjectionTrace_eq_zero_of_isLocalMax
    (h : HermitianMetric (K := K) M) (k : HermitianMetric (K := K) N)
    (P : Submodule (𝓞 K) (M ⊗[𝓞 K] N))
    (A : ∀ σ : K →+* ℂ, Module.End ℂ (ComplexFiber M σ))
    (B : ∀ σ : K →+* ℂ, Module.End ℂ (ComplexFiber N σ))
    (hs : ∀ σ x y, (h.fiber σ).inner (A σ x) y = (h.fiber σ).inner x (A σ y))
    (ks : ∀ σ x y, (k.fiber σ).inner (B σ x) y = (k.fiber σ).inner x (B σ y))
    (hc : ∀ σ x, A (ComplexEmbedding.conjugate σ) (fiberConjugate M σ x) =
      fiberConjugate M σ (A σ x))
    (kc : ∀ σ x, B (ComplexEmbedding.conjugate σ) (fiberConjugate N σ x) =
      fiberConjugate N σ (B σ x))
    (hmax : IsLocalMax (fun t => (((h.exponentialVariation A hs hc t).tensor
      (k.exponentialVariation B ks kc t)).submodule P).degree) 0) :
    ∑ σ, (h.tensor k).fiberProjectionTrace P σ (tensorFiberGenerator A B σ) = 0 := by
  have he := hmax.hasDerivAt_eq_zero
    (hasDerivAt_submodule_degree_tensor_exponentialVariation h k P A B hs ks hc kc)
  have hD : (Module.finrank ℚ K : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'
  exact neg_eq_zero.mp ((div_eq_zero_iff.mp he).resolve_right hD)

end HermitianMetric
end BostConjecture.Arithmetic
