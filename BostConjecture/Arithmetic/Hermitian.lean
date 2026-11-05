module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Finiteness.Projective
public import Mathlib.RingTheory.Flat.Basic

/-!
# Hermitian metrics on intrinsic arithmetic fibers

A metric lives on the canonical scalar extension of an existing module, not
on a chosen coordinate space. Compatibility with conjugation is imposed on
integral generators; sesquilinearity extends it to the entire complex fiber.
The underlying module of a Hermitian bundle is finite projective, without a
freeness hypothesis. No degree or slope identities are part of the data.

Reference: bost_specht_manuscript.pdf, §2, pages 2–3.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace BostConjecture.Arithmetic

variable {K : Type*} [Field K]
variable (M : Type*) [AddCommGroup M] [Module (𝓞 K) M]

/-- The canonical complex fiber at an embedding. -/
abbrev ComplexFiber (σ : K →+* ℂ) :=
  let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  ℂ ⊗[𝓞 K] M

/-- The canonical map from the integral module into its complex fiber. -/
def fiberSection (σ : K →+* ℂ) (x : M) : ComplexFiber M σ :=
  let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  1 ⊗ₜ[𝓞 K] x

/-- Positive-definite fiber metrics compatible with complex conjugation. -/
structure HermitianMetric where
  /-- The Hermitian inner product on each canonical complex fiber. -/
  fiber : ∀ σ : K →+* ℂ, InnerProductSpace.Core ℂ (ComplexFiber M σ)
  /-- Conjugation compatibility on the spanning integral generators. -/
  conjugate : ∀ (σ : K →+* ℂ) (x y : M),
    (fiber (ComplexEmbedding.conjugate σ)).inner
      (fiberSection M (ComplexEmbedding.conjugate σ) x)
      (fiberSection M (ComplexEmbedding.conjugate σ) y) =
    star ((fiber σ).inner (fiberSection M σ x) (fiberSection M σ y))

/-- Integral sections scale by the chosen embedding on the complex fiber. -/
lemma fiberSection_smul (σ : K →+* ℂ) (a : 𝓞 K) (x : M) :
    fiberSection M σ (a • x) = σ a • fiberSection M σ x := by
  let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  change (1 : ℂ) ⊗ₜ[𝓞 K] (a • x) = σ a • ((1 : ℂ) ⊗ₜ[𝓞 K] x)
  rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
  congr 1

/-- Scalar extension at an embedding preserves nonzero integral sections of a
projective module, even when the module is not free. -/
lemma fiberSection_injective [Module.Projective (𝓞 K) M] (σ : K →+* ℂ) :
    Function.Injective (fiberSection M σ) := by
  let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  let : FaithfulSMul (𝓞 K) ℂ :=
    (faithfulSMul_iff_algebraMap_injective (𝓞 K) ℂ).mpr
      (σ.injective.comp RingOfIntegers.coe_injective)
  exact Module.Flat.tensorProduct_mk_injective (𝓞 K) M ℂ

namespace HermitianMetric

variable {M}

/-- Norm of an integral section in an archimedean fiber. -/
def sectionNorm (h : HermitianMetric (K := K) M) (σ : K →+* ℂ) (x : M) : ℝ :=
  Real.sqrt (((h.fiber σ).inner (fiberSection M σ x) (fiberSection M σ x)).re)

@[simp]
lemma sectionNorm_conjugate (h : HermitianMetric (K := K) M)
    (σ : K →+* ℂ) (x : M) :
    h.sectionNorm (ComplexEmbedding.conjugate σ) x = h.sectionNorm σ x := by
  simp only [sectionNorm, h.conjugate, Complex.star_def, Complex.conj_re]

/-- The section norm depends only on the infinite place, not on its representing
complex embedding. -/
lemma sectionNorm_eq_of_place_eq (h : HermitianMetric (K := K) M)
    {σ τ : K →+* ℂ} (heq : InfinitePlace.mk σ = InfinitePlace.mk τ) (x : M) :
    h.sectionNorm σ x = h.sectionNorm τ x := by
  rcases InfinitePlace.mk_eq_iff.mp heq with heq | heq
  · rw [heq]
  · rw [← heq, h.sectionNorm_conjugate]

/-- Fiber norms scale by the archimedean absolute value. -/
lemma sectionNorm_smul (h : HermitianMetric (K := K) M)
    (σ : K →+* ℂ) (a : 𝓞 K) (x : M) :
    h.sectionNorm σ (a • x) = ‖σ a‖ * h.sectionNorm σ x := by
  let : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
  let := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
  change ‖fiberSection M σ (a • x)‖ = ‖σ a‖ * ‖fiberSection M σ x‖
  rw [fiberSection_smul, norm_smul]

lemma sectionNorm_pos [Module.Projective (𝓞 K) M]
    (h : HermitianMetric (K := K) M) (σ : K →+* ℂ) {x : M} (hx : x ≠ 0) :
    0 < h.sectionNorm σ x := by
  let : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
  change 0 < ‖fiberSection M σ x‖
  apply norm_pos_iff.mpr
  intro heq
  apply hx
  apply fiberSection_injective M σ
  simpa only [fiberSection, TensorProduct.tmul_zero] using heq

end HermitianMetric
end BostConjecture.Arithmetic
