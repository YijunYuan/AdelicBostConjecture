module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Finiteness.Projective

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
  letI : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  ℂ ⊗[𝓞 K] M

/-- The canonical map from the integral module into its complex fiber. -/
def fiberSection (σ : K →+* ℂ) (x : M) : ComplexFiber M σ :=
  letI : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
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

end HermitianMetric
end BostConjecture.Arithmetic
