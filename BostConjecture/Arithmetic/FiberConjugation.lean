module

public import BostConjecture.Arithmetic.SubmoduleMetric

/-!
# Conjugation on intrinsic complex fibers

The canonical conjugate-linear equivalence sends `z ⊗ x` to `conj z ⊗ x`.
It is natural in the integral module and carries each compatible Hermitian
form to its complex conjugate on the entire fiber.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace BostConjecture.Arithmetic

variable {K : Type*} [Field K]
variable (M : Type*) [AddCommGroup M] [Module (𝓞 K) M]

/-- Additive fiber conjugation between an explicitly conjugate pair of embeddings. -/
def conjugateAddHom (σ τ : K →+* ℂ) (hτ : ∀ a, τ a = star (σ a)) :
    ComplexFiber M σ →+ ComplexFiber M τ := by
  letI : Module ℂ (ComplexFiber M τ) := inferInstance
  letI : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  let f : ℂ →+ M →+ ComplexFiber M τ :=
    { toFun := fun z =>
        { toFun := fun x => star z • fiberSection M τ x
          map_zero' := by simp [fiberSection]
          map_add' := by intros; simp [fiberSection, tmul_add, smul_add] }
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp [star_add, add_smul] }
  refine TensorProduct.liftAddHom f ?_
  intro a z x
  change star (σ a * z) • fiberSection M τ x =
    star z • fiberSection M τ (a • x)
  rw [fiberSection_smul, hτ, star_mul, smul_smul, mul_comm]

lemma conjugateAddHom_tmul (σ τ : K →+* ℂ)
    (hτ : ∀ a, τ a = star (σ a)) (z : ℂ) (x : M) :
    letI : Module ℂ (ComplexFiber M τ) := inferInstance
    letI : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
    conjugateAddHom M σ τ hτ (z ⊗ₜ[𝓞 K] x) = star z • fiberSection M τ x := rfl

lemma conjugateAddHom_smul (σ τ : K →+* ℂ)
    (hτ : ∀ a, τ a = star (σ a)) (z : ℂ) (x : ComplexFiber M σ) :
    conjugateAddHom M σ τ hτ (z • x) = star z • conjugateAddHom M σ τ hτ x := by
  let : Module ℂ (ComplexFiber M τ) := inferInstance
  let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  induction x using TensorProduct.inductionOn with
  | tmul w x =>
    rw [smul_tmul', smul_eq_mul, conjugateAddHom_tmul, conjugateAddHom_tmul,
      star_mul, smul_smul, mul_comm]
  | add x y hx hy => simp [smul_add, hx, hy]

lemma conjugateAddHom_inverse (σ τ : K →+* ℂ)
    (hτ : ∀ a, τ a = star (σ a)) (hσ : ∀ a, σ a = star (τ a))
    (x : ComplexFiber M σ) :
    conjugateAddHom M τ σ hσ (conjugateAddHom M σ τ hτ x) = x := by
  let : Module ℂ (ComplexFiber M τ) := inferInstance
  let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  induction x using TensorProduct.inductionOn with
  | tmul z x =>
    rw [conjugateAddHom_tmul, conjugateAddHom_smul]
    have hs : conjugateAddHom M τ σ hσ (fiberSection M τ x) = fiberSection M σ x := by
      change star (1 : ℂ) • fiberSection M σ x = _
      simp
    rw [hs, star_star]
    simp [fiberSection, smul_tmul']
  | add x y hx hy => simp [hx, hy]

/-- The canonical conjugate-linear equivalence of conjugate archimedean fibers. -/
def fiberConjugate (σ : K →+* ℂ) :
    ComplexFiber M σ ≃ₗ⋆[ℂ] ComplexFiber M (ComplexEmbedding.conjugate σ) := by
  let τ := ComplexEmbedding.conjugate σ
  have hτ : ∀ a, τ a = star (σ a) := fun _ => rfl
  have hσ : ∀ a, σ a = star (τ a) := fun a => by rw [hτ, star_star]
  exact
    { toFun := conjugateAddHom M σ τ hτ
      invFun := conjugateAddHom M τ σ hσ
      left_inv := conjugateAddHom_inverse M σ τ hτ hσ
      right_inv := conjugateAddHom_inverse M τ σ hσ hτ
      map_add' := (conjugateAddHom M σ τ hτ).map_add
      map_smul' := conjugateAddHom_smul M σ τ hτ }

@[simp]
lemma fiberConjugate_section (σ : K →+* ℂ) (x : M) :
    fiberConjugate M σ (fiberSection M σ x) =
      fiberSection M (ComplexEmbedding.conjugate σ) x := by
  change star (1 : ℂ) • fiberSection M (ComplexEmbedding.conjugate σ) x = _
  simp

@[simp]
lemma fiberConjugate_symm_section (σ : K →+* ℂ) (x : M) :
    (fiberConjugate M σ).symm (fiberSection M (ComplexEmbedding.conjugate σ) x) =
      fiberSection M σ x := by
  apply (fiberConjugate M σ).injective
  simp

variable {M}

/-- Fiber conjugation commutes with every integral linear map. -/
lemma fiberConjugate_map {N : Type*} [AddCommGroup N] [Module (𝓞 K) N]
    (f : M →ₗ[𝓞 K] N) (σ : K →+* ℂ) (x : ComplexFiber M σ) :
    fiberConjugate N σ (fiberMap f σ x) =
      fiberMap f (ComplexEmbedding.conjugate σ) (fiberConjugate M σ x) := by
  let : Module ℂ (ComplexFiber M (ComplexEmbedding.conjugate σ)) := inferInstance
  let : Module ℂ (ComplexFiber N (ComplexEmbedding.conjugate σ)) := inferInstance
  let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  induction x using TensorProduct.inductionOn with
  | tmul z x =>
    have he : z ⊗ₜ[𝓞 K] x = z • fiberSection M σ x := by
      simp [fiberSection, smul_tmul']
    rw [he]
    simp only [map_smulₛₗ, RingHom.id_apply, fiberMap_section, fiberConjugate_section]
  | add x y hx hy => simp only [map_add, hx, hy]

namespace HermitianMetric

/-- Compatibility on integral sections implies antiunitarity on the whole fiber. -/
lemma inner_conjugate (h : HermitianMetric (K := K) M) (σ : K →+* ℂ)
    (x y : ComplexFiber M σ) :
    (h.fiber (ComplexEmbedding.conjugate σ)).inner
      (fiberConjugate M σ x) (fiberConjugate M σ y) = star ((h.fiber σ).inner x y) := by
  let : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  let : InnerProductSpace.Core ℂ (ComplexFiber M (ComplexEmbedding.conjugate σ)) :=
    h.fiber (ComplexEmbedding.conjugate σ)
  let : Module ℂ (ComplexFiber M (ComplexEmbedding.conjugate σ)) := inferInstance
  let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  have he (z : ℂ) (x : M) : z ⊗ₜ[𝓞 K] x = z • fiberSection M σ x := by
    simp [fiberSection, smul_tmul']
  induction x using TensorProduct.inductionOn with
  | tmul z x =>
    induction y using TensorProduct.inductionOn with
    | tmul w y =>
      rw [he z x, he w y]
      simp only [map_smulₛₗ, fiberConjugate_section,
        InnerProductSpace.Core.inner_smul_left, InnerProductSpace.Core.inner_smul_right,
        h.conjugate, RCLike.star_def, map_mul]
    | add y₁ y₂ h₁ h₂ =>
      simp only [map_add, InnerProductSpace.Core.inner_add_right, star_add, h₁, h₂]
  | add x₁ x₂ h₁ h₂ =>
    simp only [map_add, InnerProductSpace.Core.inner_add_left, star_add, h₁, h₂]

end HermitianMetric
end BostConjecture.Arithmetic
