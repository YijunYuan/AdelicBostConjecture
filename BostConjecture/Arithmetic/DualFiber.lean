module

public import BostConjecture.Arithmetic.FiberConjugation
public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.LinearAlgebra.Contraction

/-!
# Scalar extension of the intrinsic integral dual

The canonical dual base-change map is an equivalence for finite projective
modules. The arithmetic specialization has the expected evaluation formula
and intertwines conjugation on the entire dual fiber.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct Module

namespace BostConjecture.Arithmetic

section BaseChange

variable (R S M : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M]

/-- The scalar-linear extension of Mathlib's canonical dual base-change map. -/
def dualBaseChangeMap : S ⊗[R] Dual R M →ₗ[S] Dual S (S ⊗[R] M) :=
  (Module.Dual.baseChange (V := M) S).liftBaseChange S

@[simp]
lemma dualBaseChangeMap_tmul (a b : S) (f : Dual R M) (x : M) :
    dualBaseChangeMap R S M (a ⊗ₜ[R] f) (b ⊗ₜ[R] x) =
      a * b * algebraMap R S (f x) := by
  simp [dualBaseChangeMap, Algebra.smul_def, mul_comm, mul_assoc]

variable [Module.Finite R M] [Module.Projective R M]

/-- Dual base change is bijective without an integral freeness hypothesis. -/
lemma dualBaseChangeMap_bijective : Function.Bijective (dualBaseChangeMap R S M) := by
  let e : S ⊗[R] Dual R M ≃ₗ[R] Dual S (S ⊗[R] M) :=
    (TensorProduct.comm R S (Dual R M)).trans
      ((dualTensorHomEquiv R M S).trans ((LinearMap.liftBaseChangeEquiv S).restrictScalars R))
  have he : (dualBaseChangeMap R S M).restrictScalars R = e.toLinearMap := by
    apply TensorProduct.ext'
    intro a f
    apply TensorProduct.AlgebraTensorModule.ext
    intro b x
    simp [e, dualBaseChangeMap_tmul, Algebra.smul_def, mul_comm, mul_left_comm, mul_assoc]
  change Function.Bijective ((dualBaseChangeMap R S M).restrictScalars R)
  rw [he]
  exact e.bijective

/-- The canonical scalar-linear dual base-change equivalence. -/
def dualBaseChangeEquiv : S ⊗[R] Dual R M ≃ₗ[S] Dual S (S ⊗[R] M) :=
  LinearEquiv.ofBijective (dualBaseChangeMap R S M) (dualBaseChangeMap_bijective R S M)

@[simp]
lemma dualBaseChangeEquiv_tmul (a b : S) (f : Dual R M) (x : M) :
    dualBaseChangeEquiv R S M (a ⊗ₜ[R] f) (b ⊗ₜ[R] x) =
      a * b * algebraMap R S (f x) := dualBaseChangeMap_tmul R S M a b f x

end BaseChange

variable {K : Type*} [Field K]
variable (M : Type*) [AddCommGroup M] [Module (𝓞 K) M]
    [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]

/-- The actual complex fiber of the integral dual is the complex algebraic dual. -/
def dualFiberEquiv (σ : K →+* ℂ) :
    ComplexFiber (Dual (𝓞 K) M) σ ≃ₗ[ℂ] Dual ℂ (ComplexFiber M σ) :=
  letI : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  dualBaseChangeEquiv (𝓞 K) ℂ M

@[simp]
lemma dualFiberEquiv_section (σ : K →+* ℂ) (f : Dual (𝓞 K) M) (x : M) :
    dualFiberEquiv M σ (fiberSection _ σ f) (fiberSection M σ x) = σ (f x) := by
  let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  simp [dualFiberEquiv, fiberSection, dualBaseChangeEquiv_tmul]
  rfl

/-- Conjugation of dual fibers is characterized by conjugating evaluation. -/
lemma dualFiberEquiv_conjugate (σ : K →+* ℂ)
    (f : ComplexFiber (Dual (𝓞 K) M) σ) (x : ComplexFiber M σ) :
    dualFiberEquiv M (ComplexEmbedding.conjugate σ)
        (fiberConjugate (Dual (𝓞 K) M) σ f) (fiberConjugate M σ x) =
      star (dualFiberEquiv M σ f x) := by
  let : Module ℂ (ComplexFiber M (ComplexEmbedding.conjugate σ)) := inferInstance
  let : Module ℂ (ComplexFiber (Dual (𝓞 K) M) (ComplexEmbedding.conjugate σ)) := inferInstance
  let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  have he (z : ℂ) (v : M) :
      z ⊗ₜ[𝓞 K] v = z • fiberSection M σ v := by simp [fiberSection, smul_tmul']
  have hd (z : ℂ) (v : Dual (𝓞 K) M) :
      z ⊗ₜ[𝓞 K] v = z • fiberSection (Dual (𝓞 K) M) σ v := by
    simp [fiberSection, smul_tmul']
  induction f using TensorProduct.inductionOn with
  | tmul a f =>
    induction x using TensorProduct.inductionOn with
    | tmul b x =>
      rw [hd a f, he b x]
      simp only [map_smulₛₗ, RingHom.id_apply, fiberConjugate_section,
        LinearMap.smul_apply, dualFiberEquiv_section, ComplexEmbedding.conjugate_coe_eq,
        smul_eq_mul, star_mul]
      change star b * (star a * star (σ (f x))) = star (σ (f x)) * star a * star b
      ac_rfl
    | add x y hx hy => simp only [map_add, star_add, hx, hy]
  | add f g hf hg => simp only [map_add, LinearMap.add_apply, star_add, hf, hg]

end BostConjecture.Arithmetic
