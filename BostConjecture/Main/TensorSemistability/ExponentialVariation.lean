module

public import BostConjecture.Main.TensorSemistability.MetricVariation
public import BostConjecture.Balanced.ExponentialDeterminant
public import BostConjecture.Balanced.ExponentialFlow

/-!
# Conjugation-compatible exponential changes of metric

The exponential of a Hermitian endomorphism is a fiber automorphism.
Conjugate-linear intertwiners commute with real-time exponential flows.
These facts produce admissible archimedean metric changes on the original
integral module.

Reference: bost_specht_manuscript.pdf, Proposition 7.3, page 13.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Arithmetic

section ComplexFlow

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F]

/-- The real-time operator exponential as an actual linear automorphism. -/
def expLinearEquiv (A : E →L[ℂ] E) (t : ℝ) : E ≃ₗ[ℂ] E := by
  let := FiniteDimensional.complete ℂ E
  refine
    { (NormedSpace.exp (t • A)).toLinearMap with
      invFun := fun x => (NormedSpace.exp (-(t • A)) : E →L[ℂ] E) x
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    have he : NormedSpace.exp (-(t • A)) * NormedSpace.exp (t • A) = 1 := by
      rw [← NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℂ)
        (Commute.refl (t • A)).neg_left
        (by simp [NormedSpace.expSeries_radius_eq_top])
        (by simp [NormedSpace.expSeries_radius_eq_top]),
        neg_add_cancel, NormedSpace.exp_zero]
    exact congrArg (fun f : E →L[ℂ] E => f x) he
  · intro x
    have he : NormedSpace.exp (t • A) * NormedSpace.exp (-(t • A)) = 1 := by
      rw [← NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℂ)
        (Commute.refl (t • A)).neg_right
        (by simp [NormedSpace.expSeries_radius_eq_top])
        (by simp [NormedSpace.expSeries_radius_eq_top]),
        add_neg_cancel, NormedSpace.exp_zero]
    exact congrArg (fun f : E →L[ℂ] E => f x) he

@[simp]
lemma expLinearEquiv_apply (A : E →L[ℂ] E) (t : ℝ) (x : E) :
    expLinearEquiv A t x = NormedSpace.exp (t • A) x := rfl

/-- A conjugate-linear intertwiner commutes with real-time Hermitian
exponentials. No choice of real or complex embedding is made here. -/
theorem expLinearEquiv_conjugate (A : Module.End ℂ E) (B : Module.End ℂ F)
    (hA : A.IsSymmetric) (c : E ≃ₗ⋆[ℂ] F)
    (hc : ∀ x, B (c x) = c (A x)) (t : ℝ) (x : E) :
    expLinearEquiv (LinearMap.toContinuousLinearMap B) t (c x) =
      c (expLinearEquiv (LinearMap.toContinuousLinearMap A) t x) := by
  let b := hA.eigenvectorBasis rfl
  have he (i) : B (c (b i)) = ((hA.eigenvalues rfl i : ℝ) : ℂ) • c (b i) := by
    rw [hc, hA.apply_eigenvectorBasis rfl i, map_smulₛₗ]
    rw [RCLike.conj_ofReal]
    rfl
  have hf (i) : expLinearEquiv (LinearMap.toContinuousLinearMap B) t (c (b i)) =
      c (expLinearEquiv (LinearMap.toContinuousLinearMap A) t (b i)) := by
    simp only [expLinearEquiv_apply]
    rw [Balanced.exp_real_smul_apply_of_apply_eq_smul _ _ _ _ (he i),
      Balanced.exp_real_smul_apply_of_apply_eq_smul _ _ _ _
        (hA.apply_eigenvectorBasis rfl i), map_smulₛₗ]
    rw [Complex.conj_ofReal]
    simp only [Algebra.algebraMap_self_apply]
  conv_lhs => rw [← b.sum_repr x]
  conv_rhs => rw [← b.sum_repr x]
  simp only [map_sum, map_smulₛₗ, RingHom.id_apply, hf]

/-- A traceless Hermitian generator has determinant-one real-time flow. -/
theorem det_expLinearEquiv (A : Module.End ℂ E) (hA : A.IsSymmetric)
    (htr : LinearMap.trace ℂ E A = 0) (t : ℝ) :
    LinearMap.det (expLinearEquiv (LinearMap.toContinuousLinearMap A) t).toLinearMap = 1 := by
  have hs : (t • A).IsSymmetric := by
    intro x y
    simp only [LinearMap.smul_apply, RCLike.real_smul_eq_coe_smul (K := ℂ),
      inner_smul_left, inner_smul_right, hA x y]
    rw [RCLike.conj_ofReal]
  have he := Balanced.det_exp_of_isSymmetric (t • A) hs
  have htrace : LinearMap.trace ℂ E (t • A) = 0 := by
    change LinearMap.trace ℂ E ((t : ℂ) • A) = 0
    rw [map_smul, htr, smul_zero]
  rw [htrace] at he
  have heq : LinearMap.toContinuousLinearMap (t • A) =
      t • LinearMap.toContinuousLinearMap A := by ext x; rfl
  rw [heq] at he
  simpa only [expLinearEquiv, Complex.zero_re, Real.exp_zero,
    Complex.ofReal_one] using he

end ComplexFlow

namespace HermitianMetric

open NumberField

variable {K : Type*} [Field K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M] [Module.Finite (𝓞 K) M]

/-- Exponentiation in the norm supplied by the actual fiber metric. -/
def fiberExp (h : HermitianMetric (K := K) M) (σ : K →+* ℂ)
    (A : Module.End ℂ (ComplexFiber M σ)) (t : ℝ) :
    ComplexFiber M σ ≃ₗ[ℂ] ComplexFiber M σ := by
  letI : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  letI := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
  letI := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
  exact expLinearEquiv (LinearMap.toContinuousLinearMap A) t

/-- Fiber conjugation intertwines the exponential automorphisms. -/
theorem fiberExp_conjugate (h : HermitianMetric (K := K) M)
    (A : ∀ σ : K →+* ℂ, Module.End ℂ (ComplexFiber M σ))
    (hs : ∀ σ x y, (h.fiber σ).inner (A σ x) y = (h.fiber σ).inner x (A σ y))
    (hc : ∀ σ x, A (ComplexEmbedding.conjugate σ) (fiberConjugate M σ x) =
      fiberConjugate M σ (A σ x)) (t : ℝ) (σ : K →+* ℂ) (x : ComplexFiber M σ) :
    h.fiberExp (ComplexEmbedding.conjugate σ) (A _) t (fiberConjugate M σ x) =
      fiberConjugate M σ (h.fiberExp σ (A σ) t x) := by
  letI (τ : K →+* ℂ) : InnerProductSpace.Core ℂ (ComplexFiber M τ) := h.fiber τ
  letI (τ : K →+* ℂ) :=
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M τ)
  letI (τ : K →+* ℂ) := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M τ))
  exact expLinearEquiv_conjugate (A σ) (A _) (hs σ) (fiberConjugate M σ) (hc σ) t x

/-- The actual arithmetic metric along a compatible self-adjoint flow. -/
def exponentialVariation (h : HermitianMetric (K := K) M)
    (A : ∀ σ : K →+* ℂ, Module.End ℂ (ComplexFiber M σ))
    (hs : ∀ σ x y, (h.fiber σ).inner (A σ x) y = (h.fiber σ).inner x (A σ y))
    (hc : ∀ σ x, A (ComplexEmbedding.conjugate σ) (fiberConjugate M σ x) =
      fiberConjugate M σ (A σ x)) (t : ℝ) : HermitianMetric (K := K) M :=
  h.archimedeanPullback (fun σ => h.fiberExp σ (A σ) t)
    (h.fiberExp_conjugate A hs hc t)

end HermitianMetric

end BostConjecture.Arithmetic
