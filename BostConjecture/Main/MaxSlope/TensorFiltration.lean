module

public import BostConjecture.Main.MaxSlope.LowerBound

/-!
# Actual tensor submodules and their saturated quotients

The terms of a tensor filtration are actual images in the integral tensor
product. Right exactness identifies their quotients without any integral
freeness assumption; the corresponding metrics are the Hilbert tensor metrics.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace BostConjecture.Arithmetic

universe u
variable {K : Type*} [Field K]
variable {M : Type u} [AddCommGroup M] [Module (𝓞 K) M]
variable (N : Type u) [AddCommGroup N] [Module (𝓞 K) N]

/-- The actual image of a submodule tensored with the entire second factor. -/
def tensorRight (P : Submodule (𝓞 K) M) : Submodule (𝓞 K) (M ⊗[𝓞 K] N) :=
  LinearMap.range (P.subtype.rTensor N)

lemma tensorRight_mono {P Q : Submodule (𝓞 K) M} (hPQ : P ≤ Q) :
    tensorRight N P ≤ tensorRight N Q := by
  rintro x ⟨y, rfl⟩
  refine ⟨(Submodule.inclusion hPQ).rTensor N y, ?_⟩
  have he : (Q.subtype.rTensor N).comp ((Submodule.inclusion hPQ).rTensor N) =
      P.subtype.rTensor N := by
    ext p n
    rfl
  exact LinearMap.congr_fun he y

@[simp]
lemma tensorRight_bot : tensorRight N (⊥ : Submodule (𝓞 K) M) = ⊥ := by
  have he : (⊥ : Submodule (𝓞 K) M).subtype.rTensor N = 0 := by
    ext p n
    simp [show (p : M) = 0 from p.property]
  simp [tensorRight, he]

@[simp]
lemma tensorRight_top : tensorRight N (⊤ : Submodule (𝓞 K) M) = ⊤ := by
  apply LinearMap.range_eq_top.mpr
  apply LinearMap.rTensor_surjective
  intro x
  exact ⟨⟨x, trivial⟩, rfl⟩

/-- Right exactness computes the actual tensor image as the quotient-map kernel. -/
lemma tensorRight_eq_ker (P : Submodule (𝓞 K) M) :
    tensorRight N P = LinearMap.ker (P.mkQ.rTensor N) :=
  (rTensor_mkQ N P).symm

/-- The canonical integral tensor quotient identification. -/
def tensorRightQuotientEquiv (P : Submodule (𝓞 K) M) :
    ((M ⊗[𝓞 K] N) ⧸ tensorRight N P) ≃ₗ[𝓞 K] ((M ⧸ P) ⊗[𝓞 K] N) :=
  (Submodule.quotEquivOfEq _ _ (tensorRight_eq_ker N P)).trans
    ((P.mkQ.rTensor N).quotKerEquivOfSurjective (LinearMap.rTensor_surjective N P.mkQ_surjective))

@[simp]
lemma tensorRightQuotientEquiv_mkQ (P : Submodule (𝓞 K) M) (x : M ⊗[𝓞 K] N) :
    tensorRightQuotientEquiv N P ((tensorRight N P).mkQ x) = P.mkQ.rTensor N x := rfl

instance tensorRightQuotientProjective (P : Submodule (𝓞 K) M)
    [Module.Projective (𝓞 K) (M ⧸ P)] [Module.Projective (𝓞 K) N] :
    Module.Projective (𝓞 K) ((M ⊗[𝓞 K] N) ⧸ tensorRight N P) :=
  Module.Projective.of_equiv (tensorRightQuotientEquiv N P).symm

/-- The tensor injection identifies its source with the actual integral image. -/
def tensorRightEquiv [Module.Flat (𝓞 K) N] (P : Submodule (𝓞 K) M) :
    (P ⊗[𝓞 K] N) ≃ₗ[𝓞 K] tensorRight N P :=
  LinearEquiv.ofInjective (P.subtype.rTensor N)
    (Module.Flat.rTensor_preserves_injective_linearMap _ P.injective_subtype)

namespace HermitianMetric

variable [NumberField K]
variable {N}

/-- The integral image of a tensor injection carries the tensor induced metric. -/
lemma tensorRightEquiv_inner [Module.Flat (𝓞 K) N]
    (h : HermitianMetric (K := K) M) (g : HermitianMetric (K := K) N)
    (P : Submodule (𝓞 K) M) (σ : K →+* ℂ)
    (x y : ComplexFiber (P ⊗[𝓞 K] N) σ) :
    (((h.tensor g).submodule (tensorRight N P)).fiber σ).inner
      (fiberMap (tensorRightEquiv N P).toLinearMap σ x)
      (fiberMap (tensorRightEquiv N P).toLinearMap σ y) =
      (((h.submodule P).tensor g).fiber σ).inner x y := by
  have he := congrArg (fun m : HermitianMetric (K := K) (P ⊗[𝓞 K] N) =>
    (m.fiber σ).inner x y) (tensor_pullback h g P.subtype P.injective_subtype)
  change ((h.tensor g).fiber σ).inner
    (fiberMap (tensorRight N P).subtype σ (fiberMap (tensorRightEquiv N P).toLinearMap σ x))
    (fiberMap (tensorRight N P).subtype σ (fiberMap (tensorRightEquiv N P).toLinearMap σ y)) = _
  simp only [← LinearMap.comp_apply, ← fiberMap_comp]
  exact he

variable [Module.Finite (𝓞 K) M]

/-- Two surjections related by an actual integral isomorphism induce the same
quotient metric on the whole complex fibers. -/
lemma pushforward_equiv_inner
    {P : Type u} [AddCommGroup P] [Module (𝓞 K) P]
    (h : HermitianMetric (K := K) M)
    (f : M →ₗ[𝓞 K] N) (hf : Function.Surjective f)
    (q : M →ₗ[𝓞 K] P) (hq : Function.Surjective q)
    (e : N ≃ₗ[𝓞 K] P) (he : e.toLinearMap.comp f = q)
    (σ : K →+* ℂ) (x y : ComplexFiber N σ) :
    ((h.pushforward q hq).fiber σ).inner
      (fiberMap e.toLinearMap σ x) (fiberMap e.toLinearMap σ y) =
      ((h.pushforward f hf).fiber σ).inner x y := by
  let : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
  let := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
  have hl (z : ComplexFiber N σ) :
      h.fiberLift f hf σ z = h.fiberLift q hq σ (fiberMap e.toLinearMap σ z) := by
    apply ComplexQuotient.lift_natural LinearMap.id (fun _ _ => rfl)
      (fiberMap f σ) (fiberMap_surjective f hf σ)
      (fiberMap q σ) (fiberMap_surjective q hq σ)
      (fiberMap e.toLinearMap σ) (fiberMap_injective _ e.injective σ)
    · intro z
      have he' := congrArg (fun j => fiberMap j σ) he
      rw [fiberMap_comp] at he'
      exact (LinearMap.congr_fun he' z).symm
    · intro z _
      exact ⟨z, rfl⟩
  change (h.fiber σ).inner (h.fiberLift q hq σ _) (h.fiberLift q hq σ _) = _
  rw [← hl, ← hl]
  rfl

variable [Module.Finite (𝓞 K) N]

/-- The canonical tensor quotient identification preserves the Hilbert metric. -/
lemma tensorRightQuotientEquiv_inner
    (h : HermitianMetric (K := K) M) (g : HermitianMetric (K := K) N)
    (P : Submodule (𝓞 K) M) (σ : K →+* ℂ)
    (x y : ComplexFiber ((M ⊗[𝓞 K] N) ⧸ tensorRight N P) σ) :
    (((h.quotient P).tensor g).fiber σ).inner
      (fiberMap (tensorRightQuotientEquiv N P).toLinearMap σ x)
      (fiberMap (tensorRightQuotientEquiv N P).toLinearMap σ y) =
      (((h.tensor g).quotient (tensorRight N P)).fiber σ).inner x y := by
  rw [show (h.quotient P).tensor g = (h.tensor g).pushforward
      (P.mkQ.rTensor N) (LinearMap.rTensor_surjective N P.mkQ_surjective) from
    (tensor_pushforward h g P.mkQ P.mkQ_surjective).symm]
  exact pushforward_equiv_inner _ _ (tensorRight N P).mkQ_surjective _
    (LinearMap.rTensor_surjective N P.mkQ_surjective) (tensorRightQuotientEquiv N P)
    (by ext; rfl) σ x y

end HermitianMetric

end BostConjecture.Arithmetic
