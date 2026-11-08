/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Tensor.Submodule

/-!
# Transport of actual quotient metrics

Isometric commuting quotient diagrams and successive orthogonal quotients
supply the metric identifications needed by the HN tensor grades.
-/

@[expose] public section
noncomputable section
open NumberField TensorProduct
open scoped InnerProductSpace

namespace BostConjecture.Arithmetic
namespace ComplexQuotient

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [AddCommGroup F] [Module ℂ F]
    [AddCommGroup G] [Module ℂ G]

/-- Pairing with an orthogonal lift depends only on the image of the other vector. -/
lemma inner_lift_map (f : E →ₗ[ℂ] F) (hf : Function.Surjective f) (x : E) (y : F) :
    inner ℂ (lift f hf (f x)) (lift f hf y) = inner ℂ x (lift f hf y) := by
  have hk : x - lift f hf (f x) ∈ LinearMap.ker f := by
    simp [LinearMap.mem_ker]
  have ho := (Submodule.mem_orthogonal _ _).mp (lift_mem f hf y) _ hk
  rw [inner_sub_left] at ho
  exact (sub_eq_zero.mp ho).symm

end ComplexQuotient

namespace HermitianMetric

universe u
variable {K : Type*} [Field K] [NumberField K]
variable {M N P Q : Type u}
    [AddCommGroup M] [Module (𝓞 K) M]
    [AddCommGroup N] [Module (𝓞 K) N]
    [AddCommGroup P] [Module (𝓞 K) P]
    [AddCommGroup Q] [Module (𝓞 K) Q]
    [Module.Finite (𝓞 K) M] [Module.Finite (𝓞 K) N]

/-- An isometric commuting square identifies its actual quotient metrics when
the larger kernel is contained in the isometric image. -/
lemma pushforward_natural_inner
    (h : HermitianMetric K M) (g : HermitianMetric K N)
    (i : M →ₗ[𝓞 K] N)
    (hi : ∀ σ x y, (g.fiber σ).inner (fiberMap i σ x) (fiberMap i σ y) =
      (h.fiber σ).inner x y)
    (f : M →ₗ[𝓞 K] P) (hf : Function.Surjective f)
    (q : N →ₗ[𝓞 K] Q) (hq : Function.Surjective q)
    (j : P →ₗ[𝓞 K] Q) (hj : Function.Injective j)
    (hc : q.comp i = j.comp f)
    (hk : ∀ σ, LinearMap.ker (fiberMap q σ) ≤ LinearMap.range (fiberMap i σ))
    (σ : K →+* ℂ) (x y : ComplexFiber P σ) :
    ((g.pushforward q hq).fiber σ).inner (fiberMap j σ x) (fiberMap j σ y) =
      ((h.pushforward f hf).fiber σ).inner x y := by
  let : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
  let := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
  let : InnerProductSpace.Core ℂ (ComplexFiber N σ) := g.fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber N σ)
  let := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber N σ))
  have hl (z : ComplexFiber P σ) :
      fiberMap i σ (h.fiberLift f hf σ z) =
        g.fiberLift q hq σ (fiberMap j σ z) := by
    apply ComplexQuotient.lift_natural (fiberMap i σ) (hi σ)
      (fiberMap f σ) (fiberMap_surjective f hf σ)
      (fiberMap q σ) (fiberMap_surjective q hq σ)
      (fiberMap j σ) (fiberMap_injective j hj σ)
    · intro z
      have he := congrArg (fun a => fiberMap a σ) hc
      simp only [fiberMap_comp] at he
      exact LinearMap.congr_fun he z
    · exact hk σ
  change (g.fiber σ).inner (g.fiberLift q hq σ _) (g.fiberLift q hq σ _) = _
  rw [← hl, ← hl, hi]
  rfl

omit [NumberField K] in
/-- Successive quotient metrics agree with the quotient by the composite. -/
lemma pushforward_comp (h : HermitianMetric K M)
    (f : M →ₗ[𝓞 K] N) (hf : Function.Surjective f)
    (q : N →ₗ[𝓞 K] P) (hq : Function.Surjective q) :
    (h.pushforward f hf).pushforward q hq =
      h.pushforward (q.comp f) (hq.comp hf) := by
  apply ext_inner
  intro σ x y
  let : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
  let := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
  let : InnerProductSpace.Core ℂ (ComplexFiber N σ) := (h.pushforward f hf).fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber N σ)
  let := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber N σ))
  have hl (z : ComplexFiber P σ) :
      h.fiberLift f hf σ ((h.pushforward f hf).fiberLift q hq σ z) =
        h.fiberLift (q.comp f) (hq.comp hf) σ z := by
    apply ComplexQuotient.eq_lift
    · rw [Submodule.mem_orthogonal]
      intro u hu
      change (h.fiber σ).inner u (h.fiberLift f hf σ _) = 0
      have hip := ComplexQuotient.inner_lift_map (fiberMap f σ)
        (fiberMap_surjective f hf σ) u ((h.pushforward f hf).fiberLift q hq σ z)
      change (h.fiber σ).inner (h.fiberLift f hf σ (fiberMap f σ u))
          (h.fiberLift f hf σ _) = (h.fiber σ).inner u (h.fiberLift f hf σ _) at hip
      rw [← hip]
      have hu' : fiberMap f σ u ∈ LinearMap.ker (fiberMap q σ) := by
        change fiberMap q σ (fiberMap f σ u) = 0
        rw [← LinearMap.comp_apply, ← fiberMap_comp]
        exact hu
      exact (Submodule.mem_orthogonal _ _).mp
        (ComplexQuotient.lift_mem (fiberMap q σ) (fiberMap_surjective q hq σ) z) _ hu'
    · rw [fiberMap_comp, LinearMap.comp_apply, h.fiberMap_fiberLift,
        (h.pushforward f hf).fiberMap_fiberLift]
  change (h.fiber σ).inner
      (h.fiberLift f hf σ ((h.pushforward f hf).fiberLift q hq σ x))
      (h.fiberLift f hf σ ((h.pushforward f hf).fiberLift q hq σ y)) = _
  rw [hl, hl]
  rfl

/-- The actual quotient metric commutes with left tensoring. -/
lemma tensor_pushforward_left (h : HermitianMetric K M)
    (g : HermitianMetric K N) (f : N →ₗ[𝓞 K] P) (hf : Function.Surjective f) :
    (h ⊗[𝓞 K] g).pushforward (f.lTensor M) (LinearMap.lTensor_surjective M hf) =
      h ⊗[𝓞 K] (g.pushforward f hf) := by
  apply ext_inner
  intro σ x y
  have he := pushforward_natural_inner (h ⊗[𝓞 K] g) (g ⊗[𝓞 K] h)
    (TensorProduct.comm (𝓞 K) M N).toLinearMap (tensor_comm_inner h g)
    (f.lTensor M) (LinearMap.lTensor_surjective M hf)
    (f.rTensor M) (LinearMap.rTensor_surjective M hf)
    (TensorProduct.comm (𝓞 K) M P).toLinearMap (TensorProduct.comm _ _ _).injective
    (by ext m n; rfl)
    (fun σ z _ => fiberMap_surjective _ (TensorProduct.comm _ _ _).surjective σ z) σ x y
  rw [tensor_pushforward, tensor_comm_inner] at he
  exact he.symm

/-- Simultaneous actual quotients carry the Hilbert tensor quotient metric. -/
lemma tensor_map_pushforward (h : HermitianMetric K M)
    (g : HermitianMetric K N)
    (f : M →ₗ[𝓞 K] P) (hf : Function.Surjective f)
    (j : N →ₗ[𝓞 K] Q) (hj : Function.Surjective j) :
    (h ⊗[𝓞 K] g).pushforward (TensorProduct.map f j)
        (TensorProduct.map_surjective hf hj) =
      (h.pushforward f hf) ⊗[𝓞 K] (g.pushforward j hj) := by
  let : Module.Finite (𝓞 K) P := Module.Finite.of_surjective f hf
  have hc : (j.lTensor P).comp (f.rTensor N) = TensorProduct.map f j := by
    ext m n
    rfl
  have he := (h ⊗[𝓞 K] g).pushforward_comp (f.rTensor N)
    (LinearMap.rTensor_surjective N hf) (j.lTensor P) (LinearMap.lTensor_surjective P hj)
  rw [tensor_pushforward, tensor_pushforward_left] at he
  simpa only [hc] using he.symm

end HermitianMetric
end BostConjecture.Arithmetic
