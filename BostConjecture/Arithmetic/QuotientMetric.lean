module

public import BostConjecture.Arithmetic.FiberConjugation
public import BostConjecture.Arithmetic.OrthogonalLift
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Canonical quotient Hermitian metrics

The metric on a quotient is constructed from the orthogonal right inverse
of its actual complex fiber map. Conjugation compatibility follows from
uniqueness of orthogonal representatives, not from an additional hypothesis.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct
open scoped InnerProductSpace

namespace BostConjecture.Arithmetic

variable {K : Type*} [Field K]
variable {M N : Type*} [AddCommGroup M] [Module (𝓞 K) M]
variable [AddCommGroup N] [Module (𝓞 K) N]

/-- Complex scalar extension preserves every integral surjection. -/
lemma fiberMap_surjective (f : M →ₗ[𝓞 K] N) (hf : Function.Surjective f)
    (σ : K →+* ℂ) : Function.Surjective (fiberMap f σ) := by
  let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  exact f.baseChange_surjective ℂ hf

/-- The kernel of the actual quotient fiber map is the image of the submodule fiber. -/
lemma ker_fiberMap_mkQ (P : Submodule (𝓞 K) M) (σ : K →+* ℂ) :
    LinearMap.ker (fiberMap P.mkQ σ) = LinearMap.range (fiberMap P.subtype σ) := by
  let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  have he := lTensor_mkQ ℂ P
  ext x
  exact SetLike.ext_iff.mp he x

namespace HermitianMetric

variable [Module.Finite (𝓞 K) M]

/-- The orthogonal representative of a vector in the target complex fiber. -/
def fiberLift (h : HermitianMetric (K := K) M) (f : M →ₗ[𝓞 K] N)
    (hf : Function.Surjective f) (σ : K →+* ℂ) :
    ComplexFiber N σ →ₗ[ℂ] ComplexFiber M σ := by
  letI : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  letI := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
  letI := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
  exact ComplexQuotient.lift (fiberMap f σ) (fiberMap_surjective f hf σ)

@[simp]
lemma fiberMap_fiberLift (h : HermitianMetric (K := K) M) (f : M →ₗ[𝓞 K] N)
    (hf : Function.Surjective f) (σ : K →+* ℂ) (x : ComplexFiber N σ) :
    fiberMap f σ (h.fiberLift f hf σ x) = x := by
  let : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
  let := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
  exact ComplexQuotient.map_lift _ _ x

/-- Fiber conjugation carries the orthogonal lift to the orthogonal lift. -/
lemma fiberLift_conjugate (h : HermitianMetric (K := K) M) (f : M →ₗ[𝓞 K] N)
    (hf : Function.Surjective f) (σ : K →+* ℂ) (x : ComplexFiber N σ) :
    fiberConjugate M σ (h.fiberLift f hf σ x) =
      h.fiberLift f hf (ComplexEmbedding.conjugate σ) (fiberConjugate N σ x) := by
  let : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
  let := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
  let : InnerProductSpace.Core ℂ (ComplexFiber M (ComplexEmbedding.conjugate σ)) :=
    h.fiber (ComplexEmbedding.conjugate σ)
  let := InnerProductSpace.Core.toNormedAddCommGroup
    (𝕜 := ℂ) (F := ComplexFiber M (ComplexEmbedding.conjugate σ))
  let := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ
    (ComplexFiber M (ComplexEmbedding.conjugate σ)))
  apply ComplexQuotient.eq_lift
  · rw [Submodule.mem_orthogonal]
    intro u hu
    obtain ⟨v, rfl⟩ := (fiberConjugate M σ).surjective u
    have hv : v ∈ LinearMap.ker (fiberMap f σ) := by
      change fiberMap f σ v = 0
      apply (fiberConjugate N σ).injective
      rw [fiberConjugate_map, map_zero]
      exact hu
    change (h.fiber (ComplexEmbedding.conjugate σ)).inner
      (fiberConjugate M σ v) (fiberConjugate M σ (h.fiberLift f hf σ x)) = 0
    rw [h.inner_conjugate]
    have ho := (Submodule.mem_orthogonal _ _).mp
      (ComplexQuotient.lift_mem (fiberMap f σ) (fiberMap_surjective f hf σ) x) v hv
    exact (congrArg star ho).trans (star_zero ℂ)
  · rw [← fiberConjugate_map, h.fiberMap_fiberLift]

/-- The canonical positive Hermitian form on a target complex fiber. -/
@[instance_reducible]
def pushforwardFiber (h : HermitianMetric (K := K) M) (f : M →ₗ[𝓞 K] N)
    (hf : Function.Surjective f) (σ : K →+* ℂ) :
    InnerProductSpace.Core ℂ (ComplexFiber N σ) := by
  letI : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  letI := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
  letI := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
  exact ComplexQuotient.core (fiberMap f σ) (fiberMap_surjective f hf σ)

lemma pushforwardFiber_inner (h : HermitianMetric (K := K) M) (f : M →ₗ[𝓞 K] N)
    (hf : Function.Surjective f) (σ : K →+* ℂ) (x y : ComplexFiber N σ) :
    (h.pushforwardFiber f hf σ).inner x y =
      (h.fiber σ).inner (h.fiberLift f hf σ x) (h.fiberLift f hf σ y) := rfl

/-- The quotient metric along an actual surjective integral map. -/
def pushforward (h : HermitianMetric (K := K) M) (f : M →ₗ[𝓞 K] N)
    (hf : Function.Surjective f) : HermitianMetric (K := K) N where
  fiber := h.pushforwardFiber f hf
  conjugate := by
    intro σ x y
    simp only [pushforwardFiber_inner, ← fiberConjugate_section N σ,
      ← h.fiberLift_conjugate, h.inner_conjugate]

/-- The canonical quotient Hermitian metric on the actual module quotient. -/
def quotient (h : HermitianMetric (K := K) M) (P : Submodule (𝓞 K) M) :
    HermitianMetric (K := K) (M ⧸ P) := h.pushforward P.mkQ P.mkQ_surjective

/-- An integral quotient map decreases section norms for the quotient metric. -/
lemma sectionNorm_pushforward_le (h : HermitianMetric (K := K) M)
    (f : M →ₗ[𝓞 K] N) (hf : Function.Surjective f) (σ : K →+* ℂ) (x : M) :
    (h.pushforward f hf).sectionNorm σ (f x) ≤ h.sectionNorm σ x := by
  let : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
  let := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
  change ‖h.fiberLift f hf σ (fiberSection N σ (f x))‖ ≤ ‖fiberSection M σ x‖
  rw [← fiberMap_section f σ x]
  exact ComplexQuotient.norm_lift_map_le _ _ _

lemma sectionNorm_quotient_le (h : HermitianMetric (K := K) M)
    (P : Submodule (𝓞 K) M) (σ : K →+* ℂ) (x : M) :
    (h.quotient P).sectionNorm σ (P.mkQ x) ≤ h.sectionNorm σ x :=
  h.sectionNorm_pushforward_le P.mkQ P.mkQ_surjective σ x

/-- The fiber norm is the attained minimum among norms of all lifts. -/
lemma pushforwardFiber_min (h : HermitianMetric (K := K) M)
    (f : M →ₗ[𝓞 K] N) (hf : Function.Surjective f) (σ : K →+* ℂ)
    (y : ComplexFiber N σ) :
    ∃ x : ComplexFiber M σ, fiberMap f σ x = y ∧
      Real.sqrt (((h.pushforwardFiber f hf σ).inner y y).re) =
        Real.sqrt (((h.fiber σ).inner x x).re) ∧
      ∀ z : ComplexFiber M σ, fiberMap f σ z = y →
        Real.sqrt (((h.fiber σ).inner x x).re) ≤
          Real.sqrt (((h.fiber σ).inner z z).re) := by
  let : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
  let := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
  refine ⟨h.fiberLift f hf σ y, h.fiberMap_fiberLift f hf σ y, rfl, ?_⟩
  intro z hz
  change ‖h.fiberLift f hf σ y‖ ≤ ‖z‖
  rw [← hz]
  exact ComplexQuotient.norm_lift_map_le _ _ _

/-- The quotient norm is the attained distance to the actual submodule fiber. -/
lemma quotientFiber_min (h : HermitianMetric (K := K) M)
    (P : Submodule (𝓞 K) M) (σ : K →+* ℂ) (v : ComplexFiber M σ) :
    ∃ u ∈ LinearMap.range (fiberMap P.subtype σ),
      Real.sqrt ((((h.quotient P).fiber σ).inner (fiberMap P.mkQ σ v)
        (fiberMap P.mkQ σ v)).re) = Real.sqrt (((h.fiber σ).inner (v - u) (v - u)).re) ∧
      ∀ w ∈ LinearMap.range (fiberMap P.subtype σ),
        Real.sqrt (((h.fiber σ).inner (v - u) (v - u)).re) ≤
          Real.sqrt (((h.fiber σ).inner (v - w) (v - w)).re) := by
  obtain ⟨x, hx, he, hmin⟩ := h.pushforwardFiber_min P.mkQ P.mkQ_surjective σ
    (fiberMap P.mkQ σ v)
  refine ⟨v - x, ?_, ?_, ?_⟩
  · rw [← ker_fiberMap_mkQ]
    change fiberMap P.mkQ σ (v - x) = 0
    rw [map_sub, hx, sub_self]
  · rw [sub_sub_cancel]
    exact he
  · intro w hw
    rw [← ker_fiberMap_mkQ] at hw
    simpa only [sub_sub_cancel] using hmin (v - w) (by
      rw [map_sub, (LinearMap.mem_ker.mp hw), sub_zero])

/-- Agreement on all orthogonal representatives determines the quotient form. -/
lemma pushforwardFiber_unique (h : HermitianMetric (K := K) M)
    (f : M →ₗ[𝓞 K] N) (hf : Function.Surjective f) (σ : K →+* ℂ)
    (c : InnerProductSpace.Core ℂ (ComplexFiber N σ))
    (hc : ∀ x y : ComplexFiber N σ, c.inner x y =
      (h.fiber σ).inner (h.fiberLift f hf σ x) (h.fiberLift f hf σ y)) :
    c = h.pushforwardFiber f hf σ := by
  have he : c.inner = (h.pushforwardFiber f hf σ).inner := funext fun x => funext fun y => hc x y
  generalize hd : h.pushforwardFiber f hf σ = d at he ⊢
  rcases c with ⟨⟨⟨ci⟩, cs, cp, ca, cm⟩, cd⟩
  rcases d with ⟨⟨⟨di⟩, ds, dp, da, dm⟩, dd⟩
  cases he
  rfl

end HermitianMetric
end BostConjecture.Arithmetic
