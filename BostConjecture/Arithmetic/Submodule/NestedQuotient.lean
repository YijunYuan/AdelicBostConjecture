/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Submodule.QuotientMetric
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Compatibility of induced and quotient Hermitian metrics

For nested integral submodules, the quotient of the induced metric is the
pullback of the ambient quotient metric. The proof compares the actual
orthogonal representatives in the canonical complex fibers.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct
open scoped InnerProductSpace

namespace BostConjecture.Arithmetic

variable {K : Type*} [Field K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]

/-- The canonical inclusion of a submodule quotient in the ambient quotient. -/
def submoduleQuotientMap (P T : Submodule (𝓞 K) M) :
    T ⧸ P.comap T.subtype →ₗ[𝓞 K] M ⧸ P :=
  (P.comap T.subtype).mapQ P T.subtype le_rfl

lemma submoduleQuotientMap_injective (P T : Submodule (𝓞 K) M) :
    Function.Injective (submoduleQuotientMap P T) := by
  rw [← LinearMap.ker_eq_bot]
  simp [submoduleQuotientMap, Submodule.ker_mapQ]

@[simp]
lemma submoduleQuotientMap_mkQ (P T : Submodule (𝓞 K) M) (x : T) :
    submoduleQuotientMap P T ((P.comap T.subtype).mkQ x) = P.mkQ x := rfl

lemma fiberMap_comp {N L : Type*} [AddCommGroup N] [Module (𝓞 K) N]
    [AddCommGroup L] [Module (𝓞 K) L]
    (f : M →ₗ[𝓞 K] N) (g : N →ₗ[𝓞 K] L) (σ : K →+* ℂ) :
    fiberMap (g.comp f) σ = (fiberMap g σ).comp (fiberMap f σ) := by
  let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  exact LinearMap.baseChange_comp f g

/-- The two quotient maps commute with scalar extension of the inclusions. -/
lemma fiberMap_submoduleQuotientMap_mkQ (P T : Submodule (𝓞 K) M)
    (σ : K →+* ℂ) (x : ComplexFiber T σ) :
    fiberMap P.mkQ σ (fiberMap T.subtype σ x) =
      fiberMap (submoduleQuotientMap P T) σ (fiberMap (P.comap T.subtype).mkQ σ x) := by
  have he : P.mkQ.comp T.subtype =
      (submoduleQuotientMap P T).comp (P.comap T.subtype).mkQ := by ext; rfl
  have he' := congrArg (fun f => fiberMap f σ) he
  simp only [fiberMap_comp] at he'
  exact LinearMap.congr_fun he' x

/-- For nested submodules, the ambient quotient kernel lies in the smaller fiber. -/
lemma ker_fiberMap_le_range_subtype {P T : Submodule (𝓞 K) M} (hPT : P ≤ T)
    (σ : K →+* ℂ) :
    LinearMap.ker (fiberMap P.mkQ σ) ≤ LinearMap.range (fiberMap T.subtype σ) := by
  rw [ker_fiberMap_mkQ]
  rintro _ ⟨x, rfl⟩
  refine ⟨fiberMap (Submodule.inclusion hPT) σ x, ?_⟩
  have he : T.subtype.comp (Submodule.inclusion hPT) = P.subtype := rfl
  have he' := congrArg (fun f => fiberMap f σ) he
  rw [fiberMap_comp] at he'
  exact LinearMap.congr_fun he' x

namespace HermitianMetric

variable [NumberField K] [Module.Finite (𝓞 K) M]

/-- Nested quotient constructions have the same orthogonal representative. -/
lemma fiberLift_submodule (h : HermitianMetric (K := K) M)
    {P T : Submodule (𝓞 K) M} (hPT : P ≤ T) (σ : K →+* ℂ)
    (x : ComplexFiber (T ⧸ P.comap T.subtype) σ) :
    fiberMap T.subtype σ
        ((h.submodule T).fiberLift (P.comap T.subtype).mkQ
          (P.comap T.subtype).mkQ_surjective σ x) =
      h.fiberLift P.mkQ P.mkQ_surjective σ (fiberMap (submoduleQuotientMap P T) σ x) := by
  let : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
  let := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
  let : InnerProductSpace.Core ℂ (ComplexFiber T σ) := (h.submodule T).fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber T σ)
  let := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber T σ))
  exact ComplexQuotient.lift_natural (fiberMap T.subtype σ) (fun _ _ => rfl)
    (fiberMap (P.comap T.subtype).mkQ σ)
    (fiberMap_surjective _ (P.comap T.subtype).mkQ_surjective σ)
    (fiberMap P.mkQ σ) (fiberMap_surjective _ P.mkQ_surjective σ)
    (fiberMap (submoduleQuotientMap P T) σ)
    (fiberMap_injective _ (submoduleQuotientMap_injective P T) σ)
    (fiberMap_submoduleQuotientMap_mkQ P T σ) (ker_fiberMap_le_range_subtype hPT σ) x

/-- Quotient metrics commute with restriction to an intermediate submodule. -/
theorem quotient_submodule (h : HermitianMetric (K := K) M)
    {P T : Submodule (𝓞 K) M} (hPT : P ≤ T) :
    (h.submodule T).quotient (P.comap T.subtype) =
      (h.quotient P).pullback (submoduleQuotientMap P T)
        (submoduleQuotientMap_injective P T) := by
  have hf : ((h.submodule T).quotient (P.comap T.subtype)).fiber =
      ((h.quotient P).pullback (submoduleQuotientMap P T)
        (submoduleQuotientMap_injective P T)).fiber := by
    funext σ
    have hi : (((h.submodule T).quotient (P.comap T.subtype)).fiber σ).inner =
        (((h.quotient P).pullback (submoduleQuotientMap P T)
          (submoduleQuotientMap_injective P T)).fiber σ).inner := by
      funext x y
      change (h.fiber σ).inner
          (fiberMap T.subtype σ ((h.submodule T).fiberLift (P.comap T.subtype).mkQ
            (P.comap T.subtype).mkQ_surjective σ x))
          (fiberMap T.subtype σ ((h.submodule T).fiberLift (P.comap T.subtype).mkQ
            (P.comap T.subtype).mkQ_surjective σ y)) = _
      rw [h.fiberLift_submodule hPT, h.fiberLift_submodule hPT]
      rfl
    generalize hc : ((h.submodule T).quotient (P.comap T.subtype)).fiber σ = c at hi ⊢
    generalize hd : ((h.quotient P).pullback (submoduleQuotientMap P T)
      (submoduleQuotientMap_injective P T)).fiber σ = d at hi ⊢
    rcases c with ⟨⟨⟨ci⟩, cs, cp, ca, cm⟩, cd⟩
    rcases d with ⟨⟨⟨di⟩, ds, dp, da, dm⟩, dd⟩
    cases hi
    rfl
  generalize hc : (h.submodule T).quotient (P.comap T.subtype) = c at hf ⊢
  generalize hd : (h.quotient P).pullback (submoduleQuotientMap P T)
    (submoduleQuotientMap_injective P T) = d at hf ⊢
  cases c
  cases d
  cases hf
  rfl

/-- The same norm on an integral intermediate quotient, computed in either ambient module. -/
lemma sectionNorm_quotient_submodule (h : HermitianMetric (K := K) M)
    {P T : Submodule (𝓞 K) M} (hPT : P ≤ T) (σ : K →+* ℂ)
    (x : T ⧸ P.comap T.subtype) :
    ((h.submodule T).quotient (P.comap T.subtype)).sectionNorm σ x =
      (h.quotient P).sectionNorm σ (submoduleQuotientMap P T x) := by
  rw [h.quotient_submodule hPT, sectionNorm_pullback]

end HermitianMetric
end BostConjecture.Arithmetic
