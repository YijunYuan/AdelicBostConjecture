/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.RestrictionCovolume.RealForm
public import BostConjecture.Arithmetic.Submodule.QuotientMetric
public import Mathlib.Algebra.Exact.Basic

/-!
# Maps and orthogonal lifts on the actual trace spaces

Fiber maps and the canonical orthogonal quotient lifts preserve the
conjugation-compatible real forms. Their pairings give the induced and
quotient real trace metrics without any metric-comparison assumptions.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct
open scoped InnerProductSpace

namespace BostConjecture.Arithmetic.HermitianMetric

variable {K : Type*} [Field K] [NumberField K]
variable {M N : Type*} [AddCommGroup M] [Module (𝓞 K) M]
    [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
    [AddCommGroup N] [Module (𝓞 K) N]
    [Module.Finite (𝓞 K) N] [Module.Projective (𝓞 K) N]
variable (h : HermitianMetric K M) (g : HermitianMetric K N)

/-- The real trace map induced by an actual integral linear map. -/
def traceMap (f : M →ₗ[𝓞 K] N) : h.TraceSpace →ₗ[ℝ] g.TraceSpace where
  toFun x := ⟨fun σ => fiberMap f σ (h.traceInclusion x σ), by
    apply (g.mem_archimedeanSpan_iff_conjugate _).mpr
    intro σ
    rw [fiberConjugate_map, h.traceInclusion_conjugate]⟩
  map_add' x y := by
    apply Subtype.ext
    funext σ
    change fiberMap f σ (h.traceInclusion x σ + h.traceInclusion y σ) =
      fiberMap f σ (h.traceInclusion x σ) + fiberMap f σ (h.traceInclusion y σ)
    exact map_add _ _ _
  map_smul' r x := by
    apply Subtype.ext
    funext σ
    change fiberMap f σ ((r : ℂ) • h.traceInclusion x σ) =
      (r : ℂ) • fiberMap f σ (h.traceInclusion x σ)
    exact map_smul _ _ _

@[simp]
lemma traceMap_apply (f : M →ₗ[𝓞 K] N) (x : h.TraceSpace) (σ : K →+* ℂ) :
    g.traceInclusion (h.traceMap g f x) σ = fiberMap f σ (h.traceInclusion x σ) := rfl

@[simp]
lemma traceMap_section (f : M →ₗ[𝓞 K] N) (x : M) :
    h.traceMap g f (h.traceSection x) = g.traceSection (f x) := rfl

/-- The map of real trace spaces preserves integral injections. -/
lemma traceMap_injective (f : M →ₗ[𝓞 K] N) (hf : Function.Injective f) :
    Function.Injective (h.traceMap g f) := by
  intro x y he
  apply Subtype.ext
  funext σ
  apply fiberMap_injective f hf σ
  exact congrArg (fun z => g.traceInclusion z σ) he

/-- The actual quotient fiber lifts combine to a map of the constructed real trace spaces. -/
def traceLift (q : M →ₗ[𝓞 K] N) (hq : Function.Surjective q) :
    (h.pushforward q hq).TraceSpace →ₗ[ℝ] h.TraceSpace where
  toFun x := ⟨fun σ => h.fiberLift q hq σ ((h.pushforward q hq).traceInclusion x σ), by
    apply (h.mem_archimedeanSpan_iff_conjugate _).mpr
    intro σ
    rw [h.fiberLift_conjugate, (h.pushforward q hq).traceInclusion_conjugate]⟩
  map_add' x y := by
    apply Subtype.ext
    funext σ
    change h.fiberLift q hq σ ((h.pushforward q hq).traceInclusion x σ +
      (h.pushforward q hq).traceInclusion y σ) = _
    exact map_add _ _ _
  map_smul' r x := by
    apply Subtype.ext
    funext σ
    change h.fiberLift q hq σ ((r : ℂ) • (h.pushforward q hq).traceInclusion x σ) =
      (r : ℂ) • h.fiberLift q hq σ ((h.pushforward q hq).traceInclusion x σ)
    exact map_smul _ _ _

@[simp]
lemma traceLift_apply (q : M →ₗ[𝓞 K] N) (hq : Function.Surjective q)
    (x : (h.pushforward q hq).TraceSpace) (σ : K →+* ℂ) :
    h.traceInclusion (h.traceLift q hq x) σ =
      h.fiberLift q hq σ ((h.pushforward q hq).traceInclusion x σ) := rfl

/-- The real orthogonal lift is a right inverse to the actual trace quotient map. -/
@[simp]
lemma traceMap_traceLift (q : M →ₗ[𝓞 K] N) (hq : Function.Surjective q)
    (x : (h.pushforward q hq).TraceSpace) :
    h.traceMap (h.pushforward q hq) q (h.traceLift q hq x) = x := by
  apply Subtype.ext
  funext σ
  exact h.fiberMap_fiberLift q hq σ _

/-- The orthogonal real lift has precisely the actual quotient trace pairing. -/
lemma traceLift_inner (q : M →ₗ[𝓞 K] N) (hq : Function.Surjective q)
    (x y : (h.pushforward q hq).TraceSpace) :
    inner ℝ (h.traceLift q hq x) (h.traceLift q hq y) = inner ℝ x y := rfl

/-- The induced real trace map preserves the actual pullback pairing. -/
lemma traceMap_pullback_inner (i : N →ₗ[𝓞 K] M) (hi : Function.Injective i)
    (x y : (h.pullback i hi).TraceSpace) :
    inner ℝ ((h.pullback i hi).traceMap h i x) ((h.pullback i hi).traceMap h i y) =
      inner ℝ x y := rfl

/-- Orthogonal quotient lifts are perpendicular to the actual submodule trace image. -/
lemma traceLift_orthogonal (P : Submodule (𝓞 K) M)
    [Module.Projective (𝓞 K) (M ⧸ P)]
    (x : (h.submodule P).TraceSpace) (y : (h.quotient P).TraceSpace) :
    inner ℝ ((h.submodule P).traceMap h P.subtype x)
      (h.traceLift P.mkQ P.mkQ_surjective y) = 0 := by
  change (∑ σ, ((h.fiber σ).inner
    (fiberMap P.subtype σ ((h.submodule P).traceInclusion x σ))
    (h.fiberLift P.mkQ P.mkQ_surjective σ ((h.quotient P).traceInclusion y σ))).re) = 0
  apply Finset.sum_eq_zero
  intro σ _
  let : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
  let := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
  have hu : fiberMap P.subtype σ ((h.submodule P).traceInclusion x σ) ∈
      LinearMap.ker (fiberMap P.mkQ σ) := by
    rw [ker_fiberMap_mkQ]
    exact LinearMap.mem_range_self _ _
  have ho := (Submodule.mem_orthogonal _ _).mp
    (ComplexQuotient.lift_mem (fiberMap P.mkQ σ) (fiberMap_surjective P.mkQ P.mkQ_surjective σ)
      ((h.quotient P).traceInclusion y σ)) _ hu
  exact congrArg Complex.re ho

/-- Scalar restriction preserves the actual submodule kernel, with no dimension certificate. -/
lemma ker_traceMap_mkQ (P : Submodule (𝓞 K) M)
    [Module.Projective (𝓞 K) (M ⧸ P)] :
    LinearMap.ker (h.traceMap (h.quotient P) P.mkQ) =
      LinearMap.range ((h.submodule P).traceMap h P.subtype) := by
  ext x
  constructor
  · intro hx
    have hxσ (σ : K →+* ℂ) :
        fiberMap P.mkQ σ (h.traceInclusion x σ) = 0 := by
      have hh := congrArg (fun z => (h.quotient P).traceInclusion z σ) hx
      simpa only [traceMap_apply, map_zero, Pi.zero_apply] using hh
    have hx' (σ : K →+* ℂ) : ∃ v : ComplexFiber P σ,
        fiberMap P.subtype σ v = h.traceInclusion x σ := by
      apply LinearMap.mem_range.mp
      rw [← ker_fiberMap_mkQ]
      exact hxσ σ
    choose v hv using hx'
    have hc : ∀ σ, fiberConjugate P σ (v σ) = v (ComplexEmbedding.conjugate σ) := by
      intro σ
      apply fiberMap_injective P.subtype P.injective_subtype (ComplexEmbedding.conjugate σ)
      rw [← fiberConjugate_map, hv, h.traceInclusion_conjugate, hv]
    let y : (h.submodule P).TraceSpace :=
      ⟨v, ((h.submodule P).mem_archimedeanSpan_iff_conjugate v).mpr hc⟩
    refine ⟨y, ?_⟩
    apply Subtype.ext
    funext σ
    exact hv σ
  · rintro ⟨y, rfl⟩
    apply Subtype.ext
    funext σ
    have hx : fiberMap P.subtype σ ((h.submodule P).traceInclusion y σ) ∈
        LinearMap.ker (fiberMap P.mkQ σ) := by
      rw [ker_fiberMap_mkQ]
      exact LinearMap.mem_range_self _ _
    exact hx

/-- The actual saturated sequence remains exact on real trace spaces. -/
lemma trace_exact (P : Submodule (𝓞 K) M) [Module.Projective (𝓞 K) (M ⧸ P)] :
    Function.Exact ((h.submodule P).traceMap h P.subtype)
      (h.traceMap (h.quotient P) P.mkQ) := by
  intro x
  change x ∈ LinearMap.ker _ ↔ x ∈ LinearMap.range _
  rw [h.ker_traceMap_mkQ]

/-- The canonical orthogonal decomposition of the actual real trace space. -/
def traceSplitEquiv (P : Submodule (𝓞 K) M) [Module.Projective (𝓞 K) (M ⧸ P)] :
    ((h.submodule P).TraceSpace × (h.quotient P).TraceSpace) ≃ₗ[ℝ] h.TraceSpace :=
  ((h.trace_exact P).splitSurjectiveEquiv
    ((h.submodule P).traceMap_injective h P.subtype P.injective_subtype)
    ⟨h.traceLift P.mkQ P.mkQ_surjective, by ext x; exact h.traceMap_traceLift _ _ x⟩).1.symm

@[simp]
lemma traceSplitEquiv_apply (P : Submodule (𝓞 K) M) [Module.Projective (𝓞 K) (M ⧸ P)]
    (x : (h.submodule P).TraceSpace × (h.quotient P).TraceSpace) :
    h.traceSplitEquiv P x = (h.submodule P).traceMap h P.subtype x.1 +
      h.traceLift P.mkQ P.mkQ_surjective x.2 := rfl

/-- The second orthogonal coordinate is the actual quotient map. -/
lemma traceSplitEquiv_symm_snd (P : Submodule (𝓞 K) M)
    [Module.Projective (𝓞 K) (M ⧸ P)] (x : h.TraceSpace) :
    ((h.traceSplitEquiv P).symm x).2 = h.traceMap (h.quotient P) P.mkQ x :=
  (LinearMap.congr_fun ((h.trace_exact P).splitSurjectiveEquiv
    ((h.submodule P).traceMap_injective h P.subtype P.injective_subtype)
    ⟨h.traceLift P.mkQ P.mkQ_surjective, by ext y; exact h.traceMap_traceLift _ _ y⟩).2.2 x).symm

end BostConjecture.Arithmetic.HermitianMetric
