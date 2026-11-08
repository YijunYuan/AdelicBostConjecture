/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Bundle.RestrictionOfScalars
public import BostConjecture.Arithmetic.Degree.ArchimedeanFiniteness
public import Mathlib.Algebra.Module.ZLattice.Basic

/-!
# The real trace space of a Hermitian module

The real span of the simultaneous archimedean sections carries the sum of
the real parts of the given Hermitian pairings over all complex embeddings.
Bounded-section finiteness makes the actual integral image discrete. Its
integer basis then extends to a real basis, identifying this space with
`ℝ ⊗[ℤ] M` without a freeness assumption over the ring of integers.

Reference: this paper, page 11.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace BostConjecture.Arithmetic

variable {K : Type*} [Field K] [NumberField K]
variable (M : Type*) [AddCommGroup M] [Module (𝓞 K) M]

/-- The simultaneous archimedean embedding of integral sections. -/
def archimedeanSection : M →ₗ[ℤ] ((σ : K →+* ℂ) → ComplexFiber M σ) where
  toFun x σ := fiberSection M σ x
  map_add' x y := by ext σ; simp [fiberSection, tmul_add]
  map_smul' n x := by ext σ; simp [fiberSection, tmul_smul]

/-- The real span of the actual integral archimedean image. -/
def archimedeanSpan : Submodule ℝ ((σ : K →+* ℂ) → ComplexFiber M σ) :=
  Submodule.span ℝ (Set.range (archimedeanSection (K := K) M))

namespace HermitianMetric

variable {M} (h : HermitianMetric K M)

/-- The real trace space, with its metric supplied by `h`. -/
def TraceSpace (_h : HermitianMetric K M) : Type _ :=
  archimedeanSpan (K := K) M

instance : AddCommGroup h.TraceSpace :=
  inferInstanceAs (AddCommGroup (archimedeanSpan (K := K) M))

instance : Module ℝ h.TraceSpace :=
  inferInstanceAs (Module ℝ (archimedeanSpan (K := K) M))

/-- Inclusion in the product of all complex fibers. -/
def traceInclusion : h.TraceSpace →ₗ[ℝ] ((σ : K →+* ℂ) → ComplexFiber M σ) :=
  (archimedeanSpan (K := K) M).subtype

/-- The trace pairing counts every complex embedding once. -/
@[instance_reducible]
def traceCore : InnerProductSpace.Core ℝ h.TraceSpace where
  inner x y := ∑ σ : K →+* ℂ, ((h.fiber σ).inner
    (h.traceInclusion x σ) (h.traceInclusion y σ)).re
  conj_inner_symm x y := by
    simp only [RCLike.conj_to_real]
    apply Finset.sum_congr rfl
    intro σ _
    simpa only [Complex.conj_re] using
      congrArg Complex.re ((h.fiber σ).conj_inner_symm (h.traceInclusion x σ)
        (h.traceInclusion y σ))
  re_inner_nonneg x := Finset.sum_nonneg fun σ _ => (h.fiber σ).re_inner_nonneg _
  add_left x y z := by
    simp only [map_add, Pi.add_apply, (h.fiber _).add_left, Complex.add_re, Finset.sum_add_distrib]
  smul_left x y r := by
    simp only [map_smul, Pi.smul_apply]
    have hs (σ : K →+* ℂ) :
        ((h.fiber σ).inner (r • h.traceInclusion x σ) (h.traceInclusion y σ)).re =
          r * ((h.fiber σ).inner (h.traceInclusion x σ) (h.traceInclusion y σ)).re := by
      change ((h.fiber σ).inner ((r : ℂ) • h.traceInclusion x σ)
        (h.traceInclusion y σ)).re = _
      rw [(h.fiber σ).smul_left]
      simp
    simp only [hs, Finset.mul_sum, RCLike.conj_to_real]
  definite x hx := by
    apply Subtype.ext
    funext σ
    have hz : ((h.fiber σ).inner (h.traceInclusion x σ) (h.traceInclusion x σ)).re = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun τ _ => (h.fiber τ).re_inner_nonneg _)).mp hx σ
        (Finset.mem_univ σ)
    apply (h.fiber σ).definite
    apply Complex.ext hz
    let := h.fiber σ
    exact InnerProductSpace.Core.inner_self_im (𝕜 := ℂ) _

instance : NormedAddCommGroup h.TraceSpace :=
  letI := h.traceCore
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)

instance : InnerProductSpace ℝ h.TraceSpace :=
  letI := h.traceCore
  InnerProductSpace.ofCore h.traceCore.toCore

/-- The actual integral section in the real trace space. -/
def traceSection : M →ₗ[ℤ] h.TraceSpace where
  toFun x := ⟨archimedeanSection (K := K) M x, Submodule.subset_span ⟨x, rfl⟩⟩
  map_add' x y := Subtype.ext ((archimedeanSection (K := K) M).map_add x y)
  map_smul' n x := Subtype.ext ((archimedeanSection (K := K) M).map_smul n x)

omit [NumberField K] in
@[simp]
lemma traceInclusion_section (x : M) (σ : K →+* ℂ) :
    h.traceInclusion (h.traceSection x) σ = fiberSection M σ x := rfl

/-- The squared trace norm of an integral section is the sum of its squared
Hermitian norms over all embeddings. -/
theorem traceSection_norm_sq (x : M) :
    ‖h.traceSection x‖ ^ 2 = ∑ σ : K →+* ℂ, h.sectionNorm σ x ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℝ)]
  change (∑ σ : K →+* ℂ, ((h.fiber σ).inner (fiberSection M σ x)
    (fiberSection M σ x)).re) = _
  apply Finset.sum_congr rfl
  exact fun σ _ => (Real.sq_sqrt ((h.fiber σ).re_inner_nonneg _)).symm

/-- Each fiber section norm is bounded by the trace norm. -/
lemma sectionNorm_le_traceSection_norm (σ : K →+* ℂ) (x : M) :
    h.sectionNorm σ x ≤ ‖h.traceSection x‖ := by
  have hs : h.sectionNorm σ x ^ 2 ≤ ‖h.traceSection x‖ ^ 2 := by
    rw [h.traceSection_norm_sq]
    exact Finset.single_le_sum (fun τ _ => sq_nonneg (h.sectionNorm τ x))
      (Finset.mem_univ σ)
  nlinarith [norm_nonneg (h.traceSection x)]

variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]

instance : FiniteDimensional ℝ h.TraceSpace := by
  let : ∀ σ : K →+* ℂ, Module.Finite ℂ (ComplexFiber M σ) := fun σ => by
    dsimp [ComplexFiber]
    infer_instance
  let : ∀ σ : K →+* ℂ, Module.Finite ℝ (ComplexFiber M σ) := fun σ =>
    Module.Finite.trans ℂ (ComplexFiber M σ)
  exact Module.Finite.of_injective h.traceInclusion (Submodule.injective_subtype _)

omit [Module.Finite (𝓞 K) M] in
/-- No nonzero integral section vanishes in the real trace space. -/
lemma traceSection_injective : Function.Injective h.traceSection := by
  intro x y hxy
  let σ : K →+* ℂ := Classical.choice inferInstance
  apply fiberSection_injective M σ
  exact congrArg (fun z => h.traceInclusion z σ) hxy

/-- The integer lattice is the actual image of the integral module. -/
def traceLattice : Submodule ℤ h.TraceSpace := LinearMap.range h.traceSection

/-- The integral module identifies with its image in the real trace space. -/
def traceLatticeEquiv : M ≃ₗ[ℤ] h.traceLattice :=
  LinearEquiv.ofInjective h.traceSection h.traceSection_injective

/-- A bounded ball contains only finitely many actual integral lattice points. -/
lemma finite_traceLattice_ball (r : ℝ) :
    {x : h.traceLattice | ‖(x : h.TraceSpace)‖ < r}.Finite := by
  have hf := h.finite_bounded_sections (fun _ => r)
  apply (hf.image h.traceLatticeEquiv).subset
  intro x hx
  obtain ⟨m, rfl⟩ := h.traceLatticeEquiv.surjective x
  refine ⟨m, ?_, rfl⟩
  exact fun σ => (h.sectionNorm_le_traceSection_norm σ m).trans (le_of_lt hx)

instance traceLattice_discreteTopology : DiscreteTopology h.traceLattice := by
  apply discreteTopology_iff_isOpen_singleton_zero.mpr
  apply isOpen_singleton_of_finite_mem_nhds (0 : h.traceLattice)
    (Metric.ball_mem_nhds _ zero_lt_one)
  simpa only [Metric.ball, dist_zero_right, Submodule.norm_coe] using h.finite_traceLattice_ball 1

instance traceLattice_isZLattice : IsZLattice ℝ h.traceLattice where
  span_top := by
    apply (Submodule.map_injective_of_injective
      (show Function.Injective h.traceInclusion from Subtype.val_injective)).eq_iff.mp
    rw [Submodule.map_span, Submodule.map_top]
    have hr : h.traceInclusion.range = archimedeanSpan (K := K) M :=
      Submodule.range_subtype _
    rw [hr]
    change Submodule.span ℝ (h.traceInclusion '' (h.traceLattice : Set h.TraceSpace)) =
      Submodule.span ℝ (Set.range (archimedeanSection (K := K) M))
    congr 1
    ext x
    constructor
    · rintro ⟨y, ⟨m, rfl⟩, rfl⟩
      exact ⟨m, rfl⟩
    · rintro ⟨m, rfl⟩
      exact ⟨h.traceSection m, ⟨m, rfl⟩, rfl⟩

/-- The canonical real scalar extension of the simultaneous section map. -/
def realTensorMap : ℝ ⊗[ℤ] M →ₗ[ℝ] h.TraceSpace := h.traceSection.liftBaseChange ℝ

/-- Discreteness and fullness prove that the actual scalar-extension map is
bijective; no integral basis over the ring of integers is assumed. -/
lemma realTensorMap_bijective : Function.Bijective h.realTensorMap := by
  let := finite_int (K := K) (M := M)
  let := free_int (K := K) (M := M)
  let b := Module.Free.chooseBasis ℤ M
  constructor
  · apply (LinearMap.liftBaseChange_injective_iff h.traceSection b).mpr
    convert ((b.map h.traceLatticeEquiv).ofZLatticeBasis ℝ h.traceLattice).linearIndependent
      using 1
    funext i
    simp only [Module.Basis.ofZLatticeBasis_apply, Module.Basis.map_apply,
      Function.comp_apply]
    rfl
  · apply LinearMap.range_eq_top.mp
    rw [realTensorMap, LinearMap.range_liftBaseChange]
    exact IsZLattice.span_top (L := h.traceLattice)

/-- The canonical real tensor product is the constructed trace space. -/
def realTensorEquiv : ℝ ⊗[ℤ] M ≃ₗ[ℝ] h.TraceSpace :=
  LinearEquiv.ofBijective h.realTensorMap h.realTensorMap_bijective

@[simp]
lemma realTensorEquiv_tmul (r : ℝ) (x : M) :
    h.realTensorEquiv (r ⊗ₜ[ℤ] x) = r • h.traceSection x := rfl

/-- The trace space has the correct restriction-of-scalars dimension. -/
theorem traceSpace_finrank :
    Module.finrank ℝ h.TraceSpace =
      Module.finrank ℚ K * Module.finrank K (K ⊗[𝓞 K] M) := by
  rw [← ZLattice.rank ℝ h.traceLattice, ← h.traceLatticeEquiv.finrank_eq,
    finrank_int (K := K)]

/-- An integer basis extends to a real basis of the actual trace space. -/
def traceBasis {ι : Type*} (b : Module.Basis ι ℤ M) : Module.Basis ι ℝ h.TraceSpace :=
  (b.map h.traceLatticeEquiv).ofZLatticeBasis ℝ h.traceLattice

@[simp]
lemma traceBasis_apply {ι : Type*} (b : Module.Basis ι ℤ M) (i : ι) :
    h.traceBasis b i = h.traceSection (b i) := by
  simp only [traceBasis, Module.Basis.ofZLatticeBasis_apply, Module.Basis.map_apply]
  rfl

end HermitianMetric
end BostConjecture.Arithmetic
