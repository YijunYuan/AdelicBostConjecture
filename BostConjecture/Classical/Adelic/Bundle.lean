/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.NumberTheory.NumberField.Model.GenericFibre.Invertible
public import BostConjecture.Classical.Adelic.Archimedean
public import ArakelovGeometry.AdelicVectorBundle.Construction.Countable
public import ArakelovGeometry.NumberTheory.NumberField.NormFamily.Normalization.Hermitian

/-!
# Adelization of the original Hermitian metric

The generic fibre contains the original module as a full integral lattice.
Its finite-place gauges and completed archimedean metrics form an adelic bundle.
-/

@[expose] public section
noncomputable section

section GenericLattice

open NumberField TensorProduct

namespace BostConjecture.Arithmetic

attribute [local instance 2000] ArakelovGeometry.integralVectorModule

variable {K : Type*} [Field K]
variable (M : Type*) [AddCommGroup M] [Module (𝓞 K) M]

/-- The image of the original integral module in its canonical generic fibre. -/
def genericLattice : Submodule (𝓞 K) (K ⊗[𝓞 K] M) :=
  (TensorProduct.mk (𝓞 K) K M 1).range

theorem genericLattice_fg [Module.Finite (𝓞 K) M] : (genericLattice (K := K) M).FG :=
  Submodule.fg_range _

theorem genericLattice_span :
    Submodule.span K (genericLattice (K := K) M : Set (K ⊗[𝓞 K] M)) = ⊤ :=
  ArakelovGeometry.NumberFieldInvertibleGeneric.genericImage_fullSpan M

/-- Projectivity identifies the original module with its actual image lattice. -/
def genericLatticeEquiv [Module.Projective (𝓞 K) M] : M ≃ₗ[𝓞 K] genericLattice (K := K) M :=
  LinearEquiv.ofInjective (TensorProduct.mk (𝓞 K) K M 1)
    (Module.Flat.tensorProduct_mk_injective (𝓞 K) M K)

end BostConjecture.Arithmetic

end GenericLattice

section Bundle

set_option backward.isDefEq.respectTransparency false

open NumberField TensorProduct
open ArakelovGeometry ArakelovGeometry.AdelicStructure

namespace BostConjecture.Arithmetic

attribute [local instance 2000] Algebra.toModule Algebra.toSMul

variable {K : Type*} [Field K] [NumberField K]

/-- The infinite place attached to a point in the Archimedean locus. -/
def classicalInfinitePlace (ω : (normalizedNumberFieldAdelicStructure K).Ω)
    (hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωinf) : InfinitePlace K :=
  (show ∃ w : InfinitePlace K, normalizedInfinitePlacePoint w = ω from
    by
      simpa only [normalizedNumberFieldAdelicStructure_Ωinf_eq_range,
        Set.mem_range] using hω).choose

theorem classicalInfinitePlace_point (ω : (normalizedNumberFieldAdelicStructure K).Ω)
    (hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωinf) :
    normalizedInfinitePlacePoint (classicalInfinitePlace ω hω) = ω :=
  (show ∃ w : InfinitePlace K, normalizedInfinitePlacePoint w = ω from
    by
      simpa only [normalizedNumberFieldAdelicStructure_Ωinf_eq_range,
        Set.mem_range] using hω).choose_spec

namespace HermitianMetric

variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]

/-- The classical Archimedean norm indexed by the actual adelic parameter. -/
def infiniteNormAt (h : HermitianMetric K M)
    (ω : (normalizedNumberFieldAdelicStructure K).Ω)
    (hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωinf) :
    Seminorm ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion
      (((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion ⊗[K] (K ⊗[𝓞 K] M)) :=
  cast (congrArg (fun ω : (normalizedNumberFieldAdelicStructure K).Ω =>
    Seminorm ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion
      (((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion ⊗[K] (K ⊗[𝓞 K] M)))
        (classicalInfinitePlace_point ω hω))
    (h.completedArchimedeanNorm (classicalInfinitePlace ω hω))

@[simp]
theorem infiniteNormAt_point (h : HermitianMetric K M) (w : InfinitePlace K)
    (hw : normalizedInfinitePlacePoint w ∈ (normalizedNumberFieldAdelicStructure K).Ωinf) :
    h.infiniteNormAt (normalizedInfinitePlacePoint w) hw = h.completedArchimedeanNorm w := by
  have transport (v : InfinitePlace K)
      (he : normalizedInfinitePlacePoint v = normalizedInfinitePlacePoint w) :
      cast (congrArg (fun ω : (normalizedNumberFieldAdelicStructure K).Ω =>
        Seminorm ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion
          (((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion ⊗[K] (K ⊗[𝓞 K] M)))
            he) (h.completedArchimedeanNorm v) = h.completedArchimedeanNorm w := by
    have hv := normalizedInfinitePlacePoint_injective he
    subst v
    rfl
  exact transport _ (classicalInfinitePlace_point _ hw)

theorem infiniteNormAt_eq_zero_iff (h : HermitianMetric K M)
    (ω : (normalizedNumberFieldAdelicStructure K).Ω)
    (hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωinf)
    (z : ((normalizedNumberFieldAdelicStructure K).ϕ ω).Completion ⊗[K] (K ⊗[𝓞 K] M)) :
    h.infiniteNormAt ω hω z = 0 ↔ z = 0 := by
  obtain ⟨w, rfl⟩ : ∃ w : InfinitePlace K, normalizedInfinitePlacePoint w = ω :=
    by
      simpa only [normalizedNumberFieldAdelicStructure_Ωinf_eq_range, Set.mem_range] using hω
  rw [infiniteNormAt_point]
  exact h.completedArchimedeanNorm_eq_zero_iff w z

variable [Module.Finite (𝓞 K) M]

open scoped Classical in
/-- A preliminary norm family, with the prescribed infinite metrics. -/
def archimedeanNormFamily (h : HermitianMetric K M) :
    NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M) where
  norm ω := if hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωinf
    then h.infiniteNormAt ω hω
    else (NormFamily.ofBasis (normalizedNumberFieldAdelicStructure K) _
      (Module.finBasis K (K ⊗[𝓞 K] M))).norm ω
  norm_eq_zero_iff ω z := by
    split
    · exact h.infiniteNormAt_eq_zero_iff ω _ z
    · exact (NormFamily.ofBasis _ _ _).norm_eq_zero_iff ω z

theorem archimedeanNormFamily_norm_infinite (h : HermitianMetric K M)
    (ω : (normalizedNumberFieldAdelicStructure K).Ω)
    (hω : ω ∈ (normalizedNumberFieldAdelicStructure K).Ωinf) :
    h.archimedeanNormFamily.norm ω = h.infiniteNormAt ω hω := by
  simp only [archimedeanNormFamily, dite_eq_left hω]

/-- The original integral module supplies the finite-place gauges. -/
def adelicNormFamily (h : HermitianMetric K M) :
    NormFamily (normalizedNumberFieldAdelicStructure K) (K ⊗[𝓞 K] M) :=
  NumberFieldFullLattice.fullLatticeGaugeFamily (genericLattice M)
    (genericLattice_fg M) (genericLattice_span M) h.archimedeanNormFamily

instance adelicNormFamily_isHermitian (h : HermitianMetric K M) :
    h.adelicNormFamily.IsHermitian := by
  apply NormFamily.isHermitian_iff_parallelogram.mpr
  refine ⟨NumberFieldFullLattice.fullLatticeGaugeFamily_isUltrametricAtFinitePlaces
    (genericLattice (K := K) M) (genericLattice_fg (K := K) M)
    (genericLattice_span (K := K) M) h.archimedeanNormFamily, ?_⟩
  intro ω hω x y
  obtain ⟨w, rfl⟩ : ∃ w : InfinitePlace K, normalizedInfinitePlacePoint w = ω :=
    by
      simpa only [normalizedNumberFieldAdelicStructure_Ωinf_eq_range, Set.mem_range] using hω
  have hn : h.adelicNormFamily.norm (normalizedInfinitePlacePoint w) =
      h.completedArchimedeanNorm w := by
    rw [adelicNormFamily, NumberFieldFullLattice.fullLatticeGaugeFamily_norm_not_finite
      _ _ _ _ _ hω, archimedeanNormFamily_norm_infinite _ _ hω, infiniteNormAt_point]
  simp only [hn]
  exact h.completedArchimedeanNorm_parallelogram w x y

/-- The actual adelic bundle associated to the original classical Hermitian metric. -/
abbrev toAdelicBundle (h : HermitianMetric K M) :
    AdelicVectorBundle (normalizedNumberFieldAdelicStructure K) := by
  have hd : h.adelicNormFamily.IsDominated :=
    (NumberFieldFullLattice.fullLatticeGaugeFamily_coherent_and_dominated
      (genericLattice (K := K) M) (genericLattice_fg (K := K) M)
      (genericLattice_span (K := K) M) h.archimedeanNormFamily).2
  exact AdelicVectorBundle.ofMeasurableDominated h.adelicNormFamily
    (hm := NormFamily.isMeasurable_of_discrete _) (hd := hd)

instance toAdelicBundle_isHermitian (h : HermitianMetric K M) :
    h.toAdelicBundle.IsHermitian := h.adelicNormFamily_isHermitian

/-- At an infinite point the actual adelic norm is the original completed metric. -/
theorem adelicNormFamily_norm_infinite_point (h : HermitianMetric K M)
    (w : InfinitePlace K) :
    h.adelicNormFamily.norm (normalizedInfinitePlacePoint w) =
      h.completedArchimedeanNorm w := by
  rw [adelicNormFamily, NumberFieldFullLattice.fullLatticeGaugeFamily_norm_not_finite
    _ _ _ _ _ (normalizedInfinitePlacePoint_mem_inf w),
    archimedeanNormFamily_norm_infinite _ _ (normalizedInfinitePlacePoint_mem_inf w),
    infiniteNormAt_point]

/-- All original integral section norms are preserved at infinity. -/
theorem toAdelicBundle_norm_section (h : HermitianMetric K M)
    (w : InfinitePlace K) (x : M) :
    h.toAdelicBundle.norm (normalizedInfinitePlacePoint w)
      (1 ⊗ₜ[K] ((1 : K) ⊗ₜ[𝓞 K] x)) = h.sectionNorm w.embedding x := by
  change h.adelicNormFamily.norm _ _ = _
  rw [adelicNormFamily_norm_infinite_point, completedArchimedeanNorm_section]

end HermitianMetric
end BostConjecture.Arithmetic

end Bundle
