module

public import BostConjecture.Main.TensorSemistability.ArithmeticTensorFiber

/-! # Compatible traceless defects of actual arithmetic partial traces -/

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace BostConjecture.Arithmetic.HermitianMetric

universe u
variable {K : Type*} [Field K] [NumberField K]
variable {M N : Type u} [AddCommGroup M] [Module (𝓞 K) M]
    [AddCommGroup N] [Module (𝓞 K) N]
    [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
    [Module.Finite (𝓞 K) N] [Module.Projective (𝓞 K) N]

/-- The traceless scalar defect in the first factor. -/
def tensorRightDefect (h : HermitianMetric (K := K) M)
    (k : HermitianMetric (K := K) N) (P : Submodule (𝓞 K) (M ⊗[𝓞 K] N))
    (σ : K →+* ℂ) : Module.End ℂ (ComplexFiber M σ) :=
  h.tensorPartialTraceRight k P σ -
    (((Module.finrank K (K ⊗[𝓞 K] P) : ℝ) / Module.finrank K (K ⊗[𝓞 K] M) : ℝ) : ℂ) •
      LinearMap.id

/-- The traceless scalar defect in the second factor. -/
def tensorLeftDefect (h : HermitianMetric (K := K) M)
    (k : HermitianMetric (K := K) N) (P : Submodule (𝓞 K) (M ⊗[𝓞 K] N))
    (σ : K →+* ℂ) : Module.End ℂ (ComplexFiber N σ) :=
  h.tensorPartialTraceLeft k P σ -
    (((Module.finrank K (K ⊗[𝓞 K] P) : ℝ) / Module.finrank K (K ⊗[𝓞 K] N) : ℝ) : ℂ) •
      LinearMap.id

/-- The actual right defect is self-adjoint for its factor metric. -/
theorem tensorRightDefect_symmetric (h : HermitianMetric (K := K) M)
    (k : HermitianMetric (K := K) N) (P : Submodule (𝓞 K) (M ⊗[𝓞 K] N))
    (σ : K →+* ℂ) (x y : ComplexFiber M σ) :
    (h.fiber σ).inner (h.tensorRightDefect k P σ x) y =
      (h.fiber σ).inner x (h.tensorRightDefect k P σ y) := by
  let : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
  let := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
  let : InnerProductSpace.Core ℂ (ComplexFiber N σ) := k.fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber N σ)
  let := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber N σ))
  exact Balanced.isSymmetric_sub_real_smul_id _
    (Balanced.isSymmetric_partialTraceRight _ (tensorSubmoduleFiber P σ).starProjection_isSymmetric)
    _ x y

/-- The full trace of the actual right partial trace is the generic submodule rank. -/
theorem trace_tensorPartialTraceRight (h : HermitianMetric (K := K) M)
    (k : HermitianMetric (K := K) N) (P : Submodule (𝓞 K) (M ⊗[𝓞 K] N))
    (σ : K →+* ℂ) : LinearMap.trace ℂ (ComplexFiber M σ)
      (h.tensorPartialTraceRight k P σ) = (Module.finrank K (K ⊗[𝓞 K] P) : ℂ) := by
  let : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
  let := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
  let : InnerProductSpace.Core ℂ (ComplexFiber N σ) := k.fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber N σ)
  let := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber N σ))
  change LinearMap.trace ℂ (ComplexFiber M σ)
    (Balanced.partialTraceRight ℂ _ _ (tensorSubmoduleFiber P σ).starProjection.toLinearMap) = _
  rw [Balanced.trace_partialTraceRight, Balanced.trace_starProjection, finrank_tensorSubmoduleFiber]

/-- The actual right defect is traceless for a positive-rank factor. -/
theorem trace_tensorRightDefect (h : HermitianMetric (K := K) M)
    (k : HermitianMetric (K := K) N) (P : Submodule (𝓞 K) (M ⊗[𝓞 K] N))
    (hr : 0 < Module.finrank K (K ⊗[𝓞 K] M)) (σ : K →+* ℂ) :
    LinearMap.trace ℂ (ComplexFiber M σ) (h.tensorRightDefect k P σ) = 0 := by
  simp only [tensorRightDefect, map_sub, map_smul, LinearMap.trace_id]
  rw [trace_tensorPartialTraceRight, complexFiber_finrank]
  apply sub_eq_zero.mpr
  push_cast
  exact (div_mul_cancel₀ _ (by exact_mod_cast hr.ne')).symm

/-- The actual right scalar-defect family respects canonical conjugation. -/
theorem tensorRightDefect_conjugate (h : HermitianMetric (K := K) M)
    (k : HermitianMetric (K := K) N) (P : Submodule (𝓞 K) (M ⊗[𝓞 K] N))
    (σ : K →+* ℂ) (x : ComplexFiber M σ) :
    h.tensorRightDefect k P (ComplexEmbedding.conjugate σ) (fiberConjugate M σ x) =
      fiberConjugate M σ (h.tensorRightDefect k P σ x) := by
  simp only [tensorRightDefect, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    map_sub, map_smulₛₗ, tensorPartialTraceRight_conjugate, Complex.conj_ofReal]

/-- The actual left defect is self-adjoint for its factor metric. -/
theorem tensorLeftDefect_symmetric (h : HermitianMetric (K := K) M)
    (k : HermitianMetric (K := K) N) (P : Submodule (𝓞 K) (M ⊗[𝓞 K] N))
    (σ : K →+* ℂ) (x y : ComplexFiber N σ) :
    (k.fiber σ).inner (h.tensorLeftDefect k P σ x) y =
      (k.fiber σ).inner x (h.tensorLeftDefect k P σ y) := by
  let : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
  let := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
  let : InnerProductSpace.Core ℂ (ComplexFiber N σ) := k.fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber N σ)
  let := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber N σ))
  exact Balanced.isSymmetric_sub_real_smul_id _
    (Balanced.isSymmetric_partialTraceLeft _ (tensorSubmoduleFiber P σ).starProjection_isSymmetric)
    _ x y

/-- The full trace of the actual left partial trace is the generic submodule rank. -/
theorem trace_tensorPartialTraceLeft (h : HermitianMetric (K := K) M)
    (k : HermitianMetric (K := K) N) (P : Submodule (𝓞 K) (M ⊗[𝓞 K] N))
    (σ : K →+* ℂ) : LinearMap.trace ℂ (ComplexFiber N σ)
      (h.tensorPartialTraceLeft k P σ) = (Module.finrank K (K ⊗[𝓞 K] P) : ℂ) := by
  let : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
  let := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
  let : InnerProductSpace.Core ℂ (ComplexFiber N σ) := k.fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber N σ)
  let := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber N σ))
  change LinearMap.trace ℂ (ComplexFiber N σ)
    (Balanced.partialTraceLeft ℂ _ _ (tensorSubmoduleFiber P σ).starProjection.toLinearMap) = _
  rw [Balanced.trace_partialTraceLeft, Balanced.trace_starProjection, finrank_tensorSubmoduleFiber]

/-- The actual left defect is traceless for a positive-rank factor. -/
theorem trace_tensorLeftDefect (h : HermitianMetric (K := K) M)
    (k : HermitianMetric (K := K) N) (P : Submodule (𝓞 K) (M ⊗[𝓞 K] N))
    (hr : 0 < Module.finrank K (K ⊗[𝓞 K] N)) (σ : K →+* ℂ) :
    LinearMap.trace ℂ (ComplexFiber N σ) (h.tensorLeftDefect k P σ) = 0 := by
  simp only [tensorLeftDefect, map_sub, map_smul, LinearMap.trace_id]
  rw [trace_tensorPartialTraceLeft, complexFiber_finrank]
  apply sub_eq_zero.mpr
  push_cast
  exact (div_mul_cancel₀ _ (by exact_mod_cast hr.ne')).symm

/-- The actual left scalar-defect family respects canonical conjugation. -/
theorem tensorLeftDefect_conjugate (h : HermitianMetric (K := K) M)
    (k : HermitianMetric (K := K) N) (P : Submodule (𝓞 K) (M ⊗[𝓞 K] N))
    (σ : K →+* ℂ) (x : ComplexFiber N σ) :
    h.tensorLeftDefect k P (ComplexEmbedding.conjugate σ) (fiberConjugate N σ x) =
      fiberConjugate N σ (h.tensorLeftDefect k P σ x) := by
  simp only [tensorLeftDefect, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    map_sub, map_smulₛₗ, tensorPartialTraceLeft_conjugate, Complex.conj_ofReal]

/-- Actual arithmetic tensor projection traces split into the two partial-trace pairings. -/
theorem fiberProjectionTrace_tensor_eq (h : HermitianMetric (K := K) M)
    (k : HermitianMetric (K := K) N) (P : Submodule (𝓞 K) (M ⊗[𝓞 K] N))
    (A : ∀ σ : K →+* ℂ, Module.End ℂ (ComplexFiber M σ))
    (B : ∀ σ : K →+* ℂ, Module.End ℂ (ComplexFiber N σ)) (σ : K →+* ℂ) :
    (h.tensor k).fiberProjectionTrace P σ (tensorFiberGenerator A B σ) =
      (LinearMap.trace ℂ (ComplexFiber M σ) ((h.tensorPartialTraceRight k P σ).comp (A σ))).re +
      (LinearMap.trace ℂ (ComplexFiber N σ) ((h.tensorPartialTraceLeft k P σ).comp (B σ))).re := by
  rw [tensorFiberGenerator, fiberProjectionTrace_tensor_transport]
  simp only [LinearMap.comp_add, map_add, Complex.add_re,
    ← Balanced.trace_partialTraceRight_comp, ← Balanced.trace_partialTraceLeft_comp,
    tensorPartialTraceRight, tensorPartialTraceLeft]

end BostConjecture.Arithmetic.HermitianMetric
