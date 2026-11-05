module

public import Mathlib.LinearAlgebra.Trace

/-!
# Partial traces of tensor endomorphisms

The contraction of one endomorphism factor by its trace defines the actual
partial trace, independently of bases. The trace pairing identities are the
algebraic input to the balanced-projection variation formula.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Balanced

open scoped TensorProduct

variable (R U W : Type*) [CommRing R]
  [AddCommGroup U] [Module R U] [Module.Free R U] [Module.Finite R U]
  [AddCommGroup W] [Module R W] [Module.Free R W] [Module.Finite R W]

/-- Trace out the right tensor factor. -/
def partialTraceRight : Module.End R (U ⊗[R] W) →ₗ[R] Module.End R U :=
  (TensorProduct.rid R (Module.End R U)).toLinearMap ∘ₗ
    TensorProduct.map LinearMap.id (LinearMap.trace R W) ∘ₗ
      (homTensorHomEquiv R U W U W).symm.toLinearMap

/-- Trace out the left tensor factor. -/
def partialTraceLeft : Module.End R (U ⊗[R] W) →ₗ[R] Module.End R W :=
  (TensorProduct.lid R (Module.End R W)).toLinearMap ∘ₗ
    TensorProduct.map (LinearMap.trace R U) LinearMap.id ∘ₗ
      (homTensorHomEquiv R U W U W).symm.toLinearMap

variable {R U W}

@[simp]
theorem partialTraceRight_map (A : Module.End R U) (B : Module.End R W) :
    partialTraceRight R U W (TensorProduct.map A B) = LinearMap.trace R W B • A := by
  have h : TensorProduct.map A B = homTensorHomEquiv R U W U W (A ⊗ₜ[R] B) := rfl
  rw [h]
  simp only [partialTraceRight, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, TensorProduct.map_tmul, LinearMap.id_apply,
    TensorProduct.rid_tmul]

@[simp]
theorem partialTraceLeft_map (A : Module.End R U) (B : Module.End R W) :
    partialTraceLeft R U W (TensorProduct.map A B) = LinearMap.trace R U A • B := by
  have h : TensorProduct.map A B = homTensorHomEquiv R U W U W (A ⊗ₜ[R] B) := rfl
  rw [h]
  simp only [partialTraceLeft, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, TensorProduct.map_tmul, LinearMap.id_apply,
    TensorProduct.lid_tmul]

/-- The defining trace-pairing identity for the right partial trace. -/
theorem trace_partialTraceRight_comp (P : Module.End R (U ⊗[R] W))
    (H : Module.End R U) :
    LinearMap.trace R U ((partialTraceRight R U W P).comp H) =
      LinearMap.trace R (U ⊗[R] W) (P.comp (TensorProduct.map H LinearMap.id)) := by
  obtain ⟨p, rfl⟩ := (homTensorHomEquiv R U W U W).surjective P
  induction p using TensorProduct.inductionOn with
  | tmul A B =>
    change LinearMap.trace R U ((partialTraceRight R U W (TensorProduct.map A B)).comp H) = _
    rw [partialTraceRight_map]
    change _ = LinearMap.trace R (U ⊗[R] W)
      ((TensorProduct.map A B).comp (TensorProduct.map H LinearMap.id))
    rw [← TensorProduct.map_comp, LinearMap.comp_id, LinearMap.trace_tensorProduct']
    simp [LinearMap.smul_comp, mul_comm]
  | add p q hp hq => simp_all [LinearMap.add_comp]

/-- The defining trace-pairing identity for the left partial trace. -/
theorem trace_partialTraceLeft_comp (P : Module.End R (U ⊗[R] W))
    (J : Module.End R W) :
    LinearMap.trace R W ((partialTraceLeft R U W P).comp J) =
      LinearMap.trace R (U ⊗[R] W) (P.comp (TensorProduct.map LinearMap.id J)) := by
  obtain ⟨p, rfl⟩ := (homTensorHomEquiv R U W U W).surjective P
  induction p using TensorProduct.inductionOn with
  | tmul A B =>
    change LinearMap.trace R W ((partialTraceLeft R U W (TensorProduct.map A B)).comp J) = _
    rw [partialTraceLeft_map]
    change _ = LinearMap.trace R (U ⊗[R] W)
      ((TensorProduct.map A B).comp (TensorProduct.map LinearMap.id J))
    rw [← TensorProduct.map_comp, LinearMap.comp_id, LinearMap.trace_tensorProduct']
    simp [LinearMap.smul_comp]
  | add p q hp hq => simp_all [LinearMap.add_comp]

/-- Scalar partial traces give the infinitesimal trace formula. -/
theorem trace_comp_tensorSum_of_partialTrace_eq_smul
    (P : Module.End R (U ⊗[R] W)) (H : Module.End R U) (J : Module.End R W)
    (a b : R) (hU : partialTraceRight R U W P = a • LinearMap.id)
    (hW : partialTraceLeft R U W P = b • LinearMap.id) :
    LinearMap.trace R (U ⊗[R] W)
      (P.comp (TensorProduct.map H LinearMap.id + TensorProduct.map LinearMap.id J)) =
      a * LinearMap.trace R U H + b * LinearMap.trace R W J := by
  rw [LinearMap.comp_add, map_add, ← trace_partialTraceRight_comp,
    ← trace_partialTraceLeft_comp, hU, hW]
  simp [LinearMap.smul_comp]

/-- Balanced partial traces annihilate every pair of traceless infinitesimal generators. -/
theorem trace_comp_tensorSum_eq_zero
    (P : Module.End R (U ⊗[R] W)) (H : Module.End R U) (J : Module.End R W)
    (a b : R) (hU : partialTraceRight R U W P = a • LinearMap.id)
    (hW : partialTraceLeft R U W P = b • LinearMap.id)
    (hH : LinearMap.trace R U H = 0) (hJ : LinearMap.trace R W J = 0) :
    LinearMap.trace R (U ⊗[R] W)
      (P.comp (TensorProduct.map H LinearMap.id + TensorProduct.map LinearMap.id J)) = 0 := by
  rw [trace_comp_tensorSum_of_partialTrace_eq_smul P H J a b hU hW, hH, hJ]
  simp

end BostConjecture.Balanced
