/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.RestrictionCovolume.Covolume

/-!
# Finite-index change of the actual trace covolume

An equal-rank integral submodule is embedded into the original trace space.
The induced fiber metrics give the same Gram matrix in this common space.
Mathlib's lattice index formula therefore computes the ratio of the actual
Euclidean covolumes as the cardinality of the original integral quotient.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct MeasureTheory

namespace BostConjecture.Arithmetic.HermitianMetric

variable {K : Type*} [Field K] [NumberField K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]
variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
variable (h : HermitianMetric (K := K) M) (P : Submodule (𝓞 K) M)

/-- The actual image of an integral submodule in the ambient trace space. -/
def submoduleTraceLattice : Submodule ℤ h.TraceSpace :=
  (P.restrictScalars ℤ).map h.traceSection

omit [NumberField K] [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M] in
lemma submoduleTraceLattice_le : h.submoduleTraceLattice P ≤ h.traceLattice := by
  rintro x ⟨m, _, hm⟩
  exact ⟨m, hm⟩

/-- The integral submodule is identified with its actual ambient image. -/
def submoduleTraceLatticeEquiv : P ≃ₗ[ℤ] h.submoduleTraceLattice P :=
  Submodule.equivMapOfInjective h.traceSection h.traceSection_injective (P.restrictScalars ℤ)

instance submoduleTraceLattice_discreteTopology : DiscreteTopology (h.submoduleTraceLattice P) := by
  let f := Submodule.inclusion (h.submoduleTraceLattice_le P)
  have hi : Isometry f := fun _ _ => rfl
  exact DiscreteTopology.of_continuous_injective hi.continuous hi.injective

/-- Equal generic rank makes the actual submodule image a full lattice. -/
lemma submoduleTraceLattice_isZLattice
    (hr : Module.finrank K (K ⊗[𝓞 K] P) = Module.finrank K (K ⊗[𝓞 K] M)) :
    IsZLattice ℝ (h.submoduleTraceLattice P) := by
  constructor
  apply Submodule.eq_top_of_finrank_eq
  have hd : DiscreteTopology (Submodule.span ℤ (h.submoduleTraceLattice P : Set h.TraceSpace)) := by
    rw [(h.submoduleTraceLattice P).span_eq]
    infer_instance
  have he := Real.finrank_eq_int_finrank_of_discrete hd
  calc
    Module.finrank ℝ (Submodule.span ℝ (h.submoduleTraceLattice P : Set h.TraceSpace)) =
        Module.finrank ℤ (h.submoduleTraceLattice P) := by
      change Module.finrank ℝ (Submodule.span ℝ (h.submoduleTraceLattice P : Set h.TraceSpace)) =
        Module.finrank ℤ (Submodule.span ℤ (h.submoduleTraceLattice P : Set h.TraceSpace)) at he
      rwa [(h.submoduleTraceLattice P).span_eq] at he
    _ = Module.finrank ℤ P := (h.submoduleTraceLatticeEquiv P).finrank_eq.symm
    _ = Module.finrank ℝ h.TraceSpace := by
      rw [finrank_int (K := K), hr, h.traceSpace_finrank]

/-- The induced trace metric on a submodule gives the same covolume as its
actual image in the ambient trace space. -/
lemma traceCovolume_submodule_eq
    (hr : Module.finrank K (K ⊗[𝓞 K] P) = Module.finrank K (K ⊗[𝓞 K] M)) :
    (h.submodule P).traceCovolume = ZLattice.covolume (h.submoduleTraceLattice P) := by
  let := h.submoduleTraceLattice_isZLattice P hr
  let := finite_int (K := K) (M := P)
  let := free_int (K := K) (M := P)
  let b := Module.finBasis ℤ P
  apply (sq_eq_sq₀ (le_of_lt (h.submodule P).traceCovolume_pos)
    (le_of_lt (ZLattice.covolume_pos (h.submoduleTraceLattice P) volume))).mp
  rw [(h.submodule P).traceCovolume_sq_eq_det b,
    ZLattice.covolume_sq_eq_det_gram _ (b.map (h.submoduleTraceLatticeEquiv P))]
  congr 1

omit [Module.Finite (𝓞 K) M] in
/-- The subgroup index in the trace lattice is the original integral quotient cardinality. -/
lemma submoduleTraceLattice_relIndex :
    (h.submoduleTraceLattice P).toAddSubgroup.relIndex h.traceLattice.toAddSubgroup =
      Nat.card (M ⧸ P) := by
  have ht : h.traceLattice.toAddSubgroup =
      (⊤ : AddSubgroup M).map h.traceSection.toAddMonoidHom := by
    simp only [AddSubgroup.map_top]
    rfl
  rw [ht]
  change (P.toAddSubgroup.map h.traceSection.toAddMonoidHom).relIndex
    ((⊤ : AddSubgroup M).map h.traceSection.toAddMonoidHom) = _
  rw [AddSubgroup.relIndex_map_map_of_injective _ _ h.traceSection_injective,
    AddSubgroup.relIndex_top_right, AddSubgroup.index_eq_card]
  rfl

/-- The exact finite-index formula for the actual trace-metric Haar covolumes. -/
theorem traceCovolume_submodule
    (hr : Module.finrank K (K ⊗[𝓞 K] P) = Module.finrank K (K ⊗[𝓞 K] M)) :
    (h.submodule P).traceCovolume = (Nat.card (M ⧸ P) : ℝ) * h.traceCovolume := by
  let := h.submoduleTraceLattice_isZLattice P hr
  have hi := ZLattice.covolume_div_covolume_eq_relIndex'
    (h.submoduleTraceLattice P) h.traceLattice (h.submoduleTraceLattice_le P)
  rw [← h.traceCovolume_submodule_eq P hr, h.submoduleTraceLattice_relIndex P] at hi
  exact (div_eq_iff (ne_of_gt h.traceCovolume_pos)).mp hi

end BostConjecture.Arithmetic.HermitianMetric
