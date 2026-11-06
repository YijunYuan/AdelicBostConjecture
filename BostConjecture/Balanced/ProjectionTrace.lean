/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Analysis.InnerProductSpace.Trace
public import BostConjecture.Balanced.PartialTrace
public import Mathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# The trace of an actual orthogonal projection

Compressing an endomorphism to a subspace computes its trace against the
orthogonal projection. This connects the intrinsic partial traces with the
orthonormal-frame sum occurring in the Gram determinant derivative.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Balanced

open scoped InnerProductSpace TensorProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- The ambient projection trace equals the trace of the compressed operator. -/
theorem trace_starProjection_comp (S : Submodule ℂ E) (A : Module.End ℂ E) :
    LinearMap.trace ℂ E (S.starProjection.toLinearMap.comp A) =
      LinearMap.trace ℂ S (S.orthogonalProjectionOnto.toLinearMap.comp (A.comp S.subtype)) := by
  change LinearMap.trace ℂ E
    ((S.subtype.comp S.orthogonalProjectionOnto.toLinearMap).comp A) = _
  rw [LinearMap.comp_assoc, LinearMap.trace_comp_comm']
  rfl

/-- The trace against the projection is the sum over an orthonormal basis of the subspace. -/
theorem trace_starProjection_comp_eq_sum {ι : Type*} [Fintype ι]
    (S : Submodule ℂ E) (v : OrthonormalBasis ι ℂ S) (A : Module.End ℂ E) :
    LinearMap.trace ℂ E (S.starProjection.toLinearMap.comp A) =
      ∑ i, inner ℂ (v i : E) (A (v i : E)) := by
  rw [trace_starProjection_comp, LinearMap.trace_eq_sum_inner _ v]
  apply Finset.sum_congr rfl
  intro i _
  exact S.inner_orthogonalProjectionOnto_eq_of_mem_left (v i) (A (v i : E))

variable {U W : Type*} [NormedAddCommGroup U] [InnerProductSpace ℂ U]
  [FiniteDimensional ℂ U] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [FiniteDimensional ℂ W]

/-- The balanced equations concern the actual orthogonal projection
on the Hilbert tensor product. -/
def IsBalanced (S : Submodule ℂ (U ⊗[ℂ] W)) : Prop :=
  partialTraceRight ℂ U W S.starProjection.toLinearMap =
      ((Module.finrank ℂ S : ℂ) / Module.finrank ℂ U) • LinearMap.id ∧
    partialTraceLeft ℂ U W S.starProjection.toLinearMap =
      ((Module.finrank ℂ S : ℂ) / Module.finrank ℂ W) • LinearMap.id

/-- Balance annihilates the frame sum for the tensor infinitesimal action. -/
theorem IsBalanced.sum_inner_tensorSum_eq_zero
    {S : Submodule ℂ (U ⊗[ℂ] W)} (hS : IsBalanced S)
    {ι : Type*} [Fintype ι] (v : OrthonormalBasis ι ℂ S)
    (H : Module.End ℂ U) (J : Module.End ℂ W)
    (hH : LinearMap.trace ℂ U H = 0) (hJ : LinearMap.trace ℂ W J = 0) :
    ∑ i, inner ℂ (v i : U ⊗[ℂ] W)
      ((TensorProduct.map H LinearMap.id + TensorProduct.map LinearMap.id J :
          Module.End ℂ (U ⊗[ℂ] W))
        (v i : U ⊗[ℂ] W)) = 0 := by
  rw [← trace_starProjection_comp_eq_sum S v]
  exact trace_comp_tensorSum_eq_zero S.starProjection.toLinearMap H J _ _ hS.1 hS.2 hH hJ

end BostConjecture.Balanced
