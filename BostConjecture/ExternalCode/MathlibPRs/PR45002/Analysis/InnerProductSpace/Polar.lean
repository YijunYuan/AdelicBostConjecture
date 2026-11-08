/-
Copyright (c) 2026 Tjeerd Jan Heeringa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tjeerd Jan Heeringa
-/

/-
Modified for BostConjecture: local Abs import and range-closure documentation corrected.
Source and changes: BostConjecture/ExternalCode/MathlibPRs/PR45002/PROVENANCE.json
-/
module

public import BostConjecture.ExternalCode.MathlibPRs.PR45002.Analysis.InnerProductSpace.Abs
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Polar decomposition

This file defines the polar decomposition for a continuous linear map `T : E →L[ℂ] F`
between (potentially distinct) Hilbert spaces `E` and `F`.

## Main definitions
 - `ContinuousLinearMap.polarₚₗᵢ` the linear isometry from the closure of `|T|.range`
   onto the closure of `T.range` such that `T = U ∘ |T|`.
 - `ContinuousLinearMap.polar` the partial linear isometry `U : E →L[ℂ] F` for a continuous
   linear map `T : E →L[ℂ] F` gotten by extending the map `ContinuousLinearMap.polarₚₗᵢ` by zero.

## Source

Adapted from <https://github.com/TJHeeringa/mathlib4>, revision
`41260205df493c627e1ac0e54812cfdeb6517fbc`.
Original source:
* `Mathlib/Analysis/InnerProductSpace/Polar.lean`.

The original declaration namespaces and license notices are retained, except for
project-specific adaptations documented in `CONTRIBUTIONS.md`.
-/

public noncomputable section

namespace ContinuousLinearMap

open scoped ENNReal InnerProductSpace

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

section Polar

@[inherit_doc]
local notation "|" T "|" => abs T

/-- The polar `U` is a linear isometry from the closure of the range of `|T|`
onto the closure of the range of `T : E →L[ℂ] F`, such that `T = U ∘ |T|`. -/
def polarₚₗᵢ (T : E →L[ℂ] F) : |T|.range.topologicalClosure →ₗᵢ[ℂ] F :=
  LinearMap.extendOfIsometry
    ((Submodule.liftQ _ T (le_of_eq_of_le T.ker_abs_eq fun ⦃x⦄ a ↦ a))
      ∘ₗ (|T|.quotKerEquivRange).symm.toLinearMap)
    (e := Submodule.inclusion |T|.range.le_topologicalClosure)
    (by
      erw [denseRange_inclusion_iff (by
        simpa [← SetLike.coe_subset_coe] using |T|.range.le_topologicalClosure)]
      simp)
    (by
      rintro ⟨_, x, rfl⟩
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      erw [|T|.quotKerEquivRange_symm_apply_image x]
      simp [norm_abs_apply])

theorem polarₚₗᵢ_apply (T : E →L[ℂ] F) (x : E) :
    T.polarₚₗᵢ ⟨|T| x, |T|.range.le_topologicalClosure ⟨x, rfl⟩⟩ = T x := by
  change T.polarₚₗᵢ (Submodule.inclusion |T|.range.le_topologicalClosure ⟨|T| x, ⟨x, rfl⟩⟩) = _
  simp only [polarₚₗᵢ]
  erw [LinearMap.extendOfIsometry_eq, LinearMap.comp_apply,
    |T|.quotKerEquivRange_symm_apply_image x]
  simp

/-- The polar `U : E →L[ℂ] F` is the partial linear isometry of `T` such that
`T = U ∘ |T|`. It is isometric on the closure of the range of `|T|`, maps that subspace
onto the closure of the range of `T`, and vanishes on its orthogonal complement. -/
def polar (T : E →L[ℂ] F) : E →L[ℂ] F :=
  T.polarₚₗᵢ.toContinuousLinearMap ∘L |T|.range.topologicalClosure.orthogonalProjectionOnto

theorem polar_comp_abs (T : E →L[ℂ] F) : T.polar ∘L |T| = T := by
  ext x
  simp only [polar, ContinuousLinearMap.comp_apply]
  nth_rw 4 [← polarₚₗᵢ_apply]
  simp only [LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.map_eq_iff]
  exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self
    ⟨|T| x, |T|.range.le_topologicalClosure (by simp)⟩

end Polar

end ContinuousLinearMap
