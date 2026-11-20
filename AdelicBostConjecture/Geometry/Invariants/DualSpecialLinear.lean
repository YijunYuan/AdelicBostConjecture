/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import AdelicBostConjecture.Geometry.Invariants.Rectangular

/-!
# Actual rectangular invariants for contragredient special-linear actions

The contragredient special-linear action has the rectangular Specht
invariants supplied by the determinant-twisted construction. These invariants
provide the dual factors in the canonical contraction.
-/

@[expose] public section

noncomputable section

namespace AdelicBostConjecture.Geometry

open Module PiTensorProduct
open scoped TensorProduct

variable {F E : Type*} [Field F] [AddCommGroup E] [Module F E]
  [FiniteDimensional F E]

/-- Every special-linear map of the dual is the transpose of one on the original space. -/
theorem specialLinear_dualMap_surjective :
    Function.Surjective (SpecialLinearGroup.dualMap (R := F) (V := E)) := by
  intro g
  let h := SpecialLinearGroup.congr_linearEquiv (evalEquiv F E).symm g.dualMap
  refine ⟨h, ?_⟩
  apply Subtype.ext
  apply LinearEquiv.ext
  intro ℓ
  apply LinearMap.ext
  intro x
  change ℓ (h x) = (g ℓ) x
  simp [h, SpecialLinearGroup.dualMap, LinearEquiv.dualMap]

/-- Transpose invariance under the original SL group is full SL invariance on the dual. -/
theorem dual_specialLinear_fixed_iff {n : ℕ} (w : ⨂[F] (_ : Fin n), Dual F E) :
    (∀ g : SpecialLinearGroup F E, map (fun _ => (g : E →ₗ[F] E).dualMap) w = w) ↔
    ∀ h : SpecialLinearGroup F (Dual F E),
      map (fun _ => (h : Dual F E →ₗ[F] Dual F E)) w = w := by
  constructor
  · intro hw h
    obtain ⟨g, rfl⟩ := specialLinear_dualMap_surjective h
    exact hw g
  · intro hw g
    exact hw g.dualMap

/-- The actual contragredient fixed subspace lies in the rectangular integral
lattice image on the dual, without assuming that image identification. -/
theorem mem_range_freeLatticeMap_of_dual_specialLinear_fixed [CharZero F] [IsAlgClosed F]
    {n a k : ℕ} (ha : 0 < a) (hk : 0 < k)
    (t : OAI.Saxl.Tableau n (Specht.rectangle a k)) (b : Basis (Fin a) F (Dual F E))
    (w : ⨂[F] (_ : Fin n), Dual F E)
    (hw : ∀ g : SpecialLinearGroup F E,
      map (fun _ => (g : E →ₗ[F] E).dualMap) w = w) :
    w ∈ LinearMap.range (freeLatticeMap hk t b) :=
  (mem_range_freeLatticeMap_iff_specialLinear_fixed ha hk t b w).mpr
    ((dual_specialLinear_fixed_iff w).mp hw)

end AdelicBostConjecture.Geometry
