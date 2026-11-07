/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.HN.QuotientSemistable
public import BostConjecture.Arithmetic.Bundle.Scaling

/-!
# Normalized semistable extensions

Zero-degree semistability is equivalent to nonpositivity of all induced
degrees. Exact degree and the sum/intersection inequality prove extension
closure and semistability of the two pieces cut out by a degree-zero
submodule. All modules are finite projective over the full ring of integers.

Reference: this paper, Proposition 7.3, pages 12–13.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace BostConjecture.Arithmetic.HermitianMetric

variable {K : Type*} [Field K] [NumberField K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]
variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]

/-- At degree zero, semistability bounds every induced degree, including rank zero. -/
theorem isSemistable_iff_degree_nonpos (h : HermitianMetric K M)
    (h0 : h.degree = 0) :
    h.IsSemistable ↔ ∀ P : Submodule (𝓞 K) M, (h.submodule P).degree ≤ 0 := by
  constructor
  · intro hs P
    by_cases hr : Module.finrank K (K ⊗[𝓞 K] P) = 0
    · exact ((h.submodule P).degree_eq_zero_of_rank_zero hr).le
    · have hp : (0 : ℝ) < Module.finrank K (K ⊗[𝓞 K] P) := by
        exact_mod_cast Nat.pos_of_ne_zero hr
      have hb := hs P (Nat.pos_of_ne_zero hr)
      simpa only [slope, h0, zero_div, div_le_iff₀ hp, zero_mul] using hb
  · intro hs P hP
    simp only [slope, h0, zero_div]
    exact div_nonpos_of_nonpos_of_nonneg (hs P) (Nat.cast_nonneg _)

/-- Uniform rescaling preserves actual semistability in positive rank. -/
theorem isSemistable_rescale_iff (h : HermitianMetric K M)
    (hr : Module.finrank K (K ⊗[𝓞 K] M) ≠ 0) (t : ℝ) :
    (h.rescale t).IsSemistable ↔ h.IsSemistable := by
  simp only [IsSemistable, slope_rescale h hr]
  refine forall_congr' fun P => forall_congr' fun hP => ?_
  rw [slope_submodule_rescale h P (Nat.ne_of_gt hP), sub_le_sub_iff_right]

/-- Rescaling by the slope gives degree zero, for any generic rank. -/
theorem degree_rescale_self (h : HermitianMetric K M) :
    (h.rescale h.slope).degree = 0 := by
  by_cases hr : Module.finrank K (K ⊗[𝓞 K] M) = 0
  · rw [degree_rescale, hr, Nat.cast_zero, zero_mul, sub_zero]
    exact h.degree_eq_zero_of_rank_zero hr
  · rw [degree_rescale, slope, mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hr), sub_self]

/-- The degree of the actual quotient is the difference of the two degrees. -/
theorem degree_quotient (h : HermitianMetric K M)
    (P : Submodule (𝓞 K) M) [Module.Projective (𝓞 K) (M ⧸ P)] :
    (h.quotient P).degree = h.degree - (h.submodule P).degree := by
  simpa only [degree_submodule_top, Submodule.comap_top] using
    h.degree_quotient_submodule P ⊤

/-- A degree-zero submodule of a normalized semistable bundle is semistable. -/
theorem IsSemistable.submodule_of_degree_zero {h : HermitianMetric K M}
    (hs : h.IsSemistable) (h0 : h.degree = 0)
    (P : Submodule (𝓞 K) M) (hP0 : (h.submodule P).degree = 0) :
    (h.submodule P).IsSemistable := by
  apply ((h.submodule P).isSemistable_iff_degree_nonpos hP0).mpr
  intro S
  rw [degree_submodule_map]
  exact (h.isSemistable_iff_degree_nonpos h0).mp hs _

/-- The quotient by a degree-zero saturated submodule is normalized semistable. -/
theorem IsSemistable.quotient_of_degree_zero {h : HermitianMetric K M}
    (hs : h.IsSemistable) (h0 : h.degree = 0)
    (P : Submodule (𝓞 K) M) [Module.Projective (𝓞 K) (M ⧸ P)]
    (hP0 : (h.submodule P).degree = 0) :
    (h.quotient P).degree = 0 ∧ (h.quotient P).IsSemistable := by
  have hQ0 : (h.quotient P).degree = 0 := by rw [degree_quotient, h0, hP0, sub_zero]
  refine ⟨hQ0, ((h.quotient P).isSemistable_iff_degree_nonpos hQ0).mpr ?_⟩
  intro S
  rw [degree_quotient_submodule, hP0, sub_zero]
  exact (h.isSemistable_iff_degree_nonpos h0).mp hs _

/-- Extensions of normalized semistable bundles are normalized semistable,
with the actual induced and quotient metrics. -/
theorem isSemistable_of_submodule_quotient (h : HermitianMetric K M)
    (P : Submodule (𝓞 K) M) [Module.IsTorsionFree (𝓞 K) (M ⧸ P)]
    (hP : (h.submodule P).IsSemistable) (hP0 : (h.submodule P).degree = 0)
    (hQ : (h.quotient P).IsSemistable) (hQ0 : (h.quotient P).degree = 0) :
    h.degree = 0 ∧ h.IsSemistable := by
  let : Module.FinitePresentation (𝓞 K) (M ⧸ P) :=
    Module.finitePresentation_of_finite (𝓞 K) _
  let : Module.Projective (𝓞 K) (M ⧸ P) :=
    Module.Flat.projective_of_finitePresentation
  have h0 : h.degree = 0 := by
    rw [degree_quotient, hP0, sub_zero] at hQ0
    exact hQ0
  refine ⟨h0, (h.isSemistable_iff_degree_nonpos h0).mpr ?_⟩
  intro S
  have hB := ((h.submodule P).isSemistable_iff_degree_nonpos hP0).mp hP
    (S.comap P.subtype)
  rw [degree_submodule_map] at hB
  have hBeq := congrArg (fun T : Submodule (𝓞 K) M => (h.submodule T).degree)
    ((Submodule.map_comap_subtype P S).trans (inf_comm P S))
  rw [hBeq] at hB
  have hI := ((h.quotient P).isSemistable_iff_degree_nonpos hQ0).mp hQ
    (S.map P.mkQ)
  rw [degree_quotient_submodule, hP0, sub_zero] at hI
  have hIe : (S.map P.mkQ).comap P.mkQ = S ⊔ P := by
    rw [Submodule.comap_map_eq, Submodule.ker_mkQ]
  have hIeq := congrArg (fun T : Submodule (𝓞 K) M => (h.submodule T).degree) hIe
  rw [hIeq] at hI
  have hi := h.degree_submodule_sup S P
  rw [hP0, add_zero] at hi
  linarith

end BostConjecture.Arithmetic.HermitianMetric
