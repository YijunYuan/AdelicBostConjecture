/-
Copyright (c) 2026 The openai/math contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The openai/math contributors
-/
/-
Adapted from openai/math, commit 4eaee87548250b2682affda7d05d947c05554bae.
Original path: lean/OAI/NumberTheory/ArithmeticGroups/Lattices/UniformShortSpan.lean
Released under Apache 2.0; see BostConjecture/ExternalCode/OAI/LICENSE.
Local changes: see CONTRIBUTIONS.md in the BostConjecture project root.
This file has been modified for Lean 4.35 module visibility.
-/
module

public import BostConjecture.ExternalCode.OAI.NumberTheory.ArithmeticGroups.Lattices.Minkowski.Ellipsoid
public import BostConjecture.ExternalCode.OAI.NumberTheory.ArithmeticGroups.Lattices.BoundedBasis

/-!
# Uniform Short Span

## Source

Adapted from <https://github.com/openai/math>, revision
`4eaee87548250b2682affda7d05d947c05554bae`.
Original source:
* `lean/OAI/NumberTheory/ArithmeticGroups/Lattices/UniformShortSpan.lean`.

The original declaration namespaces and license notices are retained, except for
project-specific adaptations documented in `CONTRIBUTIONS.md`.
-/

@[expose] public section

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.UniformShortSpan.Construction

noncomputable section

/-! Uniform spanning and basis bounds from an upper covolume bound and a
positive lower bound on nonzero lattice-vector lengths. -/

open Set _root_.Module _root_.MeasureTheory

theorem exists_uniform_ellipsoid_scale (n : ℕ) {a V C : ℝ}
    (ha : 0 < a) (hV : 0 < V) :
    ∃ B : ℝ, 1 ≤ B ∧ C * 2 ^ n < a ^ n * B * V := by
  classical
  let B := max 1 ((C * 2 ^ n + 1) / (a ^ n * V))
  have hB : (C * 2 ^ n + 1) / (a ^ n * V) ≤ B := le_max_right _ _
  have h := (div_le_iff₀ (mul_pos (pow_pos ha n) hV)).mp hB
  refine ⟨B, le_max_left _ _, ?_⟩
  nlinarith

theorem exists_uniform_short_spanning_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] (ε C : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ],
      ZLattice.covolume Λ μ ≤ C →
      (∀ x ∈ Λ, x ≠ 0 → ε ≤ ‖x‖) →
      Submodule.span ℝ {x : E | x ∈ Λ ∧ ‖x‖ ≤ R} = ⊤ := by
  classical
  let a := min ε 1
  have ha : 0 < a := lt_min hε zero_lt_one
  have ha1 : a ≤ 1 := min_le_right _ _
  let V := μ.real (Metric.ball (0 : E) 1)
  have hV : 0 < V := ENNReal.toReal_pos (Metric.measure_ball_pos μ 0 zero_lt_one).ne'
    measure_ball_ne_top
  have hVeq : ENNReal.ofReal V = μ (Metric.ball (0 : E) 1) :=
    ENNReal.ofReal_toReal measure_ball_ne_top
  obtain ⟨B, hB1, hB⟩ := exists_uniform_ellipsoid_scale (finrank ℝ E) (C := C) ha hV
  have hBpos : 0 < B := zero_lt_one.trans_le hB1
  refine ⟨a + B, add_pos ha hBpos, ?_⟩
  intro Λ _ _ hcov hgap
  let W := Submodule.span ℝ {x : E | x ∈ Λ ∧ ‖x‖ ≤ a + B}
  by_contra hW
  have hWdim : finrank ℝ W < finrank ℝ E := by
    simpa only [finrank_top] using
      Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr hW)
  have hp : 1 ≤ finrank ℝ Wᗮ := by
    have hd := W.finrank_add_finrank_orthogonal
    omega
  have haPow : a ^ finrank ℝ E ≤ a ^ finrank ℝ W :=
    pow_le_pow_of_le_one ha.le ha1 hWdim.le
  have hBPow : B ≤ B ^ finrank ℝ Wᗮ := by
    simpa only [pow_one] using pow_le_pow_right₀ hB1 hp
  have hdet : a ^ finrank ℝ E * B ≤ a ^ finrank ℝ W * B ^ finrank ℝ Wᗮ :=
    mul_le_mul haPow hBPow hBpos.le (pow_nonneg ha.le _)
  have hr : ZLattice.covolume Λ μ * 2 ^ finrank ℝ E <
      (a ^ finrank ℝ W * B ^ finrank ℝ Wᗮ) * V :=
    (mul_le_mul_of_nonneg_right hcov (by positivity)).trans_lt
      (hB.trans_le (mul_le_mul_of_nonneg_right hdet hV.le))
  have hvol : ENNReal.ofReal (ZLattice.covolume Λ μ) * 2 ^ finrank ℝ E <
      ENNReal.ofReal (a ^ finrank ℝ W * B ^ finrank ℝ Wᗮ) * μ (Metric.ball 0 1) := by
    have he := ENNReal.ofReal_lt_ofReal_iff
      (mul_pos (mul_pos (pow_pos ha _) (pow_pos hBpos _)) hV) |>.mpr hr
    simpa only [ENNReal.ofReal_mul (ZLattice.covolume_pos Λ μ).le,
      ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
      ENNReal.ofReal_mul (mul_nonneg (pow_nonneg ha.le _) (pow_nonneg hBpos.le _)),
      hVeq] using he
  obtain ⟨x, hxΛ, hxW, hxR⟩ :=
    Minkowski.Ellipsoid.Construction.minkowski_outside_subspace Λ μ W ha hBpos
    (min_le_left ε 1) hgap hvol
  exact hxW (Submodule.subset_span ⟨hxΛ, hxR⟩)

theorem exists_uniform_lattice_basis_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] (ε C : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ],
      ZLattice.covolume Λ μ ≤ C →
      (∀ x ∈ Λ, x ≠ 0 → ε ≤ ‖x‖) →
      ∃ b : Basis (Fin (finrank ℝ E)) ℤ Λ, ∀ i, ‖(b i).val‖ ≤ R := by
  classical
  obtain ⟨R, hR, hspan⟩ := exists_uniform_short_spanning_bound μ ε C hε
  refine ⟨finrank ℝ E * R, mul_nonneg (Nat.cast_nonneg _) hR.le, ?_⟩
  intro Λ _ _ hcov hgap
  exact BoundedBasis.Construction.bounded_spanning_lattice_basis
    (finrank ℝ E) Λ rfl R hR.le (hspan Λ hcov hgap)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.UniformShortSpan.Construction
