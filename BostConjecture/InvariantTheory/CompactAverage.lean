module

public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Compact averaging in a finite-dimensional complex representation

Integration against probability Haar measure projects a continuous compact
orbit to the invariant subspace and preserves every linear observation
constant on that orbit. This is the finite-dimensional analytic ingredient
of polynomial averaging; the special-linear extension requires density.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.InvariantTheory

open MeasureTheory

variable {H V : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [CompactSpace H] [MeasurableSpace H] [BorelSpace H]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

variable (μ : Measure H) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]

/-- The actual vector-valued Haar integral of a representation orbit. -/
def compactRepresentationAverage (ρ : Representation ℂ H V) (v : V) : V :=
  ∫ h, ρ h v ∂μ

omit [IsTopologicalGroup H] [FiniteDimensional ℂ V] [μ.IsMulLeftInvariant] in
theorem integrable_representation_orbit (ρ : Representation ℂ H V) (v : V)
    (hc : Continuous fun h => ρ h v) : Integrable (fun h => ρ h v) μ :=
  hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Left invariance of Haar measure makes the vector average invariant. -/
theorem compactRepresentationAverage_mem_invariants (ρ : Representation ℂ H V) (v : V)
    (hc : Continuous fun h => ρ h v) :
    compactRepresentationAverage μ ρ v ∈ ρ.invariants := by
  let := FiniteDimensional.complete ℂ V
  intro g
  change ρ g (∫ h, ρ h v ∂μ) = ∫ h, ρ h v ∂μ
  have hi := integrable_representation_orbit μ ρ v hc
  calc
    _ = ∫ h, ρ g (ρ h v) ∂μ :=
      ((ρ g).toContinuousLinearMap.integral_comp_comm hi).symm
    _ = ∫ h, ρ (g * h) v ∂μ := by
      congr 1
      funext h
      exact (ρ.map_mul g h |> congrArg (fun f => f v)).symm
    _ = _ := integral_mul_left_eq_self (fun h => ρ h v) g

omit [IsTopologicalGroup H] [μ.IsMulLeftInvariant] in
/-- Linear observation commutes with the average. -/
theorem linearMap_compactRepresentationAverage (ρ : Representation ℂ H V) (v : V)
    (hc : Continuous fun h => ρ h v) (ℓ : Module.Dual ℂ V) :
    ℓ (compactRepresentationAverage μ ρ v) = ∫ h, ℓ (ρ h v) ∂μ := by
  let := FiniteDimensional.complete ℂ V
  exact (ℓ.toContinuousLinearMap.integral_comp_comm
    (integrable_representation_orbit μ ρ v hc)).symm

omit [IsTopologicalGroup H] [μ.IsMulLeftInvariant] in
/-- A constant orbit observation retains its value after averaging. -/
theorem linearMap_compactRepresentationAverage_of_constant
    (ρ : Representation ℂ H V) (v : V) (hc : Continuous fun h => ρ h v)
    (ℓ : Module.Dual ℂ V) (c : ℂ) (hℓ : ∀ h, ℓ (ρ h v) = c) :
    ℓ (compactRepresentationAverage μ ρ v) = c := by
  rw [linearMap_compactRepresentationAverage μ ρ v hc ℓ]
  simp_rw [hℓ]
  simp

omit [IsTopologicalGroup H] [CompactSpace H] [BorelSpace H]
  [TopologicalSpace H] [μ.IsMulLeftInvariant] in
/-- Averaging fixes every already invariant vector. -/
theorem compactRepresentationAverage_of_mem_invariants (ρ : Representation ℂ H V)
    {v : V} (hv : v ∈ ρ.invariants) : compactRepresentationAverage μ ρ v = v := by
  let := NormedSpace.restrictScalars ℝ ℂ V
  let := FiniteDimensional.complete ℂ V
  have hv' (h : H) : ρ h v = v := hv h
  simp [compactRepresentationAverage, hv']

/-- A compact group has a probability left Haar measure, normalized on the whole group. -/
theorem exists_probability_leftInvariant_measure (H : Type*) [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
    [MeasurableSpace H] [BorelSpace H] :
    ∃ μ : Measure H, IsProbabilityMeasure μ ∧ μ.IsMulLeftInvariant := by
  let D : TopologicalSpace.PositiveCompacts H :=
    ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩
  refine ⟨Measure.haarMeasure D, ?_, inferInstance⟩
  exact ⟨Measure.haarMeasure_self (K₀ := D)⟩

end BostConjecture.InvariantTheory
