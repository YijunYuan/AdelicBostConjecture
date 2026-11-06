/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.InvariantTheory.Polynomial.Average
public import BostConjecture.InvariantTheory.SpecialLinear.SpecialUnitaryAction
public import BostConjecture.InvariantTheory.Polynomial.InvariantDetection

/-!
# Invariant polynomial averaging for the Plücker representation

Special-unitary coordinate detection extends the fixed polynomial obtained
by the actual compact-group Haar integral to the full special-linear action.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.InvariantTheory

open Module exteriorPower MeasureTheory
open scoped TensorProduct

variable {ι κ E : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  [AddCommGroup E] [Module ℂ E]

/-- Compact pairs detect tensor-valued regular coefficients. -/
theorem polynomialCoefficientEval_detects_of_unitary (i₀ : ι) (j₀ : κ)
    {z : SpecialLinearPairCoordinateRing ℂ ι κ ⊗[ℂ] SymmetricAlgebra ℂ (Dual ℂ E)}
    (hz : ∀ g : Matrix.SpecialLinearGroup ι ℂ × Matrix.SpecialLinearGroup κ ℂ,
      (g.1 : Matrix ι ι ℂ) ∈ Matrix.unitaryGroup ι ℂ →
      (g.2 : Matrix κ κ ℂ) ∈ Matrix.unitaryGroup κ ℂ →
      polynomialCoefficientEval (specialLinearPairEval g) z = 0) : z = 0 := by
  classical
  let b := Module.Free.chooseBasis ℂ (SymmetricAlgebra ℂ (Dual ℂ E))
  apply (TensorProduct.equivFinsuppOfBasisRight b).injective
  ext i
  simp only [map_zero, Finsupp.zero_apply]
  apply specialLinearPairEval_detects_of_unitary i₀ j₀
  intro g hg hh
  rw [polynomialCoefficientEval_coord, hz g hg hh, map_zero]

variable {U W : Type*} [AddCommGroup U] [Module ℂ U] [AddCommGroup W] [Module ℂ W]
  [LinearOrder (ι × κ)]

/-- An actual compact-subgroup invariant of the Plücker action is an SL invariant. -/
theorem plucker_invariant_of_specialUnitary
    (bU : Basis ι ℂ U) (bW : Basis κ ℂ W) (i₀ : ι) (j₀ : κ) (s : ℕ)
    {p : SymmetricAlgebra ℂ (Dual ℂ (⋀[ℂ]^s (U ⊗[ℂ] W)))}
    (hp : p ∈ (polynomialRepresentation (specialUnitaryPluckerRepresentation bU bW s)).invariants) :
    p ∈ (polynomialRepresentation (pluckerRepresentation ℂ U W s)).invariants := by
  have he : pluckerCoordinatePullback bU bW s p =
      (1 : SpecialLinearPairCoordinateRing ℂ ι κ) ⊗ₜ[ℂ] p := by
    apply sub_eq_zero.mp
    apply polynomialCoefficientEval_detects_of_unitary i₀ j₀
    intro g hg hh
    let u : Matrix.specialUnitaryGroup ι ℂ := ⟨g.1, hg, g.1.property⟩
    let v : Matrix.specialUnitaryGroup κ ℂ := ⟨g.2, hh, g.2.property⟩
    let k := (u, v)
    have hi : polynomialPullback
        (pluckerRepresentation ℂ U W s (specialUnitaryPluckerGroupHom bU bW k)) p = p := by
      simpa only [polynomialRepresentation_apply, specialUnitaryPluckerRepresentation,
        inv_inv, MonoidHom.comp_apply] using hp k⁻¹
    have hev : specialLinearPairEval g =
        pluckerGroupEval bU bW (specialUnitaryPluckerGroupHom bU bW k) := by
      simp [pluckerGroupEval, specialLinearMatrix, specialUnitaryPluckerGroupHom,
        specialUnitaryToSpecialLinear, k, u, v]
      rfl
    rw [hev, map_sub, polynomialCoefficientEval_pluckerCoordinatePullback, hi]
    simp
  intro g
  change polynomialPullback (pluckerRepresentation ℂ U W s g⁻¹) p = p
  have h := congrArg (polynomialCoefficientEval (pluckerGroupEval bU bW g⁻¹)) he
  simpa only [polynomialCoefficientEval_pluckerCoordinatePullback,
    polynomialCoefficientEval_tmul, map_one, one_smul] using h

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
/-- Concrete polynomial averaging over the compact subgroup, with SL-invariant output. -/
theorem exists_pluckerInvariant_average [Finite ι] [Finite κ]
    (bU : Basis ι ℂ U) (bW : Basis κ ℂ W) (i₀ : ι) (j₀ : κ) (s : ℕ)
    (q : SymmetricAlgebra ℂ (Dual ℂ (⋀[ℂ]^s (U ⊗[ℂ] W)))) :
    ∃ r : SymmetricAlgebra ℂ (Dual ℂ (⋀[ℂ]^s (U ⊗[ℂ] W))),
      r ∈ (polynomialRepresentation (pluckerRepresentation ℂ U W s)).invariants ∧
      ∀ x c, (∀ g, polynomialEval (pluckerRepresentation ℂ U W s g x) q = c) →
        polynomialEval x r = c := by
  classical
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite κ
  let : Nonempty ι := ⟨i₀⟩
  let : Nonempty κ := ⟨j₀⟩
  let : FiniteDimensional ℂ U := bU.finiteDimensional_of_finite
  let : FiniteDimensional ℂ W := bW.finiteDimensional_of_finite
  let H := Matrix.specialUnitaryGroup ι ℂ × Matrix.specialUnitaryGroup κ ℂ
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  obtain ⟨μ, hμ, hμl⟩ := exists_probability_leftInvariant_measure H
  let := hμ
  let := hμl
  obtain ⟨r, hr, he⟩ := exists_compactInvariant_polynomial μ
    (specialUnitaryPluckerRepresentation bU bW s)
    (continuous_specialUnitaryPlucker_dual bU bW s) q
  refine ⟨r, plucker_invariant_of_specialUnitary bU bW i₀ j₀ s hr, ?_⟩
  intro x c hc
  rw [he x]
  have hf (h : H) : polynomialEval (specialUnitaryPluckerRepresentation bU bW s h⁻¹ x) q = c :=
    hc (specialUnitaryPluckerGroupHom bU bW h⁻¹)
  simp_rw [hf]
  simp

end BostConjecture.InvariantTheory
