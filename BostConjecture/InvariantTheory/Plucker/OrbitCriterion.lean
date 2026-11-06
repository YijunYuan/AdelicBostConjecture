/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.InvariantTheory.Plucker.Average
public import BostConjecture.InvariantTheory.Semistability

/-!
# The invariant-polynomial criterion for actual Plücker orbits

A separator of the orbit from zero is normalized, averaged over the proved
compact subgroup and decomposed into homogeneous components. Every step
uses intrinsic polynomials and the actual exterior tensor representation.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.InvariantTheory

open Module exteriorPower
open scoped TensorProduct

variable {ι κ U W : Type*} [Finite ι] [Finite κ]
  [AddCommGroup U] [Module ℂ U] [AddCommGroup W] [Module ℂ W]
  [LinearOrder (ι × κ)]

/-- Excluding zero from the actual orbit closure produces a nonvanishing
positive-degree invariant, with no assumed invariant-theoretic criterion. -/
theorem exists_homogeneousInvariant_of_plucker_semistable
    (bU : Basis ι ℂ U) (bW : Basis κ ℂ W) (i₀ : ι) (j₀ : κ) (s : ℕ)
    {x : ⋀[ℂ]^s (U ⊗[ℂ] W)}
    (hx : IsGeometricallySemistable (pluckerRepresentation ℂ U W s) x) :
    ∃ d : ℕ, 0 < d ∧ ∃ p : homogeneousInvariants (pluckerRepresentation ℂ U W s) d,
      polynomialEval x (p : SymmetricAlgebra ℂ (Dual ℂ (⋀[ℂ]^s (U ⊗[ℂ] W)))) ≠ 0 := by
  classical
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite κ
  let : FiniteDimensional ℂ U := bU.finiteDimensional_of_finite
  let : FiniteDimensional ℂ W := bW.finiteDimensional_of_finite
  change ¬ ∀ f : SymmetricAlgebra ℂ (Dual ℂ (⋀[ℂ]^s (U ⊗[ℂ] W))),
    (∀ y ∈ Set.range (fun g => pluckerRepresentation ℂ U W s g x), polynomialEval y f = 0) →
      polynomialEval (0 : ⋀[ℂ]^s (U ⊗[ℂ] W)) f = 0 at hx
  push Not at hx
  obtain ⟨f, hf, hf0⟩ := hx
  let c := polynomialEval (0 : ⋀[ℂ]^s (U ⊗[ℂ] W)) f
  let q := (1 : SymmetricAlgebra ℂ (Dual ℂ (⋀[ℂ]^s (U ⊗[ℂ] W)))) - c⁻¹ • f
  have hq0 : polynomialEval (0 : ⋀[ℂ]^s (U ⊗[ℂ] W)) q = 0 := by
    simp [q, c, hf0]
  have hqx (g) : polynomialEval (pluckerRepresentation ℂ U W s g x) q = 1 := by
    simp only [q, map_sub, map_one, map_smul, hf _ ⟨g, rfl⟩, smul_zero, sub_zero]
  obtain ⟨r, hr, he⟩ := exists_pluckerInvariant_average bU bW i₀ j₀ s q
  have hr0 : polynomialEval (0 : ⋀[ℂ]^s (U ⊗[ℂ] W)) r = 0 :=
    he 0 0 (by intro g; simpa only [map_zero] using hq0)
  have hrx : polynomialEval x r = 1 := he x 1 hqx
  exact exists_homogeneousInvariant_of_invariant (pluckerRepresentation ℂ U W s)
    hr hr0 (hrx.trans_ne one_ne_zero)

/-- The exact equivalence between orbit-closure and invariant-polynomial semistability. -/
theorem plucker_semistable_iff_exists_homogeneousInvariant
    (bU : Basis ι ℂ U) (bW : Basis κ ℂ W) (i₀ : ι) (j₀ : κ) (s : ℕ)
    (x : ⋀[ℂ]^s (U ⊗[ℂ] W)) :
    IsGeometricallySemistable (pluckerRepresentation ℂ U W s) x ↔
      ∃ d : ℕ, 0 < d ∧ ∃ p : homogeneousInvariants (pluckerRepresentation ℂ U W s) d,
        polynomialEval x (p : SymmetricAlgebra ℂ (Dual ℂ (⋀[ℂ]^s (U ⊗[ℂ] W)))) ≠ 0 := by
  constructor
  · exact exists_homogeneousInvariant_of_plucker_semistable bU bW i₀ j₀ s
  · rintro ⟨d, hd, p, hp⟩
    exact isGeometricallySemistable_of_homogeneousInvariant _ x (Nat.ne_of_gt hd) p.property hp

end BostConjecture.InvariantTheory
