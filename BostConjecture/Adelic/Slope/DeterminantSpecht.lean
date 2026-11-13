/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Adelic.Slope.DeterminantPower
public import BostConjecture.Adelic.Specht.Degree
public import BostConjecture.Adelic.Semistability.Specht
public import BostConjecture.Adelic.Semistability.LineTensor
public import BostConjecture.Adelic.Specht.Permutation
public import ArakelovGeometry.AdelicVectorBundle.Slope.Tensor

/-!
# The actual determinant–Specht auxiliary bundle

This is the auxiliary bundle of Lemma 6.1 of this paper, on the source module
of the canonical determinant map. The lattice metric is the existing adelic
Specht metric, including its word Gram norm at infinity.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace BostConjecture.Adelic

open ArakelovGeometry ArakelovGeometry.AdelicVectorBundle Specht Module

universe u v

variable {K : Type u} [Field K] [CharZero K] {S : AdelicStructure.{u, v} K}
  (V : AdelicVectorBundle S)
  [hN : S.IsArchimedeanNormalized]
  [hcount : S.HasCommonCountableDenseSubfield]
  (k : ℕ) {n : ℕ} (t : OAI.Saxl.Tableau n (rectangle (finrank K V) k))
  (b : Basis (Fin (finrank K (K ⊗[ℤ] orbitLattice t))) ℤ (orbitLattice t))

/-- The determinant tensor power tensored with the actual adelic Specht lattice,
on exactly the source of `Geometry.projectiveDeterminantMap`. -/
abbrev determinantSpechtBundle :
    AdelicVectorBundle S where
  carrier := (⨂[K] (_ : Fin k), ⋀[K]^(finrank K V) V) ⊗[K] (K ⊗[ℤ] orbitLattice t)
  instAddCommGroup := inferInstance
  instModule := inferInstance
  instFiniteDimensional := inferInstance
  toNormFamily := ((determinantPower V k) ⊗ʰ (latticeBundle S t b)).toNormFamily
  toIsAdelic := ((determinantPower V k) ⊗ʰ (latticeBundle S t b)).toIsAdelic

instance determinantSpechtBundle_isHermitian :
    (determinantSpechtBundle V k t b).IsHermitian :=
  orthogonalTensorPair_isHermitian (determinantPower V k) (latticeBundle S t b)

variable [S.IsProper]

/-- The actual auxiliary bundle and its actual dual are semistable, without
any semistability assumption on the original bundle. -/
theorem determinantSpechtBundle_isMeanSlopeSemistable_and_dual :
    (determinantSpechtBundle V k t b).IsMeanSlopeSemistable ∧
      ((determinantSpechtBundle V k t b).dualOfNormMeasurability).IsMeanSlopeSemistable := by
  let ρ := Arithmetic.representationBaseChange K (Arithmetic.Specht.integralRepresentation t)
  let : ρ.IsIrreducible := Arithmetic.Specht.integralRepresentation_baseChange_isIrreducible K t
  exact isMeanSlopeSemistable_lineTensor_and_dual_of_isIrreducible
    (determinantPower V k) (latticeBundle S t b)
    (determinantPower_isLine V k).rank_eq_one finrank_pos ρ
    (latticeNormFamily_orbitAction S t b)

/-- The canonical determinant--Specht auxiliary bundle is semistable. -/
instance determinantSpechtBundle_isMeanSlopeSemistable :
    (determinantSpechtBundle V k t b).IsMeanSlopeSemistable :=
  (determinantSpechtBundle_isMeanSlopeSemistable_and_dual V k t b).1

/-- The dual of the canonical determinant--Specht auxiliary bundle is semistable. -/
instance determinantSpechtBundle_dual_isMeanSlopeSemistable :
    (determinantSpechtBundle V k t b).dualOfNormMeasurability.IsMeanSlopeSemistable :=
  (determinantSpechtBundle_isMeanSlopeSemistable_and_dual V k t b).2

/-- The slope formula in the canonical rectangular covolume notation used by
the asymptotic error-elimination theorem. -/
theorem determinantSpechtBundle_slope_rectangle :
    (determinantSpechtBundle V k t b).slope =
      n * V.slope -
        (S.v S.Ωinf).toReal * rectangleLogCovolume (finrank K V) k := by
  have hn : n = finrank K V * k := by
    simpa using Fintype.card_congr (rectangleCoordinates t)
  have hp : finrank K (⨂[K] (_ : Fin k), ⋀[K]^(finrank K V) V) = 1 :=
    (determinantPower_isLine V k).rank_eq_one
  change ((determinantPower V k) ⊗ʰ (latticeBundle S t b)).slope = _
  rw [slope_orthogonalTensorPair (determinantPower V k) (latticeBundle S t b)
    (by simp only [hp, Nat.zero_lt_one]) finrank_pos,
    determinantPower_slope_eq_rank_mul, latticeBundle_slope_rectangle, ← hn]
  ring

/-- The actual auxiliary slope, before identifying the lattice covolume with
the canonical rectangular covolume. -/
theorem determinantSpechtBundle_slope :
    (determinantSpechtBundle V k t b).slope =
      n * V.slope - (S.v S.Ωinf).toReal *
        (Real.log (ZLattice.covolume (spanLattice t)) /
          finrank K (K ⊗[ℤ] orbitLattice t)) := by
  have hr : 0 < finrank K (K ⊗[ℤ] orbitLattice t) := Module.finrank_pos
  have hn : n = finrank K V * k := by
    simpa using Fintype.card_congr (rectangleCoordinates t)
  have hp : finrank K (⨂[K] (_ : Fin k), ⋀[K]^(finrank K V) V) = 1 :=
    (determinantPower_isLine V k).rank_eq_one
  change ((determinantPower V k) ⊗ʰ (latticeBundle S t b)).slope = _
  rw [slope_orthogonalTensorPair (determinantPower V k) (latticeBundle S t b)
    (by simp only [hp, Nat.zero_lt_one]) hr,
    determinantPower_slope_eq_rank_mul, latticeBundle_slope, ← hn]
  ring

end BostConjecture.Adelic
