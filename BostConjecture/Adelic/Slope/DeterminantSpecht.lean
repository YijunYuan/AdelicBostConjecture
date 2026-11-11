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
  {E : Type u} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (V : AdelicVectorBundle S E)
  (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
  (hcount : S.HasCommonCountableDenseSubfield)
  (k : ℕ) {n : ℕ} (t : OAI.Saxl.Tableau n (rectangle (finrank K E) k))
  (b : Basis (Fin (finrank K (K ⊗[ℤ] orbitLattice t))) ℤ (orbitLattice t))

/-- The determinant tensor power tensored with the actual adelic Specht lattice,
on exactly the source of `Geometry.projectiveDeterminantMap`. -/
def determinantSpechtBundle :
    AdelicVectorBundle S
      ((⨂[K] (_ : Fin k), ⋀[K]^(finrank K E) E) ⊗[K] (K ⊗[ℤ] orbitLattice t)) :=
  (determinantPower V (Or.inr hcount) hN k).orthogonalTensorPair
    (latticeBundle S t b hN hcount) (Or.inr hcount) hN
    (determinantPower_isHermitian V (Or.inr hcount) hN k)
    (latticeBundle_isHermitian S t b hN hcount)

theorem determinantSpechtBundle_isHermitian :
    (determinantSpechtBundle V hN hcount k t b).IsHermitian hN :=
  orthogonalTensorPair_isHermitian _ _ _ _ _ _

variable [S.IsProper]

/-- The actual auxiliary bundle and its actual dual are semistable, without
any semistability assumption on the original bundle. -/
theorem determinantSpechtBundle_isMeanSlopeSemistable_and_dual :
    (determinantSpechtBundle V hN hcount k t b).IsMeanSlopeSemistable
        (Or.inr hcount) hN ∧
      ((determinantSpechtBundle V hN hcount k t b).dualOfMeasurableBase
        (Or.inr hcount)).IsMeanSlopeSemistable (Or.inr hcount) hN := by
  let := Arithmetic.Specht.orbitLattice_baseChange_nontrivial K t
  let ρ := Arithmetic.representationBaseChange K (Arithmetic.Specht.integralRepresentation t)
  let : ρ.IsIrreducible := Arithmetic.Specht.integralRepresentation_baseChange_isIrreducible K t
  exact isMeanSlopeSemistable_lineTensor_and_dual_of_isIrreducible
    (determinantPower V (Or.inr hcount) hN k) (latticeBundle S t b hN hcount)
    (Or.inr hcount) hN (determinantPower_isHermitian V (Or.inr hcount) hN k)
    (latticeBundle_isHermitian S t b hN hcount)
    (determinantPower_isLine V (Or.inr hcount) hN k) finrank_pos ρ
    (latticeNormFamily_orbitAction S t b)

/-- The slope formula in the canonical rectangular covolume notation used by
the asymptotic error-elimination theorem. -/
theorem determinantSpechtBundle_slope_rectangle :
    (determinantSpechtBundle V hN hcount k t b).slope (Or.inr hcount) hN =
      n * V.slope (Or.inr hcount) hN -
        (S.v S.Ωinf).toReal * rectangleLogCovolume (finrank K E) k := by
  let := Arithmetic.Specht.orbitLattice_baseChange_nontrivial K t
  have hn : n = finrank K E * k := by
    simpa using Fintype.card_congr (rectangleCoordinates t)
  have hp : finrank K (⨂[K] (_ : Fin k), ⋀[K]^(finrank K E) E) = 1 :=
    determinantPower_isLine V (Or.inr hcount) hN k
  rw [determinantSpechtBundle, slope_orthogonalTensorPair _ _ _ _ _ _
    (by simp only [hp, Nat.zero_lt_one]) finrank_pos,
    determinantPower_slope_eq_rank_mul, latticeBundle_slope_rectangle, ← hn]
  ring

/-- The actual auxiliary slope, before identifying the lattice covolume with
the canonical rectangular covolume. -/
theorem determinantSpechtBundle_slope :
    (determinantSpechtBundle V hN hcount k t b).slope (Or.inr hcount) hN =
      n * V.slope (Or.inr hcount) hN - (S.v S.Ωinf).toReal *
        (Real.log (ZLattice.covolume (spanLattice t)) /
          finrank K (K ⊗[ℤ] orbitLattice t)) := by
  let := Arithmetic.Specht.orbitLattice_baseChange_nontrivial K t
  have hr : 0 < finrank K (K ⊗[ℤ] orbitLattice t) := Module.finrank_pos
  have hn : n = finrank K E * k := by
    simpa using Fintype.card_congr (rectangleCoordinates t)
  have hp : finrank K (⨂[K] (_ : Fin k), ⋀[K]^(finrank K E) E) = 1 :=
    determinantPower_isLine V (Or.inr hcount) hN k
  rw [determinantSpechtBundle, slope_orthogonalTensorPair _ _ _ _ _ _
    (by simp only [hp, Nat.zero_lt_one]) hr,
    determinantPower_slope_eq_rank_mul, latticeBundle_slope, ← hn]
  ring

end BostConjecture.Adelic
