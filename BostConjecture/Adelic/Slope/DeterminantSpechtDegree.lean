/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Adelic.Slope.DeterminantSpecht
public import BostConjecture.Adelic.Induction.FiniteSlopes
public import ArakelovGeometry.AdelicVectorBundle.Slope.DualUpper

/-!
# Slopes of determinant–Specht tensor products and their duals

The independent finite mean-slope identity computes the exact covolume error
of the actual auxiliary product. Its proof has no geometric-slope premise.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace BostConjecture.Adelic

open ArakelovGeometry ArakelovGeometry.AdelicVectorBundle Specht Module

universe u v w

variable {K : Type u} [Field K] [CharZero K] {S : AdelicStructure.{u, v} K}
  [S.IsProper] {ι : Type w} [Fintype ι]
  {E : ι → Type u} [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]
  [∀ i, FiniteDimensional K (E i)] (V : ∀ i, AdelicVectorBundle S (E i))
  [hN : S.IsArchimedeanNormalized]
  [hcount : S.HasCommonCountableDenseSubfield]
  (k : ι → ℕ) {n : ι → ℕ}
  (t : ∀ i, OAI.Saxl.Tableau (n i) (rectangle (finrank K (E i)) (k i)))
  (b : ∀ i, Basis (Fin (finrank K (K ⊗[ℤ] orbitLattice (t i)))) ℤ (orbitLattice (t i)))

/-- The slope of the actual independent auxiliary tensor, with every
rectangular error expressed in the canonical asymptotic notation. -/
theorem determinantSpechtBundle_tensor_slope_rectangle :
    (orthogonalTensorOfMeasurableBase
      (fun i => determinantSpechtBundle (V i) (k i) (t i) (b i))).slope =
      ∑ i, ((n i : ℝ) * (V i).slope -
        (S.v S.Ωinf).toReal * rectangleLogCovolume (finrank K (E i)) (k i)) := by
  have hr (i : ι) : 0 < finrank K
      ((⨂[K] (_ : Fin (k i)), ⋀[K]^(finrank K (E i)) (E i)) ⊗[K]
        (K ⊗[ℤ] orbitLattice (t i))) := by
    have hp : finrank K (⨂[K] (_ : Fin (k i)), ⋀[K]^(finrank K (E i)) (E i)) = 1 :=
      (determinantPower_isLine (V i) (k i)).rank_eq_one
    simpa only [Module.finrank_tensorProduct, hp, one_mul] using
      (finrank_pos : 0 < finrank K (K ⊗[ℤ] orbitLattice (t i)))
  rw [slope_orthogonalTensorOfMeasurableBase _ _ hr]
  exact Finset.sum_congr rfl fun i _ =>
    determinantSpechtBundle_slope_rectangle (V i) (k i) (t i) (b i)

/-- The exact slope of the actual dual auxiliary product in Section 6. -/
theorem determinantSpechtBundle_tensor_dual_slope_rectangle :
    ((orthogonalTensorOfMeasurableBase
      (fun i => determinantSpechtBundle (V i) (k i) (t i) (b i))).dualOfMeasurableBase).slope =
      ∑ i, (-(n i : ℝ) * (V i).slope +
        (S.v S.Ωinf).toReal * rectangleLogCovolume (finrank K (E i)) (k i)) := by
  have h := slope_add_slope_dual_eq_zero_of_isHermitian
    (orthogonalTensorOfMeasurableBase
      (fun i => determinantSpechtBundle (V i) (k i) (t i) (b i)))
  rw [determinantSpechtBundle_tensor_slope_rectangle] at h
  calc
    _ = -(∑ i, ((n i : ℝ) * (V i).slope -
        (S.v S.Ωinf).toReal * rectangleLogCovolume (finrank K (E i)) (k i))) := by
      linarith
    _ = _ := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring

section DualFactors

variable {d : ℕ}
  (tD : ∀ i, OAI.Saxl.Tableau d (rectangle (finrank K (Dual K (E i))) (k i)))
  (bD : ∀ i, Basis (Fin (finrank K (K ⊗[ℤ] orbitLattice (tD i)))) ℤ
    (orbitLattice (tD i)))

-- Use the field-specific dual instance to avoid searching for projectivity
-- through every layer of the nested auxiliary tensor.
omit [Fintype ι] in
local instance [Finite ι] : FiniteDimensional K (Dual K
    (⨂[K] i, (⨂[K] (_ : Fin (k i)), ⋀[K]^(finrank K (Dual K (E i))) (Dual K (E i))) ⊗[K]
      (K ⊗[ℤ] orbitLattice (tD i)))) :=
  Subspace.instModuleDualFiniteDimensional (K := K)
    (V := ⨂[K] i, (⨂[K] (_ : Fin (k i)),
      ⋀[K]^(finrank K (Dual K (E i))) (Dual K (E i))) ⊗[K] (K ⊗[ℤ] orbitLattice (tD i)))

/-- The right-hand slope in Section 6: apply the auxiliary construction to
the actual duals of the original factors, then dualize their tensor product. -/
theorem determinantSpechtBundle_dual_tensor_dual_slope_rectangle
    (hV : ∀ i, (V i).IsHermitian) :
    ((orthogonalTensorOfMeasurableBase
      (fun i => determinantSpechtBundle ((V i).dualOfMeasurableBase)
          (k i) (tD i) (bD i))).dualOfMeasurableBase).slope =
      (d : ℝ) * ∑ i, (V i).slope +
        (S.v S.Ωinf).toReal * ∑ i, rectangleLogCovolume (finrank K (E i)) (k i) := by
  rw [determinantSpechtBundle_tensor_dual_slope_rectangle]
  have hd (i : ι) : ((V i).dualOfMeasurableBase).slope = -(V i).slope := by
    have h := slope_add_slope_dual_eq_zero_of_isHermitian
      (V i)
    linarith
  simp_rw [hd, Subspace.dual_finrank_eq, neg_mul_neg]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

end DualFactors

end BostConjecture.Adelic
