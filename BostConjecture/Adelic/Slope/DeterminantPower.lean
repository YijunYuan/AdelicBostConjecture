/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Degree.LineVector
public import ArakelovGeometry.AdelicVectorBundle.Slope.Basic

/-!
# The determinant powers in the Specht auxiliary bundles

We use AG's actual orthogonal tensor product of determinant lines. Its slope is
the number of factors times the original degree, as needed in Lemma 6.1 of this
paper. No semistability assumption on the original bundle is involved.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace BostConjecture.Adelic

open ArakelovGeometry ArakelovGeometry.AdelicVectorBundle

universe u v w

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  (V : AdelicVectorBundle S)
  [hS : S.NormMeasurabilityHypotheses]
  [hN : S.IsArchimedeanNormalized]

/-- The actual orthogonal tensor power of the determinant adelic line. -/
abbrev determinantPower (k : ℕ) :
    AdelicVectorBundle S where
  carrier := ⨂[K] (_ : Fin k), ⋀[K]^(Module.finrank K V) V
  instAddCommGroup := inferInstance
  instModule := inferInstance
  instFiniteDimensional := inferInstance
  toNormFamily :=
    (orthogonalTensorLines (fun _ : Fin k ↦ V.determinantOfNormMeasurability)).toNormFamily
  toIsAdelic :=
    (orthogonalTensorLines (fun _ : Fin k ↦ V.determinantOfNormMeasurability)).toIsAdelic

instance determinantPower_isLine (k : ℕ) : (determinantPower V k).IsLine :=
  orthogonalTensorLines_isLine (fun _ : Fin k ↦ V.determinantOfNormMeasurability)

instance determinantPower_isHermitian (k : ℕ) :
    (determinantPower V k).IsHermitian :=
  orthogonalTensorLines_isHermitian (fun _ : Fin k ↦ V.determinantOfNormMeasurability)

variable [S.IsProper]

/-- The determinant tensor power has slope equal to the number of copies times
the original degree, including the empty tensor power. -/
theorem determinantPower_slope (k : ℕ) :
    (determinantPower V k).slope = k * V.degree := by
  rw [(determinantPower V k).slope_eq_degree_of_finrank_one
    (determinantPower_isLine V k).rank_eq_one,
    (determinantPower V k).degree_eq_lineDegree]
  change (orthogonalTensorLines
    (fun _ : Fin k ↦ V.determinantOfNormMeasurability)).lineDegree = _
  rw [lineDegree_orthogonalTensorLines]
  change (∑ _ : Fin k, V.degree) = _
  simp [nsmul_eq_mul]

/-- The common rectangular degree is rank times width. -/
theorem determinantPower_slope_eq_rank_mul (k : ℕ) :
    (determinantPower V k).slope =
      (Module.finrank K V * k : ℕ) * V.slope := by
  rw [determinantPower_slope, V.degree_eq_rank_mul_slope, Nat.cast_mul]
  ring

end BostConjecture.Adelic
