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
  {E : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (V : AdelicVectorBundle S E)
  (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
  (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)

/-- The actual orthogonal tensor power of the determinant adelic line. -/
def determinantPower (k : ℕ) :
    AdelicVectorBundle S (⨂[K] (_ : Fin k), ⋀[K]^(Module.finrank K E) E) :=
  orthogonalTensorLines (fun _ : Fin k ↦ V.determinantOfMeasurableBase hS hN)
    (fun _ ↦ V.determinantOfMeasurableBase_isLine hS hN) hN

theorem determinantPower_isLine (k : ℕ) : (determinantPower V hS hN k).IsLine :=
  orthogonalTensorLines_isLine _ _ _

theorem determinantPower_isHermitian (k : ℕ) :
    (determinantPower V hS hN k).IsHermitian hN :=
  orthogonalTensorLines_isHermitian _ _ _

variable [S.IsProper]

/-- The determinant tensor power has slope equal to the number of copies times
the original degree, including the empty tensor power. -/
theorem determinantPower_slope (k : ℕ) :
    (determinantPower V hS hN k).slope hS hN = k * V.degree hS hN := by
  rw [(determinantPower V hS hN k).slope_eq_degree_of_finrank_one hS hN
    (determinantPower_isLine V hS hN k),
    (determinantPower V hS hN k).degree_eq_lineDegree hS hN
      (determinantPower_isLine V hS hN k)]
  change (orthogonalTensorLines
    (fun _ : Fin k ↦ V.determinantOfMeasurableBase hS hN)
    (fun _ ↦ V.determinantOfMeasurableBase_isLine hS hN) hN).lineDegree _ = _
  rw [lineDegree_orthogonalTensorLines]
  change (∑ _ : Fin k, V.degree hS hN) = _
  simp [nsmul_eq_mul]

/-- The common rectangular degree is rank times width. -/
theorem determinantPower_slope_eq_rank_mul (k : ℕ) :
    (determinantPower V hS hN k).slope hS hN =
      (Module.finrank K E * k : ℕ) * V.slope hS hN := by
  rw [determinantPower_slope, V.degree_eq_rank_mul_slope hS hN, Nat.cast_mul]
  ring

end BostConjecture.Adelic
