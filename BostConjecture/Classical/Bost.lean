/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Adelic.Induction.Bost
public import BostConjecture.Classical.Adelic.Tensor
public import BostConjecture.Classical.MaxSlope

/-!
# The classical Bost conjecture from Theorem 1.2

The conclusion uses the original metric, tensor notation and maximal-slope
definition from `81cf08a874039fde5d23c0fbf3970f7d28c3beca`.

The degree and completed tensor comparisons are proved in `Classical/Adelic`.
The adelic tensor theorem used in the proof is Theorem 1.2 of this paper.
-/

@[expose] public section
noncomputable section

open NumberField TensorProduct
open ArakelovGeometry ArakelovGeometry.AdelicStructure

namespace BostConjecture.Arithmetic.HermitianMetric

-- Keep the original algebra actions when the arithmetic tensor notation is opened.
scoped[BostConjecture.Arithmetic.HermitianMetric]
  attribute [instance 2000] Algebra.toModule Algebra.toSMul

universe u
variable {K M N : Type u} [Field K] [NumberField K]
    [AddCommGroup M] [Module (𝓞 K) M]
    [AddCommGroup N] [Module (𝓞 K) N]
    [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
    [Module.Finite (𝓞 K) N] [Module.Projective (𝓞 K) N]
    [Nontrivial (K ⊗[𝓞 K] M)] [Nontrivial (K ⊗[𝓞 K] N)]

/-- The actual integral tensor product has positive generic rank. -/
instance tensorGenericNontrivial :
    Nontrivial (K ⊗[𝓞 K] (M ⊗[𝓞 K] N)) := by
  apply Module.nontrivial_of_finrank_pos (R := K)
  rw [(AlgebraTensorModule.distribBaseChange (𝓞 K) K M N).finrank_eq,
    Module.finrank_tensorProduct]
  exact Nat.mul_pos Module.finrank_pos Module.finrank_pos

/-- This paper, Conjecture 1.1, maximal-slope formulation, proved by Theorem 1.2. See [Bost–Chen,
Problems 1.3–1.5][bc] and [Bost][bost97].

Bost's conjecture for the original integral Hermitian metrics, deduced from
Theorem 1.2 through the canonical adelization. -/
theorem maxSlope_tensor (h : HermitianMetric K M) (g : HermitianMetric K N) :
    (h ⊗[𝓞 K] g).maxSlope = h.maxSlope + g.maxSlope := by
  let : Countable K := (Module.finBasis ℚ K).repr.injective.countable
  have he := (h ⊗[𝓞 K] g).toAdelicBundle.maximalSlope_eq_of_completed_isometry
    (h.toAdelicBundle ⊗ʰ g.toAdelicBundle)
    (AlgebraTensorModule.distribBaseChange (𝓞 K) K M N) (h.toAdelicBundle_norm_tensor g)
  rw [AdelicVectorBundle.maximalSlope_orthogonalTensorPair,
    maximalSlope_toAdelicBundle h,
    maximalSlope_toAdelicBundle g,
    maximalSlope_toAdelicBundle (h ⊗[𝓞 K] g),
    ← EReal.coe_add, EReal.coe_eq_coe_iff] at he
  have hd : (Module.finrank ℚ K : ℝ) ≠ 0 :=
    (Nat.cast_pos.mpr (Module.finrank_pos (R := ℚ) (M := K)) :
      (0 : ℝ) < Module.finrank ℚ K).ne'
  apply mul_left_cancel₀ hd
  simpa only [mul_add] using he

end BostConjecture.Arithmetic.HermitianMetric
