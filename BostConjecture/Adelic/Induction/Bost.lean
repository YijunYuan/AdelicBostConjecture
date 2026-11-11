/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Adelic.Induction.RankInduction
public import BostConjecture.Adelic.Induction.MaxSlope
public import BostConjecture.Adelic.Induction.FiniteMaxSlope
public import BostConjecture.Adelic.Slope.GeometricQuotient

/-!
# The adelic Bost theorem

This paper, Theorem 1.1 and Corollary 7.3. The concrete Section 6 geometric
quotient inequality supplies the input of simultaneous strong rank induction.
All tensor and quotient bundles carry their actual completed Hilbert/epsilon
norms. No geometric slope or tensor semistability assumption remains.
-/

@[expose] public section

noncomputable section

open Module Submodule
open scoped TensorProduct

namespace ArakelovGeometry.AdelicVectorBundle

universe u v w wι

variable {K : Type u} [Field K] [CharZero K] [Countable K]
  {S : AdelicStructure.{u, v} K} [S.IsProper]
  (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
  (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)

/-- The concrete geometric quotient theorem closes simultaneous rank induction
on carriers in the field universe, including zero-rank HN identities. -/
theorem tensorHN_and_semistable
    {E F : Type u} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    [AddCommGroup F] [Module K F] [FiniteDimensional K F]
    (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F)
    (hV : V.IsHermitian hN) (hW : W.IsHermitian hN) :
    (V.orthogonalTensorPair W hS hN hV hW).hermitianHNFiltration hS hN
        (orthogonalTensorPair_isHermitian V W hS hN hV hW) =
      tensorFiltration (V.hermitianHNFiltration hS hN hV)
        (W.hermitianHNFiltration hS hN hW) ∧
    (V.IsMeanSlopeSemistable hS hN → W.IsMeanSlopeSemistable hS hN →
      (V.orthogonalTensorPair W hS hN hV hW).IsMeanSlopeSemistable hS hN) := by
  apply tensorHN_and_semistable_of_geometric_quotient_bound hS hN ?_ E F V W hV hW
  intro A B Q _ _ _ _ _ _ _ _ _ _ _ _ X Y hX hY _ _ q hq _ hg
  exact slope_sum_le_tensor_quotient_of_geometricallySemistable X Y hS hN hX hY q hq hg

end ArakelovGeometry.AdelicVectorBundle
