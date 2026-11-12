/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Adelic.Induction.TensorTransport
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
  [hS : S.HasMeasurableBase]
  [hN : S.IsArchimedeanNormalized]

/-- The concrete geometric quotient theorem closes simultaneous rank induction
on carriers in the field universe, including zero-rank HN identities. -/
theorem tensorHN_and_semistable
    {E F : Type u} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    [AddCommGroup F] [Module K F] [FiniteDimensional K F]
    (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F)
    (hV : V.IsHermitian) (hW : W.IsHermitian) :
    (V.orthogonalTensorPair W).hermitianHNFiltration =
      tensorFiltration (V.hermitianHNFiltration)
        (W.hermitianHNFiltration) ∧
    (V.IsMeanSlopeSemistable → W.IsMeanSlopeSemistable →
      (V.orthogonalTensorPair W).IsMeanSlopeSemistable) := by
  apply tensorHN_and_semistable_of_geometric_quotient_bound ?_ E F V W hV hW
  intro A B Q _ _ _ _ _ _ _ _ _ _ _ _ X Y hX hY _ _ q hq _ hg
  exact slope_sum_le_tensor_quotient_of_geometricallySemistable X Y hX hY q hq hg

variable {E F : Type w}
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]

/-- This paper, Theorem 1.1: maximal slopes add under the actual binary
orthogonal tensor product. The original field and arbitrary carrier universe
are retained; finite-dimensional coordinates are transported isometrically. -/
theorem maximalSlope_orthogonalTensorPair
    (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F)
    (hV : V.IsHermitian) (hW : W.IsHermitian)
    (hE : 0 < finrank K E) (hF : 0 < finrank K F) :
    (V.orthogonalTensorPair W).maximalSlope =
      V.maximalSlope + W.maximalSlope := by
  let e := (finBasis K E).equivFun.symm
  let f := (finBasis K F).equivFun.symm
  let X := V.pullbackEquiv e
  let Y := W.pullbackEquiv f
  have hX : X.IsHermitian := NormFamily.IsHermitian.pullback hV e.toLinearMap e.injective
  have hY : Y.IsHermitian := NormFamily.IsHermitian.pullback hW f.toLinearMap f.injective
  have hrX : 0 < finrank K (Fin (finrank K E) → K) := e.finrank_eq.symm ▸ hE
  have hrY : 0 < finrank K (Fin (finrank K F) → K) := f.finrank_eq.symm ▸ hF
  have hXY := maximalSlope_orthogonalTensorPair_of_hnFiltration_eq X Y hX hY
    hrX hrY (tensorHN_and_semistable X Y hX hY).1
  have he := maximalSlope_eq_of_completed_isometry X V e (fun _ _ ↦ rfl)
  have hf := maximalSlope_eq_of_completed_isometry Y W f (fun _ _ ↦ rfl)
  have ht := maximalSlope_eq_of_completed_isometry
    (X.orthogonalTensorPair Y) (V.orthogonalTensorPair W)
    (TensorProduct.congr e f)
    (fun ω z ↦ NormFamily.orthogonalTensorPair_norm_congr
      X.toNormFamily Y.toNormFamily V.toNormFamily W.toNormFamily
      hX hY hV hW
      e f ω (fun _ ↦ rfl) (fun _ ↦ rfl) z)
  exact ht.symm.trans (hXY.trans (congrArg₂ (· + ·) he hf))

/-- The binary orthogonal tensor of semistable Hermitian adelic bundles is
semistable, with positive rank supplied by the factors' semistability. -/
theorem isMeanSlopeSemistable_orthogonalTensorPair
    (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F)
    (hV : V.IsHermitian) (hW : W.IsHermitian)
    (hsV : V.IsMeanSlopeSemistable) (hsW : W.IsMeanSlopeSemistable) :
    (V.orthogonalTensorPair W).IsMeanSlopeSemistable := by
  have hr : 0 < finrank K (E ⊗[K] F) := by
    rw [finrank_tensorProduct]
    exact Nat.mul_pos hsV.1 hsW.1
  apply (isMeanSlopeSemistable_iff_maximalSlope_eq_slope _ hr).mpr
  rw [maximalSlope_orthogonalTensorPair V W hV hW hsV.1 hsW.1,
    slope_orthogonalTensorPair V W hsV.1 hsW.1,
    (V.isMeanSlopeSemistable_iff_maximalSlope_eq_slope hsV.1).mp hsV,
    (W.isMeanSlopeSemistable_iff_maximalSlope_eq_slope hsW.1).mp hsW,
    EReal.coe_add]

/-- This paper, Corollary 7.3: the actual tensor HN filtration is the weighted
tensor of the factor HN filtrations. Zero-rank factors and zero grades are allowed. -/
theorem hermitianHNFiltration_orthogonalTensorPair
    (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F)
    (hV : V.IsHermitian) (hW : W.IsHermitian) :
    (V.orthogonalTensorPair W).hermitianHNFiltration =
      tensorFiltration (V.hermitianHNFiltration)
        (W.hermitianHNFiltration) := by
  apply hermitianHNFiltration_orthogonalTensorPair_of_semistable_grades V W hV hW
  intro t u ht hu
  exact isMeanSlopeSemistable_orthogonalTensorPair
    (V.filtrationGraded _ t) (W.filtrationGraded _ u)
    (hV.filtrationGraded _ t) (hW.filtrationGraded _ u)
    ((filtrationGraded_hermitianHN_zero_or_semistable V t).resolve_left
      (Nat.ne_of_gt ht)).1
    ((filtrationGraded_hermitianHN_zero_or_semistable W u).resolve_left
      (Nat.ne_of_gt hu)).1

/-- This paper, Theorem 1.1, finite-family form: maximal slopes add on the
actual orthogonal tensor of any finite family of positive-rank factors,
including the empty family. -/
theorem maximalSlope_orthogonalTensorOfMeasurableBase
    {ι : Type wι} [Fintype ι] {D : ι → Type w}
    [∀ i, AddCommGroup (D i)] [∀ i, Module K (D i)]
    [∀ i, FiniteDimensional K (D i)] (V : ∀ i, AdelicVectorBundle S (D i))
    (hV : ∀ i, (V i).IsHermitian) (hr : ∀ i, 0 < finrank K (D i)) :
    (orthogonalTensorOfMeasurableBase V).maximalSlope =
      ∑ i, (V i).maximalSlope := by
  apply maximalSlope_orthogonalTensorOfMeasurableBase_of_binary_additivity ?_ V hV hr
  intro A B _ _ _ _ _ _ X Y hX hY hA hB
  exact maximalSlope_orthogonalTensorPair X Y hX hY hA hB

/-- The actual orthogonal tensor of any finite family of semistable
Hermitian adelic bundles is semistable, including the empty family. -/
theorem isMeanSlopeSemistable_orthogonalTensorOfMeasurableBase
    {ι : Type wι} [Fintype ι] {D : ι → Type w}
    [∀ i, AddCommGroup (D i)] [∀ i, Module K (D i)]
    [∀ i, FiniteDimensional K (D i)] (V : ∀ i, AdelicVectorBundle S (D i))
    (hV : ∀ i, (V i).IsHermitian)
    (hsemi : ∀ i, (V i).IsMeanSlopeSemistable) :
    (orthogonalTensorOfMeasurableBase V).IsMeanSlopeSemistable := by
  apply isMeanSlopeSemistable_orthogonalTensorOfMeasurableBase_of_binary_additivity
      ?_ V hV hsemi
  intro A B _ _ _ _ _ _ X Y hX hY hA hB
  exact maximalSlope_orthogonalTensorPair X Y hX hY hA hB

end ArakelovGeometry.AdelicVectorBundle
