/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Adelic.Induction.FiniteMaxSlope
public import BostConjecture.Adelic.Induction.MaxSlope
public import BostConjecture.Adelic.Induction.RankInduction
public import BostConjecture.Adelic.Semistability.Comparison
public import BostConjecture.Adelic.Slope.GeometricQuotient

/-!
# The adelic Bost theorem

This paper, Theorem 1.2 and Corollary 7.3. The concrete Section 6 geometric
quotient inequality supplies the input of simultaneous strong rank induction.
All tensor and quotient bundles carry their actual completed Hilbert/epsilon
norms. No geometric slope or tensor semistability assumption remains.
-/

@[expose] public section

noncomputable section

open Module Submodule
open scoped TensorProduct

namespace ArakelovGeometry.AdelicVectorBundle

universe u v wι

variable {K : Type u} [Field K] [CharZero K] [Countable K]
  {S : AdelicStructure.{u, v} K} [S.IsProper]
  [hN : S.IsArchimedeanNormalized]

/-- This paper, proof of Theorem 1.2, simultaneous rank induction. See [Chen–Moriwaki, Theorem
5.6.1][cm] for the original reduction.

The concrete geometric quotient theorem closes simultaneous rank induction
with independent carrier universes, including zero-rank HN identities. -/
theorem tensorHN_and_semistable
    (V : AdelicVectorBundle S) (W : AdelicVectorBundle S)
    [hV : V.IsHermitian] [hW : W.IsHermitian] :
    (V ⊗ʰ W).hermitianHNFiltration =
      tensorFiltration (V.hermitianHNFiltration)
        (W.hermitianHNFiltration) ∧
    (V.IsSemistable → W.IsSemistable → (V ⊗ʰ W).IsSemistable) := by
  have h := tensorHN_and_semistable_of_geometric_quotient_bound
    (S := S) (fun Q _ _ _ _ X Y _ _ _ _ _ _ q hq _ hg ↦
      slope_sum_le_tensor_quotient_of_geometricallySemistable X Y q hq hg) V W
  refine ⟨h.1, fun hsV hsW ↦ ?_⟩
  exact (isSemistable_iff_isMeanSlopeSemistable (V ⊗ʰ W)).mpr
    (h.2 ((isSemistable_iff_isMeanSlopeSemistable V).mp hsV)
      ((isSemistable_iff_isMeanSlopeSemistable W).mp hsW))

/-- This paper, Theorem 1.2: maximal slopes add under the actual binary
orthogonal tensor product. The two factors may have independent carrier universes. -/
theorem maximalSlope_orthogonalTensorPair
    (V : AdelicVectorBundle S) (W : AdelicVectorBundle S)
    [hV : V.IsHermitian] [hW : W.IsHermitian]
    [Nontrivial V] [Nontrivial W] :
    (V ⊗ʰ W).maximalSlope =
      V.maximalSlope + W.maximalSlope := by
  exact maximalSlope_orthogonalTensorPair_of_hnFiltration_eq V W
    finrank_pos finrank_pos (tensorHN_and_semistable V W).1

/-- This paper, Theorem 1.2, binary semistability consequence.

The binary orthogonal tensor of semistable Hermitian adelic bundles is
semistable, with positive rank supplied by the factors' semistability. -/
instance isSemistable_orthogonalTensorPair
    (V : AdelicVectorBundle S) (W : AdelicVectorBundle S)
    [hV : V.IsHermitian] [hW : W.IsHermitian]
    [V.IsSemistable] [W.IsSemistable] :
    (V ⊗ʰ W).IsSemistable :=
  (tensorHN_and_semistable V W).2 inferInstance inferInstance

/-- This paper, Corollary 7.3: the actual tensor HN filtration is the weighted
tensor of the factor HN filtrations. Zero-rank factors and zero grades are allowed. -/
theorem hermitianHNFiltration_orthogonalTensorPair
    (V : AdelicVectorBundle S) (W : AdelicVectorBundle S)
    [hV : V.IsHermitian] [hW : W.IsHermitian] :
    (V ⊗ʰ W).hermitianHNFiltration =
      tensorFiltration (V.hermitianHNFiltration)
        (W.hermitianHNFiltration) := by
  exact (tensorHN_and_semistable V W).1

/-- This paper, Theorem 1.2, finite-family form: maximal slopes add on the
actual orthogonal tensor of any finite family of positive-rank factors,
including the empty family. -/
theorem maximalSlope_orthogonalTensorOfNormMeasurability
    {ι : Type wι} [Fintype ι]
    (V : ι → AdelicVectorBundle S)
    [hV : ∀ i, (V i).IsHermitian] [∀ i, Nontrivial (V i)] :
    (orthogonalTensorOfNormMeasurability V).maximalSlope =
      ∑ i, (V i).maximalSlope := by
  apply maximalSlope_orthogonalTensorOfNormMeasurability_of_binary_additivity
    ?_ V (fun _ ↦ finrank_pos)
  intro X Y hX hY hA hB
  let : Nontrivial X := Module.nontrivial_of_finrank_pos hA
  let : Nontrivial Y := Module.nontrivial_of_finrank_pos hB
  exact maximalSlope_orthogonalTensorPair X Y

/-- This paper, Theorem 1.2, finite-family semistability consequence. The formalization also
includes the empty family.

The actual orthogonal tensor of any finite family of semistable
Hermitian adelic bundles is semistable, including the empty family. -/
instance isSemistable_orthogonalTensorOfNormMeasurability
    {ι : Type wι} [Fintype ι]
    (V : ι → AdelicVectorBundle S)
    [hV : ∀ i, (V i).IsHermitian]
    [hsemi : ∀ i, (V i).IsSemistable] :
    (orthogonalTensorOfNormMeasurability V).IsSemistable := by
  let : ∀ i, (V i).IsMeanSlopeSemistable := fun i ↦
    ((V i).isSemistable_iff_isMeanSlopeSemistable).mp (hsemi i)
  apply (isSemistable_iff_isMeanSlopeSemistable _).mpr
  apply isMeanSlopeSemistable_orthogonalTensorOfNormMeasurability_of_binary_additivity
    ?_ V
  intro X Y hX hY hA hB
  let : Nontrivial X := Module.nontrivial_of_finrank_pos hA
  let : Nontrivial Y := Module.nontrivial_of_finrank_pos hB
  exact maximalSlope_orthogonalTensorPair X Y

end ArakelovGeometry.AdelicVectorBundle
