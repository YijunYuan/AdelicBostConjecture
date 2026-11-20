/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Adelic.Contraction.Pairing
public import BostConjecture.Adelic.Geometry.Nonvanishing
public import BostConjecture.Adelic.Slope.Contraction
public import BostConjecture.Adelic.Slope.CovolumeLimit
public import BostConjecture.Adelic.Slope.DeterminantSpechtDegree
public import BostConjecture.Adelic.Slope.DeterminantSpechtTensor

/-!
# The finite-degree and limit comparisons for the actual canonical pairing

The intermediate reductions here take only the completed norm inequality of the
original-field canonical map. They compute both auxiliary slopes using the
actual determinant–Specht bundles, and use the invariant nonvanishing sequence
and the checked covolume limit. They do not assume arithmetic semistability of
the original factors.
-/

@[expose] public section
noncomputable section

open scoped TensorProduct

namespace BostConjecture.Adelic

open Module ArakelovGeometry ArakelovGeometry.AdelicVectorBundle Specht

universe u v w wV wU

variable {K : Type u} [Field K] [CharZero K] {S : AdelicStructure.{u, v} K}
  [S.IsProper] {ι : Type w} [Fintype ι]
  (V : ι → AdelicVectorBundle.{wV} S)
  [hN : S.IsArchimedeanNormalized]
  [hcount : S.HasCommonCountableDenseSubfield] [hV : ∀ i, (V i).IsHermitian]
  (U : AdelicVectorBundle.{wU} S)

include hV

/-- The exact finite-degree inequality, conditional only on the completed norm
bound for the displayed nonzero canonical pairing. -/
theorem canonicalPairing_finite_degree_bound_of_norm_le
    {n l : ℕ} {k : ι → ℕ} (hk : ∀ i, 0 < k i)
    (t : ∀ i, OAI.Saxl.Tableau n (rectangle (finrank K (Dual K (V i))) (k i)))
    (ha : ∀ i (p : PrimeSpectrum K),
      Module.rankAtStalk (Dual K (V i)) p = finrank K (Dual K (V i)))
    (b : ∀ i, Basis (Fin (finrank K (K ⊗[ℤ] orbitLattice (t i)))) ℤ (orbitLattice (t i)))
    (hl : 0 < l) (v : OAI.Saxl.Tableau n (rectangle (finrank K U) l))
    (hs : ∀ p : PrimeSpectrum K, Module.rankAtStalk U p = finrank K U)
    (bU : Basis (Fin (finrank K (K ⊗[ℤ] orbitLattice v))) ℤ (orbitLattice v))
    (A : U →ₗ[K] (⨂[K] i, V i))
    (hA : BostConjecture.Geometry.canonicalPairing (R := K) (fun i ↦ V i) hk t ha hl v hs A ≠ 0)
    (hcontract :
      let D := NormFamily.orthogonalTensor
        (E := fun i ↦ (⨂[K] (_ : Fin (k i)),
          ⋀[K]^(finrank K (Dual K (V i))) (Dual K (V i))) ⊗[K] (K ⊗[ℤ] orbitLattice (t i)))
        (fun i ↦ (determinantSpechtBundle ((V i).dualOfNormMeasurability)
            (k i) (t i) (b i)).toNormFamily)
      ∀ ω z, D.dual.norm ω
        ((BostConjecture.Geometry.canonicalPairing (R := K) (fun i ↦ V i)
          hk t ha hl v hs A).baseChange (S.ϕ ω).Completion z) ≤
            (determinantSpechtBundle U l v bU).norm ω z) :
    (n : ℝ) * U.slope -
        (S.v S.Ωinf).toReal * rectangleLogCovolume (finrank K U) l ≤
      (n : ℝ) * ∑ i, (V i).slope +
        (S.v S.Ωinf).toReal * ∑ i, rectangleLogCovolume (finrank K (V i)) (k i) := by
  let D := orthogonalTensorOfNormMeasurability
    (fun i => determinantSpechtBundle ((V i).dualOfNormMeasurability)
        (k i) (t i) (b i))
    (hH := fun i ↦ determinantSpechtBundle_isHermitian
      ((V i).dualOfNormMeasurability) (k i) (t i) (b i))
  have : D.dualOfNormMeasurability.IsMeanSlopeSemistable :=
    determinantSpechtBundle_tensor_dual_isMeanSlopeSemistable
      (fun i ↦ (V i).dualOfNormMeasurability) k t b
  have : (determinantSpechtBundle U l v bU).IsHermitian :=
    determinantSpechtBundle_isHermitian U l v bU
  have : (determinantSpechtBundle U l v bU).IsMeanSlopeSemistable :=
    determinantSpechtBundle_isMeanSlopeSemistable U l v bU
  let C := determinantSpechtBundle U l v bU
  let f : C →ₗ[K] D.dualOfNormMeasurability :=
    BostConjecture.Geometry.canonicalPairing (R := K) (fun i ↦ V i) hk t ha hl v hs A
  have hf : f ≠ 0 := by
    intro hf
    apply hA
    apply LinearMap.ext
    intro z
    apply LinearMap.ext
    intro x
    exact congrArg (fun g : C →ₗ[K] D.dualOfNormMeasurability ↦ g z x) hf
  have hc : ∀ ω z, D.dualOfNormMeasurability.norm ω
      (f.baseChange (S.ϕ ω).Completion z) ≤ C.norm ω z := hcontract
  have hcmp : C.slope ≤ D.dualOfNormMeasurability.slope :=
    slope_le_of_nonzero_completed_contraction C D.dualOfNormMeasurability f hf hc
  dsimp only [C] at hcmp
  erw [determinantSpechtBundle_slope_rectangle,
    determinantSpechtBundle_dual_tensor_dual_slope_rectangle V k t b] at hcmp
  exact hcmp

/-- This paper, equations (6.4)–(6.5).

The finite-degree geometric comparison with the actual completed canonical
pairing contraction supplied by the checked local norm theorem. -/
theorem canonicalPairing_finite_degree_bound [hU : U.IsHermitian]
    {n l : ℕ} {k : ι → ℕ} (hk : ∀ i, 0 < k i)
    (t : ∀ i, OAI.Saxl.Tableau n (rectangle (finrank K (Dual K (V i))) (k i)))
    (ha : ∀ i (p : PrimeSpectrum K),
      Module.rankAtStalk (Dual K (V i)) p = finrank K (Dual K (V i)))
    (b : ∀ i, Basis (Fin (finrank K (K ⊗[ℤ] orbitLattice (t i)))) ℤ (orbitLattice (t i)))
    (hl : 0 < l) (v : OAI.Saxl.Tableau n (rectangle (finrank K U) l))
    (hs : ∀ p : PrimeSpectrum K, Module.rankAtStalk U p = finrank K U)
    (bU : Basis (Fin (finrank K (K ⊗[ℤ] orbitLattice v))) ℤ (orbitLattice v))
    (A : U →ₗ[K] (⨂[K] i, V i))
    (hA : BostConjecture.Geometry.canonicalPairing (R := K) (fun i ↦ V i) hk t ha hl v hs A ≠ 0)
    (hi : ∀ ω x, (orthogonalTensorOfNormMeasurability V).norm ω
      (A.baseChange (S.ϕ ω).Completion x) = U.norm ω x) :
    (n : ℝ) * U.slope -
        (S.v S.Ωinf).toReal * rectangleLogCovolume (finrank K U) l ≤
      (n : ℝ) * ∑ i, (V i).slope +
        (S.v S.Ωinf).toReal * ∑ i, rectangleLogCovolume (finrank K (V i)) (k i) := by
  exact canonicalPairing_finite_degree_bound_of_norm_le V U
    hk t ha b hl v hs bU A hA
    (Contraction.canonicalPairing_norm_le V hk t ha b U hl v hs bU A hi)

section Limit

variable [∀ i, Nontrivial (V i)] [Nontrivial U]

/-- Geometric semistability and the exact universal canonical-pairing norm
inequality imply the subspace slope bound. All nonvanishing, rank choices,
semistability, slope computation, and limiting steps are discharged here. -/
theorem slope_le_sum_of_geometricallySemistable_of_pairing_norm_le
    (A : U →ₗ[K] (⨂[K] i, V i))
    (hgeom : ArakelovGeometry.InvariantTheory.IsGeometricallySemistableTensorSubspace
      (fun i ↦ V i) A)
    (hcontract : ∀ (n l : ℕ) (k : ι → ℕ) (hk : ∀ i, 0 < k i)
      (t : ∀ i, OAI.Saxl.Tableau n (rectangle (finrank K (Dual K (V i))) (k i)))
      (ha : ∀ i (p : PrimeSpectrum K),
        Module.rankAtStalk (Dual K (V i)) p = finrank K (Dual K (V i)))
      (b : ∀ i, Basis (Fin (finrank K (K ⊗[ℤ] orbitLattice (t i)))) ℤ (orbitLattice (t i)))
      (hl : 0 < l) (v : OAI.Saxl.Tableau n (rectangle (finrank K U) l))
      (hs : ∀ p : PrimeSpectrum K, Module.rankAtStalk U p = finrank K U)
      (bU : Basis (Fin (finrank K (K ⊗[ℤ] orbitLattice v))) ℤ (orbitLattice v)),
      let D := NormFamily.orthogonalTensor
        (E := fun i ↦ (⨂[K] (_ : Fin (k i)),
          ⋀[K]^(finrank K (Dual K (V i))) (Dual K (V i))) ⊗[K] (K ⊗[ℤ] orbitLattice (t i)))
        (fun i ↦ (determinantSpechtBundle ((V i).dualOfNormMeasurability)
            (k i) (t i) (b i)).toNormFamily)
      ∀ ω z, D.dual.norm ω
        ((BostConjecture.Geometry.canonicalPairing (R := K) (fun i ↦ V i)
          hk t ha hl v hs A).baseChange (S.ϕ ω).Completion z) ≤
            (determinantSpechtBundle U l v bU).norm ω z) :
    U.slope ≤ ∑ i, (V i).slope := by
  obtain ⟨d, hd, _, _, hseq⟩ :=
    Geometry.exists_canonicalPairing_nonzero_sequence_of_geometricSemistability
      (fun i ↦ V i) A hgeom
  have hex (r : ℕ) : ∃ (l : ℕ) (k : ι → ℕ) (hl : 0 < l) (hk : ∀ i, 0 < k i)
      (t : ∀ i, OAI.Saxl.Tableau (d * (r + 1))
        (rectangle (finrank K (Dual K (V i))) (k i)))
      (v : OAI.Saxl.Tableau (d * (r + 1)) (rectangle (finrank K U) l)),
      BostConjecture.Geometry.canonicalPairing (R := K) (fun i ↦ V i) hk t (fun i p => by simp)
        hl v (fun p => by simp) A ≠ 0 := by
    have hgeneral (a : ι → ℕ)
        (ha : ∀ i (p : PrimeSpectrum K), Module.rankAtStalk (Dual K (V i)) p = a i)
        (heq : a = fun i => finrank K (V i)) :
        ∃ (l : ℕ) (k : ι → ℕ) (hl : 0 < l) (hk : ∀ i, 0 < k i)
          (t : ∀ i, OAI.Saxl.Tableau (d * (r + 1)) (rectangle (a i) (k i)))
          (v : OAI.Saxl.Tableau (d * (r + 1)) (rectangle (finrank K U) l)),
          BostConjecture.Geometry.canonicalPairing (R := K) (fun i ↦ V i)
            hk t ha hl v (fun p => by simp) A ≠ 0 := by
      subst a
      exact hseq (r + 1) (Nat.succ_pos r)
    exact hgeneral _ (fun i p => by simp) (funext fun i => Subspace.dual_finrank_eq)
  choose l k hl hk t v hne using hex
  apply le_of_rectangleLogCovolume_bounds (finrank_pos : 0 < finrank K U) hd
    (fun i => (finrank_pos : 0 < finrank K (V i))) l k
  · intro r
    simpa using Fintype.card_congr (rectangleCoordinates (v r))
  · intro r i
    simpa only [Fintype.card_fin, Fintype.card_prod, Subspace.dual_finrank_eq] using
      Fintype.card_congr (rectangleCoordinates (t r i))
  · intro r
    let b (i : ι) : Basis (Fin (finrank K (K ⊗[ℤ] orbitLattice (t r i)))) ℤ
        (orbitLattice (t r i)) :=
      (Module.finBasis ℤ (orbitLattice (t r i))).reindex
        (finCongr (by rw [Module.finrank_baseChange]))
    let bU : Basis (Fin (finrank K (K ⊗[ℤ] orbitLattice (v r)))) ℤ (orbitLattice (v r)) :=
      (Module.finBasis ℤ (orbitLattice (v r))).reindex
        (finCongr (by rw [Module.finrank_baseChange]))
    exact canonicalPairing_finite_degree_bound_of_norm_le V U
      (hk r) (t r) (fun i p => by simp) b (hl r) (v r) (fun p => by simp) bU A (hne r)
      (hcontract (d * (r + 1)) (l r) (k r) (hk r) (t r) (fun i p => by simp) b
        (hl r) (v r) (fun p => by simp) bU)

/-- This paper, Theorem 6.2. This proves the inequality posed in [Bost–Chen, Problem 1.17][bc].

The geometric subspace inequality for the prescribed completed tensor norm.
The canonical pairing norm bound is discharged by its concrete local producer. -/
theorem slope_le_sum_of_geometricallySemistable
    [hU : U.IsHermitian] (A : U →ₗ[K] (⨂[K] i, V i))
    (hA : ∀ ω x, (orthogonalTensorOfNormMeasurability V).norm ω
      (A.baseChange (S.ϕ ω).Completion x) = U.norm ω x)
    (hgeom : ArakelovGeometry.InvariantTheory.IsGeometricallySemistableTensorSubspace
      (fun i ↦ V i) A) :
    U.slope ≤ ∑ i, (V i).slope := by
  apply slope_le_sum_of_geometricallySemistable_of_pairing_norm_le V U A hgeom
  intro n l k hk t ha b hl v hs bU
  exact Contraction.canonicalPairing_norm_le V hk t ha b U hl v hs bU A hA

end Limit

end BostConjecture.Adelic
