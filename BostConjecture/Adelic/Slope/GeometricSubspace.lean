/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Adelic.Slope.Contraction
public import BostConjecture.Adelic.Slope.CovolumeLimit
public import BostConjecture.Adelic.Slope.DeterminantSpechtTensor
public import BostConjecture.Adelic.Slope.DeterminantSpechtDegree
public import BostConjecture.Adelic.Geometry.Nonvanishing

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

universe u v w

variable {K : Type u} [Field K] [CharZero K] {S : AdelicStructure.{u, v} K}
  [S.IsProper] {ι : Type w} [Fintype ι] [Nonempty ι]
  {E : ι → Type u} [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]
  [∀ i, FiniteDimensional K (E i)]
  (V : ∀ i, AdelicVectorBundle S (E i))
  (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
  (hcount : S.HasCommonCountableDenseSubfield) (hV : ∀ i, (V i).IsHermitian hN)
  {F : Type u} [AddCommGroup F] [Module K F] [FiniteDimensional K F]
  (U : AdelicVectorBundle S F)

include hV

set_option maxHeartbeats 800000 in
-- Elaborating the nested determinant tensors and their dual needs this budget.
/-- The exact finite-degree inequality, conditional only on the completed norm
bound for the displayed nonzero canonical pairing. -/
theorem canonicalPairing_finite_degree_bound_of_norm_le
    {n l : ℕ} {k : ι → ℕ} (hk : ∀ i, 0 < k i)
    (t : ∀ i, OAI.Saxl.Tableau n (rectangle (finrank K (Dual K (E i))) (k i)))
    (ha : ∀ i (p : PrimeSpectrum K),
      Module.rankAtStalk (Dual K (E i)) p = finrank K (Dual K (E i)))
    (b : ∀ i, Basis (Fin (finrank K (K ⊗[ℤ] orbitLattice (t i)))) ℤ (orbitLattice (t i)))
    (hl : 0 < l) (v : OAI.Saxl.Tableau n (rectangle (finrank K F) l))
    (hs : ∀ p : PrimeSpectrum K, Module.rankAtStalk F p = finrank K F)
    (bU : Basis (Fin (finrank K (K ⊗[ℤ] orbitLattice v))) ℤ (orbitLattice v))
    (A : F →ₗ[K] (⨂[K] i, E i))
    (hA : BostConjecture.Geometry.canonicalPairing E hk t ha hl v hs A ≠ 0)
    (hcontract :
      let D := orthogonalTensorOfMeasurableBase
        (fun i => determinantSpechtBundle ((V i).dualOfMeasurableBase (Or.inr hcount))
          hN hcount (k i) (t i) (b i)) (Or.inr hcount) hN
        (fun i => determinantSpechtBundle_isHermitian
          ((V i).dualOfMeasurableBase (Or.inr hcount)) hN hcount (k i) (t i) (b i))
      ∀ ω z, (D.dualOfMeasurableBase (Or.inr hcount)).norm ω
        ((BostConjecture.Geometry.canonicalPairing E hk t ha hl v hs A).baseChange
          (S.ϕ ω).Completion z) ≤ (determinantSpechtBundle U hN hcount l v bU).norm ω z) :
    (n : ℝ) * U.slope (Or.inr hcount) hN -
        (S.v S.Ωinf).toReal * rectangleLogCovolume (finrank K F) l ≤
      (n : ℝ) * ∑ i, (V i).slope (Or.inr hcount) hN +
        (S.v S.Ωinf).toReal * ∑ i, rectangleLogCovolume (finrank K (E i)) (k i) := by
  let D := orthogonalTensorOfMeasurableBase
    (fun i => determinantSpechtBundle ((V i).dualOfMeasurableBase (Or.inr hcount))
      hN hcount (k i) (t i) (b i)) (Or.inr hcount) hN
    (fun i => determinantSpechtBundle_isHermitian
      ((V i).dualOfMeasurableBase (Or.inr hcount)) hN hcount (k i) (t i) (b i))
  have hcmp := slope_le_of_nonzero_completed_contraction
    (determinantSpechtBundle U hN hcount l v bU) (D.dualOfMeasurableBase (Or.inr hcount))
    (Or.inr hcount) hN (determinantSpechtBundle_isHermitian U hN hcount l v bU)
    (determinantSpechtBundle_isMeanSlopeSemistable_and_dual U hN hcount l v bU).1
    (determinantSpechtBundle_tensor_isMeanSlopeSemistable_and_dual
      (fun i => (V i).dualOfMeasurableBase (Or.inr hcount)) hN hcount k t b).2
    (BostConjecture.Geometry.canonicalPairing E hk t ha hl v hs A) hA hcontract
  rw [determinantSpechtBundle_slope_rectangle,
    determinantSpechtBundle_dual_tensor_dual_slope_rectangle V hN hcount k t b hV] at hcmp
  exact hcmp

section Limit

variable [∀ i, Nontrivial (E i)] [Nontrivial F]

set_option maxHeartbeats 1200000 in
-- The dependent sequence contains integral tableaux and their original-field maps.
/-- Geometric semistability and the exact universal canonical-pairing norm
inequality imply the subspace slope bound. All nonvanishing, rank choices,
semistability, slope computation, and limiting steps are discharged here. -/
theorem slope_le_sum_of_geometricallySemistable_of_pairing_norm_le
    (A : F →ₗ[K] (⨂[K] i, E i))
    (hgeom : ArakelovGeometry.InvariantTheory.IsGeometricallySemistableTensorSubspace E A)
    (hcontract : ∀ (n l : ℕ) (k : ι → ℕ) (hk : ∀ i, 0 < k i)
      (t : ∀ i, OAI.Saxl.Tableau n (rectangle (finrank K (Dual K (E i))) (k i)))
      (ha : ∀ i (p : PrimeSpectrum K),
        Module.rankAtStalk (Dual K (E i)) p = finrank K (Dual K (E i)))
      (b : ∀ i, Basis (Fin (finrank K (K ⊗[ℤ] orbitLattice (t i)))) ℤ (orbitLattice (t i)))
      (hl : 0 < l) (v : OAI.Saxl.Tableau n (rectangle (finrank K F) l))
      (hs : ∀ p : PrimeSpectrum K, Module.rankAtStalk F p = finrank K F)
      (bU : Basis (Fin (finrank K (K ⊗[ℤ] orbitLattice v))) ℤ (orbitLattice v)),
      let D := orthogonalTensorOfMeasurableBase
        (fun i => determinantSpechtBundle ((V i).dualOfMeasurableBase (Or.inr hcount))
          hN hcount (k i) (t i) (b i)) (Or.inr hcount) hN
        (fun i => determinantSpechtBundle_isHermitian
          ((V i).dualOfMeasurableBase (Or.inr hcount)) hN hcount (k i) (t i) (b i))
      ∀ ω z, (D.dualOfMeasurableBase (Or.inr hcount)).norm ω
        ((BostConjecture.Geometry.canonicalPairing E hk t ha hl v hs A).baseChange
          (S.ϕ ω).Completion z) ≤ (determinantSpechtBundle U hN hcount l v bU).norm ω z) :
    U.slope (Or.inr hcount) hN ≤ ∑ i, (V i).slope (Or.inr hcount) hN := by
  obtain ⟨d, hd, _, _, hseq⟩ :=
    Geometry.exists_canonicalPairing_nonzero_sequence_of_geometricSemistability E A hgeom
  have hex (r : ℕ) : ∃ (l : ℕ) (k : ι → ℕ) (hl : 0 < l) (hk : ∀ i, 0 < k i)
      (t : ∀ i, OAI.Saxl.Tableau (d * (r + 1))
        (rectangle (finrank K (Dual K (E i))) (k i)))
      (v : OAI.Saxl.Tableau (d * (r + 1)) (rectangle (finrank K F) l)),
      BostConjecture.Geometry.canonicalPairing E hk t (fun i p => by simp)
        hl v (fun p => by simp) A ≠ 0 := by
    have hgeneral (a : ι → ℕ)
        (ha : ∀ i (p : PrimeSpectrum K), Module.rankAtStalk (Dual K (E i)) p = a i)
        (heq : a = fun i => finrank K (E i)) :
        ∃ (l : ℕ) (k : ι → ℕ) (hl : 0 < l) (hk : ∀ i, 0 < k i)
          (t : ∀ i, OAI.Saxl.Tableau (d * (r + 1)) (rectangle (a i) (k i)))
          (v : OAI.Saxl.Tableau (d * (r + 1)) (rectangle (finrank K F) l)),
          BostConjecture.Geometry.canonicalPairing E hk t ha hl v (fun p => by simp) A ≠ 0 := by
      subst a
      exact hseq (r + 1) (Nat.succ_pos r)
    exact hgeneral _ (fun i p => by simp) (funext fun i => Subspace.dual_finrank_eq)
  choose l k hl hk t v hne using hex
  apply le_of_rectangleLogCovolume_bounds (finrank_pos : 0 < finrank K F) hd
    (fun i => (finrank_pos : 0 < finrank K (E i))) l k
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
    exact canonicalPairing_finite_degree_bound_of_norm_le V hN hcount hV U
      (hk r) (t r) (fun i p => by simp) b (hl r) (v r) (fun p => by simp) bU A (hne r)
      (hcontract (d * (r + 1)) (l r) (k r) (hk r) (t r) (fun i p => by simp) b
        (hl r) (v r) (fun p => by simp) bU)

end Limit

end BostConjecture.Adelic
