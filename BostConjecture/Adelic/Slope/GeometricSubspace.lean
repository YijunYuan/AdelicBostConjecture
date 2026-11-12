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
public import BostConjecture.Adelic.Contraction.Pairing

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
  [S.IsProper] {ι : Type w} [Fintype ι]
  {E : ι → Type u} [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]
  [∀ i, FiniteDimensional K (E i)]
  (V : ∀ i, AdelicVectorBundle S (E i))
  [hN : S.IsArchimedeanNormalized]
  [hcount : S.HasCommonCountableDenseSubfield] (hV : ∀ i, (V i).IsHermitian)
  {F : Type u} [AddCommGroup F] [Module K F] [FiniteDimensional K F]
  (U : AdelicVectorBundle S F)

include hV

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
        (fun i => determinantSpechtBundle ((V i).dualOfMeasurableBase)
            (k i) (t i) (b i))
      ∀ ω z, (D.dualOfMeasurableBase).norm ω
        ((BostConjecture.Geometry.canonicalPairing E hk t ha hl v hs A).baseChange
          (S.ϕ ω).Completion z) ≤ (determinantSpechtBundle U l v bU).norm ω z) :
    (n : ℝ) * U.slope -
        (S.v S.Ωinf).toReal * rectangleLogCovolume (finrank K F) l ≤
      (n : ℝ) * ∑ i, (V i).slope +
        (S.v S.Ωinf).toReal * ∑ i, rectangleLogCovolume (finrank K (E i)) (k i) := by
  let : ∀ i, AddCommGroup ((⨂[K] (_ : Fin (k i)),
      ⋀[K]^(finrank K (Dual K (E i))) (Dual K (E i))) ⊗[K] (K ⊗[ℤ] orbitLattice (t i))) :=
    fun _ ↦ Module.addCommMonoidToAddCommGroup K
  let D := orthogonalTensorOfMeasurableBase
    (fun i => determinantSpechtBundle ((V i).dualOfMeasurableBase)
        (k i) (t i) (b i))
    (hH := fun i => determinantSpechtBundle_isHermitian
      ((V i).dualOfMeasurableBase) (k i) (t i) (b i))
  have hcmp := slope_le_of_nonzero_completed_contraction
    (determinantSpechtBundle U l v bU) (D.dualOfMeasurableBase)
      (determinantSpechtBundle_isHermitian U l v bU)
    (determinantSpechtBundle_isMeanSlopeSemistable_and_dual U l v bU).1
    (determinantSpechtBundle_tensor_isMeanSlopeSemistable_and_dual
      (fun i => (V i).dualOfMeasurableBase) k t b).2
    (BostConjecture.Geometry.canonicalPairing E hk t ha hl v hs A) hA hcontract
  erw [determinantSpechtBundle_slope_rectangle,
    determinantSpechtBundle_dual_tensor_dual_slope_rectangle V k t b hV] at hcmp
  exact hcmp

/-- The finite-degree geometric comparison with the actual completed canonical
pairing contraction supplied by the checked local norm theorem. -/
theorem canonicalPairing_finite_degree_bound (hU : U.IsHermitian)
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
    (hi : ∀ ω x, (orthogonalTensorOfMeasurableBase V).norm ω
      (A.baseChange (S.ϕ ω).Completion x) = U.norm ω x) :
    (n : ℝ) * U.slope -
        (S.v S.Ωinf).toReal * rectangleLogCovolume (finrank K F) l ≤
      (n : ℝ) * ∑ i, (V i).slope +
        (S.v S.Ωinf).toReal * ∑ i, rectangleLogCovolume (finrank K (E i)) (k i) := by
  exact canonicalPairing_finite_degree_bound_of_norm_le V hV U
    hk t ha b hl v hs bU A hA
    (Contraction.canonicalPairing_norm_le V hV hk t ha b U hU hl v hs bU A hi)

section Limit

variable [∀ i, Nontrivial (E i)] [Nontrivial F]

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
        (fun i => determinantSpechtBundle ((V i).dualOfMeasurableBase)
            (k i) (t i) (b i))
      ∀ ω z, (D.dualOfMeasurableBase).norm ω
        ((BostConjecture.Geometry.canonicalPairing E hk t ha hl v hs A).baseChange
          (S.ϕ ω).Completion z) ≤ (determinantSpechtBundle U l v bU).norm ω z) :
    U.slope ≤ ∑ i, (V i).slope := by
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
    exact canonicalPairing_finite_degree_bound_of_norm_le V hV U
      (hk r) (t r) (fun i p => by simp) b (hl r) (v r) (fun p => by simp) bU A (hne r)
      (hcontract (d * (r + 1)) (l r) (k r) (hk r) (t r) (fun i p => by simp) b
        (hl r) (v r) (fun p => by simp) bU)

/-- The geometric subspace inequality for the prescribed completed tensor norm.
The canonical pairing norm bound is discharged by its concrete local producer. -/
theorem slope_le_sum_of_geometricallySemistable
    (hU : U.IsHermitian) (A : F →ₗ[K] (⨂[K] i, E i))
    (hA : ∀ ω x, (orthogonalTensorOfMeasurableBase V).norm ω
      (A.baseChange (S.ϕ ω).Completion x) = U.norm ω x)
    (hgeom : ArakelovGeometry.InvariantTheory.IsGeometricallySemistableTensorSubspace E A) :
    U.slope ≤ ∑ i, (V i).slope := by
  apply slope_le_sum_of_geometricallySemistable_of_pairing_norm_le V hV U A hgeom
  intro n l k hk t ha b hl v hs bU
  exact Contraction.canonicalPairing_norm_le V hV hk t ha b U hU hl v hs bU A hA

end Limit

end BostConjecture.Adelic
