module

public import BostConjecture.InvariantTheory.ComplexClosure.Density
public import BostConjecture.InvariantTheory.ComplexClosure.ConstructibleImage
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian

/-!
# Euclidean closures of constructible sets of complex points

Finite decomposition into principal opens of prime zero loci reduces closure
comparison to the proved principal-open density theorem.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.InvariantTheory

/-- Spectral closed sets pull back to the canonical coordinate zero loci. -/
theorem pointToPoint_preimage_zeroLocus {K τ : Type*} [Field K]
    (I : Ideal (MvPolynomial τ K)) :
    MvPolynomial.pointToPoint (k := K) ⁻¹' PrimeSpectrum.zeroLocus (I : Set _) =
      MvPolynomial.zeroLocus K I := by
  ext x
  change (∀ p ∈ I, p ∈ MvPolynomial.vanishingIdeal K {x}) ↔
    ∀ p ∈ I, MvPolynomial.aeval x p = 0
  simp only [MvPolynomial.mem_vanishingIdeal_singleton_iff]

/-- The complex-point trace of a spectral closed set is Euclidean closed. -/
theorem isClosed_preimage_pointToPoint {τ : Type*}
    {S : Set (PrimeSpectrum (MvPolynomial τ ℂ))} (hS : IsClosed S) :
    IsClosed ((MvPolynomial.pointToPoint (k := ℂ) : (τ → ℂ) → _) ⁻¹' S) := by
  obtain ⟨I, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal S).mp hS
  rw [pointToPoint_preimage_zeroLocus]
  exact isClosed_zeroLocus I

/-- Principal opens of a prime zero locus have that entire zero locus as Euclidean closure. -/
theorem closure_principalOpen_prime {τ : Type*} [Finite τ]
    (I : Ideal (MvPolynomial τ ℂ)) [I.IsPrime]
    {u : MvPolynomial τ ℂ} (hu : u ∉ I) :
    closure {x : τ → ℂ | x ∈ MvPolynomial.zeroLocus ℂ I ∧ MvPolynomial.eval x u ≠ 0} =
      MvPolynomial.zeroLocus ℂ I := by
  apply Set.Subset.antisymm
  · exact closure_minimal (fun _ h => h.1) (isClosed_zeroLocus I)
  · intro x hx
    have hd := dense_principalOpen_zeroLocus I hu
    have hs : {y : MvPolynomial.zeroLocus ℂ I | MvPolynomial.eval y.val u ≠ 0} ⊆
        Subtype.val ⁻¹' closure {y : τ → ℂ | y ∈ MvPolynomial.zeroLocus ℂ I ∧
          MvPolynomial.eval y u ≠ 0} := fun y hy => subset_closure ⟨y.property, hy⟩
    exact closure_minimal hs (isClosed_closure.preimage continuous_subtype_val) (hd ⟨x, hx⟩)

/-- A locally closed coordinate set has an algebraic Euclidean closure. -/
theorem exists_closed_closure_principalOpen {τ : Type*} [Finite τ]
    (I : Ideal (MvPolynomial τ ℂ)) (u : MvPolynomial τ ℂ) :
    ∃ S : Set (PrimeSpectrum (MvPolynomial τ ℂ)), IsClosed S ∧
      closure {x : τ → ℂ | x ∈ MvPolynomial.zeroLocus ℂ I ∧ MvPolynomial.eval x u ≠ 0} =
        MvPolynomial.pointToPoint (k := ℂ) ⁻¹' S := by
  classical
  let P := {J ∈ I.minimalPrimes | u ∉ J}
  have hP : P.Finite := (Ideal.finite_minimalPrimes_of_isNoetherianRing _ I).subset
    (fun _ h => h.1)
  let S := ⋃ J ∈ P, PrimeSpectrum.zeroLocus (J : Set (MvPolynomial τ ℂ))
  have hS : IsClosed S := hP.isClosed_biUnion
    (fun J _ => PrimeSpectrum.isClosed_zeroLocus (R := MvPolynomial τ ℂ) (J : Set _))
  refine ⟨S, hS, Set.Subset.antisymm ?_ ?_⟩
  · apply closure_minimal _ (isClosed_preimage_pointToPoint hS)
    intro x hx
    have hI : I ≤ MvPolynomial.vanishingIdeal ℂ {x} := by
      intro p hp
      exact (MvPolynomial.mem_vanishingIdeal_singleton_iff x p).mpr (hx.1 p hp)
    obtain ⟨J, hJ, hJx⟩ := Ideal.exists_minimalPrimes_le hI
    have huJ : u ∉ J := fun h => hx.2 ((MvPolynomial.mem_vanishingIdeal_singleton_iff x u).mp (hJx h))
    exact Set.mem_iUnion.mpr ⟨J, Set.mem_iUnion.mpr ⟨⟨hJ, huJ⟩, hJx⟩⟩
  · intro x hx
    obtain ⟨J, hJ, hxJ⟩ := Set.mem_iUnion₂.mp hx
    have : J.IsPrime := hJ.1.isPrime
    have hxV : x ∈ MvPolynomial.zeroLocus ℂ J := by
      exact (pointToPoint_preimage_zeroLocus J ▸ hxJ)
    rw [← closure_principalOpen_prime J hJ.2] at hxV
    apply closure_mono (s := {y | y ∈ MvPolynomial.zeroLocus ℂ J ∧ MvPolynomial.eval y u ≠ 0}) ?_ hxV
    intro y hy
    exact ⟨MvPolynomial.zeroLocus_anti_mono hJ.1.le hy.1, hy.2⟩

/-- Basic spectral constructible sets have the expected coordinate-point traces. -/
theorem pointToPoint_preimage_basicConstructible {K τ : Type*} [Field K]
    (C : PrimeSpectrum.BasicConstructibleSetData (MvPolynomial τ K)) :
    (MvPolynomial.pointToPoint (k := K) : (τ → K) → _) ⁻¹' C.toSet =
      {x : τ → K | x ∈ MvPolynomial.zeroLocus K (Ideal.span (Set.range C.g)) ∧
        MvPolynomial.eval x C.f ≠ 0} := by
  ext x
  rw [MvPolynomial.zeroLocus_span]
  change ((∀ p ∈ Set.range C.g, p ∈ MvPolynomial.vanishingIdeal K {x}) ∧
    ¬ ∀ p ∈ ({C.f} : Set _), p ∈ MvPolynomial.vanishingIdeal K {x}) ↔ _
  simp only [MvPolynomial.mem_vanishingIdeal_singleton_iff, Set.mem_singleton_iff,
    forall_eq, Set.mem_ofPred_eq]
  rfl

/-- The Euclidean closure of a constructible complex-point trace is algebraic. -/
theorem exists_closed_closure_constructible {τ : Type*} [Finite τ]
    {S : Set (PrimeSpectrum (MvPolynomial τ ℂ))} (hS : Topology.IsConstructible S) :
    ∃ T : Set (PrimeSpectrum (MvPolynomial τ ℂ)), IsClosed T ∧
      closure ((MvPolynomial.pointToPoint (k := ℂ) : (τ → ℂ) → _) ⁻¹' S) =
        MvPolynomial.pointToPoint (k := ℂ) ⁻¹' T := by
  classical
  obtain ⟨C, rfl⟩ := PrimeSpectrum.exists_constructibleSetData_iff.mpr hS
  choose T hT he using fun c : PrimeSpectrum.BasicConstructibleSetData (MvPolynomial τ ℂ) =>
    exists_closed_closure_principalOpen (Ideal.span (Set.range c.g)) c.f
  refine ⟨⋃ c ∈ C, T c, C.finite_toSet.isClosed_biUnion (fun c _ => hT c), ?_⟩
  simp only [PrimeSpectrum.ConstructibleSetData.toSet, Set.preimage_iUnion]
  rw [C.closure_biUnion]
  simp only [pointToPoint_preimage_basicConstructible, he]

/-- Euclidean and polynomial closures agree on constructible complex-point traces. -/
theorem closure_constructible_eq_zeroLocus_vanishingIdeal {τ : Type*} [Finite τ]
    {S : Set (PrimeSpectrum (MvPolynomial τ ℂ))} (hS : Topology.IsConstructible S) :
    closure ((MvPolynomial.pointToPoint (k := ℂ) : (τ → ℂ) → _) ⁻¹' S) =
      MvPolynomial.zeroLocus ℂ (MvPolynomial.vanishingIdeal ℂ
        ((MvPolynomial.pointToPoint (k := ℂ) : (τ → ℂ) → _) ⁻¹' S)) := by
  obtain ⟨T, hT, he⟩ := exists_closed_closure_constructible hS
  obtain ⟨I, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal T).mp hT
  rw [pointToPoint_preimage_zeroLocus] at he
  apply Set.Subset.antisymm
  · exact closure_minimal (MvPolynomial.zeroLocus_vanishingIdeal_le _)
      (isClosed_zeroLocus _)
  · rw [he]
    exact MvPolynomial.zeroLocus_anti_mono
      (MvPolynomial.le_zeroLocus_iff_le_vanishingIdeal.mp (he ▸ subset_closure))

end BostConjecture.InvariantTheory
