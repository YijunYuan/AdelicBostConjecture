/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.InvariantTheory.ComplexClosure.Normalization
public import Mathlib.RingTheory.Spectrum.Prime.Chevalley

/-!
# Constructibility of polynomial images on complex points

Chevalley's theorem on prime spectra is transported to the canonical closed
points of affine space using the weak Nullstellensatz.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.InvariantTheory

/-- A closed affine point belongs to a spectral image precisely when its character lifts. -/
theorem pointToPoint_mem_range_comap_iff {K σ B : Type*} [Field K] [IsAlgClosed K]
    [CommRing B] [Algebra K B] [Algebra.FiniteType K B]
    (f : MvPolynomial σ K →ₐ[K] B) (a : σ → K) :
    MvPolynomial.pointToPoint (k := K) a ∈ Set.range (PrimeSpectrum.comap f.toRingHom) ↔
      ∃ ψ : B →ₐ[K] K, ψ.comp f = MvPolynomial.aeval a := by
  constructor
  · rintro ⟨P, hP⟩
    obtain ⟨Q, hQ, hPQ⟩ := Ideal.exists_le_maximal P.asIdeal P.isPrime.ne_top
    have := hQ
    let : Field (B ⧸ Q) := Ideal.Quotient.field Q
    have : Module.Finite K (B ⧸ Q) := finite_of_finite_type_of_isJacobsonRing K (B ⧸ Q)
    let χ : (B ⧸ Q) →ₐ[K] K := IsAlgClosed.lift
    let ψ : B →ₐ[K] K := χ.comp (Ideal.Quotient.mkₐ K Q)
    refine ⟨ψ, ?_⟩
    ext i
    have hm : MvPolynomial.X i - MvPolynomial.C (a i) ∈
        (MvPolynomial.pointToPoint (k := K) a).asIdeal := by
      rw [MvPolynomial.pointToPoint, MvPolynomial.mem_vanishingIdeal_singleton_iff]
      simp
    rw [← hP] at hm
    have hzero : Ideal.Quotient.mk Q (f (MvPolynomial.X i - MvPolynomial.C (a i))) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (hPQ hm)
    have h := congrArg χ hzero
    rw [map_zero] at h
    have hψ : ψ (f (MvPolynomial.X i)) = a i := by
      change ψ (f (MvPolynomial.X i - MvPolynomial.C (a i))) = 0 at h
      simpa [sub_eq_zero] using h
    simpa only [AlgHom.comp_apply, MvPolynomial.aeval_X] using hψ
  · rintro ⟨ψ, hψ⟩
    refine ⟨⟨RingHom.ker ψ.toRingHom, RingHom.ker_isPrime _⟩, ?_⟩
    apply PrimeSpectrum.ext
    ext p
    change ψ (f p) = 0 ↔ p ∈ MvPolynomial.vanishingIdeal K {a}
    rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
    exact (congrArg (fun h : MvPolynomial σ K →ₐ[K] K => h p = 0) hψ).to_iff

/-- The closed points in the spectral image are exactly the actual polynomial image. -/
theorem polynomial_image_eq_preimage_range_comap {K σ τ : Type*}
    [Field K] [IsAlgClosed K] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) (q : τ → MvPolynomial σ K) :
    (fun x : σ → K => fun i => MvPolynomial.eval x (q i)) '' MvPolynomial.zeroLocus K I =
      MvPolynomial.pointToPoint (k := K) ⁻¹'
        Set.range (PrimeSpectrum.comap
          ((Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval q)).toRingHom) := by
  ext a
  rw [Set.mem_preimage, pointToPoint_mem_range_comap_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    change ∀ p ∈ I, MvPolynomial.aeval x p = 0 at hx
    refine ⟨Ideal.Quotient.liftₐ I (MvPolynomial.aeval x) hx, ?_⟩
    rw [← AlgHom.comp_assoc, Ideal.Quotient.liftₐ_comp I (MvPolynomial.aeval x) hx]
    ext i
    simp
  · rintro ⟨ψ, hψ⟩
    obtain ⟨x, hx, he⟩ := exists_point_of_quotient_algHom I ψ
    refine ⟨x, hx, funext fun i => ?_⟩
    have h := DFunLike.congr_fun hψ (MvPolynomial.X i)
    simpa only [AlgHom.comp_apply, MvPolynomial.aeval_X, Ideal.Quotient.mkₐ_eq_mk,
      he] using h

/-- Polynomial images of affine zero loci are closed-point traces of constructible sets. -/
theorem exists_constructible_polynomial_image {K σ τ : Type*}
    [Field K] [IsAlgClosed K] [Finite σ] [Finite τ]
    (I : Ideal (MvPolynomial σ K)) (q : τ → MvPolynomial σ K) :
    ∃ S : Set (PrimeSpectrum (MvPolynomial τ K)), Topology.IsConstructible S ∧
      (fun x : σ → K => fun i => MvPolynomial.eval x (q i)) '' MvPolynomial.zeroLocus K I =
        MvPolynomial.pointToPoint (k := K) ⁻¹' S := by
  let R := MvPolynomial τ K
  let B := MvPolynomial σ K ⧸ I
  let f : R →ₐ[K] B := (Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval q)
  let : Algebra R B := f.toRingHom.toAlgebra
  have : IsScalarTower K R B := IsScalarTower.of_algHom f
  have : Algebra.FiniteType R B := Algebra.FiniteType.of_restrictScalars_finiteType K R B
  have : Algebra.FinitePresentation R B := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  refine ⟨Set.range (PrimeSpectrum.comap f.toRingHom), ?_,
    polynomial_image_eq_preimage_range_comap I q⟩
  exact PrimeSpectrum.isConstructible_range_comap
    (RingHom.finitePresentation_algebraMap.mpr inferInstance)

end BostConjecture.InvariantTheory
