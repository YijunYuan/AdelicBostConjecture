/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.RingTheory.AdjoinRoot

/-!
# Lifting roots along integral finite-type extensions

The lifting argument uses the actual minimal polynomial over an integrally
closed domain. Its evaluation kernel describes the generated subalgebra;
lying over and the weak Nullstellensatz then extend its closed points.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.InvariantTheory

/-- A closed point of a subalgebra lifts through an integral finite-type extension. -/
theorem exists_algHom_extends_of_isIntegral {K B : Type*} [Field K] [IsAlgClosed K]
    [CommRing B] [Algebra K B] [Algebra.FiniteType K B]
    (A : Subalgebra K B) [Algebra.IsIntegral A B] (φ : A →ₐ[K] K) :
    ∃ ψ : B →ₐ[K] K, ψ.comp A.val = φ := by
  let P := RingHom.ker φ
  have hsurj : Function.Surjective φ := fun c => ⟨algebraMap K A c, φ.commutes c⟩
  have : P.IsMaximal := RingHom.ker_isMaximal_of_surjective φ hsurj
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := B) P (by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp Subtype.val_injective]
    exact bot_le)
  have := hQ
  let : Field (B ⧸ Q) := Ideal.Quotient.field Q
  have : Module.Finite K (B ⧸ Q) := finite_of_finite_type_of_isJacobsonRing K (B ⧸ Q)
  let χ : (B ⧸ Q) →ₐ[K] K := IsAlgClosed.lift
  refine ⟨χ.comp (Ideal.Quotient.mkₐ K Q), ?_⟩
  ext x
  have hx : x - algebraMap K A (φ x) ∈ P := by
    change φ (x - algebraMap K A (φ x)) = 0
    simp
  rw [← hQP] at hx
  have hzero : Ideal.Quotient.mk Q ((x : B) - algebraMap K B (φ x)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hx
  have h := congrArg χ hzero
  change χ (Ideal.Quotient.mk Q (x : B)) = φ x
  simpa only [map_sub, map_zero, ← Ideal.Quotient.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply K B (B ⧸ Q), χ.commutes,
    Algebra.algebraMap_self, RingHom.id_apply, sub_eq_zero] using h

/-- A root of the specialized actual minimal polynomial lifts to a point of the algebra. -/
theorem exists_algHom_of_minpoly_eq_zero {K R B : Type*}
    [Field K] [IsAlgClosed K] [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing B] [IsDomain B] [Algebra K R] [Algebra K B] [Algebra R B]
    [IsScalarTower K R B] [Module.IsTorsionFree R B]
    [Algebra.IsIntegral R B] [Algebra.FiniteType K B]
    (u : B) (χ : R →ₐ[K] K) (z : K)
    (hz : (minpoly R u).eval₂ χ.toRingHom z = 0) :
    ∃ ψ : B →ₐ[K] K, (∀ r : R, ψ (algebraMap R B r) = χ r) ∧ ψ u = z := by
  let A := (Polynomial.aeval u : Polynomial R →ₐ[R] B).range
  let e : Polynomial R →ₐ[K] A := (Polynomial.aeval u).rangeRestrict.restrictScalars K
  let f : Polynomial R →ₐ[K] K := Polynomial.eval₂AlgHom χ z (fun _ => Commute.all _ _)
  have hu : IsIntegral R u := Algebra.IsIntegral.isIntegral u
  have hk : RingHom.ker e.toRingHom ≤ RingHom.ker f.toRingHom := by
    have hker : RingHom.ker e.toRingHom = RingHom.ker (Polynomial.aeval u).toRingHom := by
      ext p
      change e p = 0 ↔ Polynomial.aeval u p = 0
      exact Subtype.ext_iff
    simpa only [hker, minpoly.ker_eval hu] using Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hz)
  let φ : A →ₐ[K] K := AlgHom.liftOfSurjective e
    (Polynomial.aeval u).rangeRestrict_surjective f hk
  have hφ (p : Polynomial R) : φ (e p) = f p :=
    AlgHom.liftOfSurjective_apply e _ f hk p
  have : Algebra.IsIntegral A B := Algebra.IsIntegral.tower_top (R := R)
  have : Algebra.IsIntegral (A.restrictScalars K) B :=
    inferInstanceAs (Algebra.IsIntegral A B)
  obtain ⟨ψ, hψ⟩ := exists_algHom_extends_of_isIntegral (A.restrictScalars K) φ
  have hψe (p : Polynomial R) : ψ (Polynomial.aeval u p) = f p :=
    (DFunLike.congr_fun hψ (e p)).trans (hφ p)
  refine ⟨ψ, fun r => ?_, ?_⟩
  · simpa [f] using hψe (Polynomial.C r)
  · simpa [f] using hψe Polynomial.X

end BostConjecture.InvariantTheory
