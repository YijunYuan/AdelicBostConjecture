/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Geometry.Descent.Frames
public import BostConjecture.Geometry.Descent.Localization
public import BostConjecture.Geometry.Determinant.Tower
public import Mathlib.RingTheory.Flat.Localization

/-!
# Determinant-twisted tensor realization for finite projective modules

The frame-independent local inclusions agree over the tensor product of any
two coefficient rings. Principal-cover descent constructs their global map
on the intrinsic exterior-power and tensor-product modules.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Geometry

open Module
open scoped TensorProduct

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n a k : ℕ}

/-- Any two determinant charts agree after passing to the tensor product of
their coefficient rings. -/
theorem determinantChart_overlap {S T : Type*} [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (hk : 0 < k)
    (t : OAI.Saxl.Tableau n (Specht.rectangle a k))
    (b : Basis (Fin a) S (S ⊗[R] M)) (c : Basis (Fin a) T (T ⊗[R] M))
    (p : (⨂[R] (_ : Fin k), ⋀[R]^a M) ⊗[R] (R ⊗[ℤ] Specht.orbitLattice t)) :
    TensorProduct.map (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T).toLinearMap
      LinearMap.id (determinantChart hk t b (1 ⊗ₜ[R] p)) =
    TensorProduct.map (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).toLinearMap
      LinearMap.id (determinantChart hk t c (1 ⊗ₜ[R] p)) := by
  let : Algebra T (S ⊗[R] T) := Algebra.TensorProduct.rightAlgebra
  let d := (b.baseChange (S ⊗[R] T)).map
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R S (S ⊗[R] T) (S ⊗[R] T) M)
  exact (determinantChart_trans hk t b d p).trans (determinantChart_trans hk t c d p).symm

/-- A finite principal family of actual determinant charts descends uniquely. -/
theorem existsUnique_determinantMap_of_frames (hk : 0 < k)
    (t : OAI.Saxl.Tableau n (Specht.rectangle a k))
    (s : Set R) [Finite s] (hs : Ideal.span s = ⊤)
    (b : ∀ i : s, Basis (Fin a) (Localization.Away (i : R))
      (Localization.Away (i : R) ⊗[R] M)) :
    ∃! U : (⨂[R] (_ : Fin k), ⋀[R]^a M) ⊗[R] (R ⊗[ℤ] Specht.orbitLattice t) →ₗ[R]
      (⨂[R] (_ : Fin n), M),
      ∀ i : s, U.baseChange (Localization.Away (i : R)) = determinantChart hk t (b i) := by
  let P := (⨂[R] (_ : Fin k), ⋀[R]^a M) ⊗[R] (R ⊗[ℤ] Specht.orbitLattice t)
  let Q := ⨂[R] (_ : Fin n), M
  have hex (p : P) : ∃ q : Q, ∀ i : s,
      (1 : Localization.Away (i : R)) ⊗ₜ[R] q = determinantChart hk t (b i) (1 ⊗ₜ[R] p) :=
    (existsUnique_of_tensorLocalization_compatible s hs
      (fun i => determinantChart hk t (b i) (1 ⊗ₜ[R] p))
      (fun i j => determinantChart_overlap hk t (b i) (b j) p)).exists
  choose g hg using hex
  let loc (i : s) := TensorProduct.mk R (Localization.Away (i : R)) Q 1
  let U : P →ₗ[R] Q :=
    { toFun := g
      map_add' := by
        intro p q
        apply Module.eq_of_isLocalized_span s hs _ loc
        intro i
        simp only [loc, TensorProduct.mk_apply, hg, map_add, TensorProduct.tmul_add]
      map_smul' := by
        intro r p
        apply Module.eq_of_isLocalized_span s hs _ loc
        intro i
        simp only [loc, TensorProduct.mk_apply, hg, TensorProduct.tmul_smul,
          LinearMap.map_smul_of_tower, RingHom.id_apply] }
  have hU (i : s) : U.baseChange (Localization.Away (i : R)) = determinantChart hk t (b i) := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro r p
    change r ⊗ₜ[R] g p = determinantChart hk t (b i) (r ⊗ₜ[R] p)
    rw [TensorProduct.tmul_eq_smul_one_tmul r (g p), hg,
      TensorProduct.tmul_eq_smul_one_tmul r p, map_smul]
  refine ⟨U, hU, ?_⟩
  intro V hV
  apply LinearMap.ext
  intro p
  apply Module.eq_of_isLocalized_span s hs _ loc
  intro i
  change (1 : Localization.Away (i : R)) ⊗ₜ[R] V p = 1 ⊗ₜ[R] g p
  rw [hg]
  exact LinearMap.congr_fun (hV i) (1 ⊗ₜ[R] p)

/-- A map recovered from one principal cover has the prescribed formula in
every frame after any coefficient extension. -/
theorem determinantMap_baseChange_of_frames {S : Type*} [CommRing S] [Algebra R S]
    (hk : 0 < k)
    (t : OAI.Saxl.Tableau n (Specht.rectangle a k))
    (s : Set R) [Finite s] (hs : Ideal.span s = ⊤)
    (b : ∀ i : s, Basis (Fin a) (Localization.Away (i : R))
      (Localization.Away (i : R) ⊗[R] M))
    (U : (⨂[R] (_ : Fin k), ⋀[R]^a M) ⊗[R] (R ⊗[ℤ] Specht.orbitLattice t) →ₗ[R]
      (⨂[R] (_ : Fin n), M))
    (hU : ∀ i : s, U.baseChange (Localization.Away (i : R)) = determinantChart hk t (b i))
    (c : Basis (Fin a) S (S ⊗[R] M)) :
    U.baseChange S = determinantChart hk t c := by
  let Q := ⨂[R] (_ : Fin n), M
  have h (p) : (1 : S) ⊗ₜ[R] U p = determinantChart hk t c (1 ⊗ₜ[R] p) := by
    let loc (i : s) := TensorProduct.map
      (TensorProduct.mk R (Localization.Away (i : R)) (S) 1)
      (LinearMap.id : Q →ₗ[R] Q)
    let (i : s) : IsLocalizedModule (Submonoid.powers (i : R)) (loc i) :=
      IsLocalizedModule.rTensor (R := R) (A := R) (N := Q) (S := Submonoid.powers (i : R))
        (TensorProduct.mk R (Localization.Away (i : R)) (S) 1)
    apply Module.eq_of_isLocalized_span s hs _ loc
    intro i
    have hi := LinearMap.congr_fun (hU i) (1 ⊗ₜ[R] p)
    change (1 : Localization.Away (i : R)) ⊗ₜ[R] U p =
      determinantChart hk t (b i) (1 ⊗ₜ[R] p) at hi
    have hi' := congrArg (TensorProduct.map (Algebra.TensorProduct.includeLeft :
      Localization.Away (i : R) →ₐ[R]
        Localization.Away (i : R) ⊗[R] S).toLinearMap
      (LinearMap.id : Q →ₗ[R] Q)) hi
    exact hi'.trans (determinantChart_overlap hk t (b i) c p)
  apply TensorProduct.AlgebraTensorModule.ext
  intro r p
  change r ⊗ₜ[R] U p = determinantChart hk t c (r ⊗ₜ[R] p)
  rw [TensorProduct.tmul_eq_smul_one_tmul r (U p), h,
    TensorProduct.tmul_eq_smul_one_tmul r p, map_smul]

variable [Module.Finite R M] [Module.Projective R M]

/-- The global map is characterized intrinsically by its formula in every
principal frame; finite projectivity produces all the required charts. -/
theorem existsUnique_projectiveDeterminantMap (hk : 0 < k)
    (t : OAI.Saxl.Tableau n (Specht.rectangle a k))
    (ha : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = a) :
    ∃! U : (⨂[R] (_ : Fin k), ⋀[R]^a M) ⊗[R] (R ⊗[ℤ] Specht.orbitLattice t) →ₗ[R]
      (⨂[R] (_ : Fin n), M),
      ∀ (f : R) (b : Basis (Fin a) (Localization.Away f) (Localization.Away f ⊗[R] M)),
        U.baseChange (Localization.Away f) = determinantChart hk t b := by
  obtain ⟨s, hs, hb⟩ := exists_finite_principal_frames ha
  let b (i : (s : Set R)) := (hb i i.property).some
  obtain ⟨U, hU, hUnique⟩ := existsUnique_determinantMap_of_frames hk t (s : Set R) hs b
  refine ⟨U, fun f c => determinantMap_baseChange_of_frames hk t (s : Set R) hs b U hU c, ?_⟩
  exact fun V hV => hUnique V (fun i => hV i (b i))

/-- The canonical determinant-twisted map of a finite projective constant-rank module. -/
def projectiveDeterminantMap (hk : 0 < k)
    (t : OAI.Saxl.Tableau n (Specht.rectangle a k))
    (ha : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = a) :
    (⨂[R] (_ : Fin k), ⋀[R]^a M) ⊗[R] (R ⊗[ℤ] Specht.orbitLattice t) →ₗ[R]
      (⨂[R] (_ : Fin n), M) :=
  (existsUnique_projectiveDeterminantMap hk t ha).choose

/-- Every principal trivialization recovers the actual free determinant inclusion. -/
theorem projectiveDeterminantMap_baseChange (hk : 0 < k)
    (t : OAI.Saxl.Tableau n (Specht.rectangle a k))
    (ha : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = a)
    (f : R) (b : Basis (Fin a) (Localization.Away f) (Localization.Away f ⊗[R] M)) :
    (projectiveDeterminantMap hk t ha).baseChange (Localization.Away f) =
      determinantChart hk t b :=
  (existsUnique_projectiveDeterminantMap hk t ha).choose_spec.1 f b

/-- The global map recovers the free inclusion after any coefficient extension
on which the original module becomes free, including generic and complex fibers. -/
theorem projectiveDeterminantMap_baseChange_of_basis {S : Type*} [CommRing S] [Algebra R S]
    (hk : 0 < k) (t : OAI.Saxl.Tableau n (Specht.rectangle a k))
    (ha : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = a)
    (c : Basis (Fin a) S (S ⊗[R] M)) :
    (projectiveDeterminantMap hk t ha).baseChange S = determinantChart hk t c := by
  obtain ⟨s, hs, hb⟩ := exists_finite_principal_frames ha
  let b (i : (s : Set R)) := (hb i i.property).some
  exact determinantMap_baseChange_of_frames hk t (s : Set R) hs b
    (projectiveDeterminantMap hk t ha)
    (fun i => projectiveDeterminantMap_baseChange hk t ha i (b i)) c

/-- This paper, Lemma 6.1, injectivity of the canonical determinant–Specht map.

Flatness over the integers preserves the integral lattice inclusion in
every chart, hence also globally. No freeness over `R` is assumed. -/
theorem projectiveDeterminantMap_injective [Module.Flat ℤ R] (hk : 0 < k)
    (t : OAI.Saxl.Tableau n (Specht.rectangle a k))
    (ha : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = a) :
    Function.Injective (projectiveDeterminantMap hk t ha) := by
  intro p q hpq
  obtain ⟨s, hs, hb⟩ := exists_finite_principal_frames ha
  apply Module.eq_of_isLocalized_span (s : Set R) hs _
    (fun i => TensorProduct.mk R (Localization.Away (i : R)) _ 1)
  intro i
  let b := (hb i i.property).some
  let : Module.Flat ℤ (Localization.Away (i : R)) := Module.Flat.trans ℤ R _
  apply determinantChart_injective hk t b
  rw [← projectiveDeterminantMap_baseChange hk t ha i b]
  change (1 : Localization.Away (i : R)) ⊗ₜ[R] projectiveDeterminantMap hk t ha p =
    1 ⊗ₜ[R] projectiveDeterminantMap hk t ha q
  rw [hpq]

end BostConjecture.Geometry
