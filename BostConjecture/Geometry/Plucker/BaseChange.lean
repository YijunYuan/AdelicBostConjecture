/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Geometry.Contraction.BaseChange
public import BostConjecture.Geometry.Plucker.Pairing

/-!
# Nonvanishing of the actual projective pairing by scalar extension

Nonvanishing of the scalar-extended projective pairing is detected on
integral generators. It therefore implies nonvanishing of the original
pairing over the coefficient ring.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Geometry

open Module PiTensorProduct
open scoped TensorProduct

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  {ι : Type*} [Fintype ι] (E : ι → Type*)
  [∀ i, AddCommGroup (E i)] [∀ i, Module R (E i)]
  [∀ i, Module.Finite R (E i)] [∀ i, Module.Projective R (E i)]
  {n : ℕ} {a k : ι → ℕ}
  (t : ∀ i, OAI.Saxl.Tableau n (Specht.rectangle (a i) (k i)))

local instance nonvanishingSourceFactorAddCommGroup : ∀ i, AddCommGroup
    ((⨂[R] (_ : Fin (k i)), ⋀[R]^(a i) (Dual R (E i))) ⊗[R]
      (R ⊗[ℤ] Specht.orbitLattice (t i))) := fun _ =>
        Module.addCommMonoidToAddCommGroup R

local instance nonvanishingSourceFactorModule : ∀ i, Module R
    ((⨂[R] (_ : Fin (k i)), ⋀[R]^(a i) (Dual R (E i))) ⊗[R]
      (R ⊗[ℤ] Specht.orbitLattice (t i))) := fun _ => inferInstance

local instance nonvanishingExtendedFactorAddCommGroup : ∀ i, AddCommGroup
    ((⨂[S] (_ : Fin (k i)), ⋀[S]^(a i) (Dual S (S ⊗[R] E i))) ⊗[S]
      (S ⊗[ℤ] Specht.orbitLattice (t i))) := fun _ =>
        Module.addCommMonoidToAddCommGroup S

local instance nonvanishingExtendedFactorModule : ∀ i, Module S
    ((⨂[S] (_ : Fin (k i)), ⋀[S]^(a i) (Dual S (S ⊗[R] E i))) ⊗[S]
      (S ⊗[ℤ] Specht.orbitLattice (t i))) := fun _ => inferInstance


variable (hk : ∀ i, 0 < k i)
  (ha : ∀ i (q : PrimeSpectrum R), Module.rankAtStalk (Dual R (E i)) q = a i)
  (haS : ∀ i (q : PrimeSpectrum S),
    Module.rankAtStalk (Dual S (S ⊗[R] E i)) q = a i)
  (b : ∀ i, Basis (Fin (a i)) S (Dual S (S ⊗[R] E i)))
  {V : Type*} [AddCommGroup V] [Module R V]
  [Module.Finite R V] [Module.Projective R V] {s l : ℕ}
  (hl : 0 < l) (v : OAI.Saxl.Tableau n (Specht.rectangle s l))
  (hs : ∀ q : PrimeSpectrum R, Module.rankAtStalk V q = s)
  (hsS : ∀ q : PrimeSpectrum S, Module.rankAtStalk (S ⊗[R] V) q = s)
  (bV : Basis (Fin s) S (S ⊗[R] V))

include b bV in
/-- Nonvanishing of the actual pairing after a free extension forces
nonvanishing over the original ring, with no faithfulness assumption. -/
theorem canonicalPairing_ne_zero_of_scalarExtension
    (A : V →ₗ[R] (⨂[R] i, E i))
    (h : canonicalPairing (fun i => S ⊗[R] E i) hk t haS hl v hsS
      ((Tensor.baseChangeEquiv R S E).toLinearMap ∘ₗ A.baseChange S) ≠ 0) :
    canonicalPairing E hk t ha hl v hs A ≠ 0 := by
  intro hzero
  apply h
  apply LinearMap.ext
  intro z
  apply LinearMap.ext
  intro u
  let e := determinantTwistBaseChangeEquiv (R := R) (S := S) (M := V)
    (Specht.orbitLattice v) l s
  have hdu := dualDeterminantTensorBaseChange_bijective (R := R) (S := S) E t
  -- Infer the preimage type before destructuring the existence proof.
  have hu_exists := hdu.2 u
  obtain ⟨u', hu⟩ := hu_exists
  have he := canonicalPairing_baseChange (R := R) (S := S) E hk t ha b hl v hs bV A
    (e.symm z) u'
  simp only [e, LinearEquiv.apply_symm_apply, hu] at he
  simp only [hzero, LinearMap.baseChange_zero, LinearMap.zero_apply,
    LinearMap.map_zero] at he
  simpa only [canonicalPairing_apply, dualDeterminantMap, LinearMap.comp_apply,
    LinearEquiv.coe_coe, projectiveDeterminantMap_eq_free hl v hsS bV,
    fun i => projectiveDeterminantMap_eq_free (hk i) (t i) (haS i) (b i),
    LinearMap.zero_apply] using he.symm

section AlgebraicallyClosed

variable {F : Type} [Field F] [CharZero F] [IsAlgClosed F] [Algebra R F]

local instance scalarExtendedTargetAddCommGroup : AddCommGroup (⨂[F] i, F ⊗[R] E i) :=
  Module.addCommMonoidToAddCommGroup F

/-- An actual invariant at a scalar-extended map detects the original
canonical projective determinant pairing. -/
theorem canonicalPairing_ne_zero_of_baseChange_invariant
    (hspos : 0 < s) (hapos : ∀ i, 0 < a i)
    (b : ∀ i, Basis (Fin (a i)) F (Dual F (F ⊗[R] E i)))
    (bV : Basis (Fin s) F (F ⊗[R] V))
    (A : V →ₗ[R] (⨂[R] i, E i))
    {p : SymmetricAlgebra F (Dual F ((F ⊗[R] V) →ₗ[F] (⨂[F] i, F ⊗[R] E i)))}
    (hp : p ∈ InvariantTheory.homogeneousInvariants
      (homSpecialLinearRepresentation
        (specialLinearTensorRepresentation F (fun i => F ⊗[R] E i))) n)
    (hpA : InvariantTheory.polynomialEval
      ((Tensor.baseChangeEquiv R F E).toLinearMap ∘ₗ A.baseChange F) p ≠ 0) :
    canonicalPairing E hk t ha hl v hs A ≠ 0 := by
  have haF (i) (q : PrimeSpectrum F) :
      Module.rankAtStalk (Dual F (F ⊗[R] E i)) q = a i := by
    simp [Module.rankAtStalk_eq_finrank_of_free, Module.finrank_eq_card_basis (b i)]
  have hsF (q : PrimeSpectrum F) : Module.rankAtStalk (F ⊗[R] V) q = s := by
    simp [Module.rankAtStalk_eq_finrank_of_free, Module.finrank_eq_card_basis bV]
  apply canonicalPairing_ne_zero_of_scalarExtension (S := F) E t hk ha haF b hl v hs hsF bV A
  exact canonicalPairing_ne_zero_of_invariant _ hspos hapos hl hk t v haF hsF bV b hp hpA

end AlgebraicallyClosed

end BostConjecture.Geometry
