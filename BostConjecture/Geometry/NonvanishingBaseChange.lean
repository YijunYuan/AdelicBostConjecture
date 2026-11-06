module

public import BostConjecture.Geometry.ContractionBaseChange
public import BostConjecture.Geometry.Nonvanishing

/-! # Nonvanishing of the actual projective pairing by scalar extension -/

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

local instance : ∀ i, AddCommGroup
    ((⨂[R] (_ : Fin (k i)), ⋀[R]^(a i) (Dual R (E i))) ⊗[R]
      (R ⊗[ℤ] Specht.orbitLattice (t i))) := fun _ =>
        Module.addCommMonoidToAddCommGroup R

local instance : ∀ i, Module R
    ((⨂[R] (_ : Fin (k i)), ⋀[R]^(a i) (Dual R (E i))) ⊗[R]
      (R ⊗[ℤ] Specht.orbitLattice (t i))) := fun _ => inferInstance

local instance : ∀ i, AddCommGroup
    ((⨂[S] (_ : Fin (k i)), ⋀[S]^(a i) (Dual S (S ⊗[R] E i))) ⊗[S]
      (S ⊗[ℤ] Specht.orbitLattice (t i))) := fun _ =>
        Module.addCommMonoidToAddCommGroup S

local instance : ∀ i, Module S
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
set_option maxHeartbeats 800000 in
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
  simp only [LinearMap.zero_apply]
  let e := determinantTwistBaseChangeEquiv (R := R) (S := S) (M := V)
    (Specht.orbitLattice v) l s
  let z' := e.symm z
  have hz : e z' = z := e.apply_symm_apply z
  obtain ⟨u', hu⟩ := (dualDeterminantTensorBaseChange_bijective (S := S) E t).surjective u
  have he := canonicalPairing_baseChange E hk t ha b hl v hs bV A z' u'
  rw [hz, hu] at he
  simp only [canonicalPairing_apply, dualDeterminantMap, LinearMap.comp_apply,
    LinearEquiv.coe_coe, projectiveDeterminantMap_eq_free hl v hsS bV,
    fun i => projectiveDeterminantMap_eq_free (hk i) (t i) (haS i) (b i)]
  have hf := congrArg (fun f => (LinearMap.baseChange S f) z') hzero
  simp only [LinearMap.baseChange_zero, LinearMap.zero_apply] at hf
  rw [hf, map_zero, LinearMap.zero_apply] at he
  exact he.symm

end BostConjecture.Geometry
