module

public import BostConjecture.Geometry.PluckerPolarization
public import BostConjecture.Geometry.NonvanishingBaseChange

/-! # Plücker invariants detect the original canonical determinant pairing -/

@[expose] public section

noncomputable section

namespace BostConjecture.Geometry

open Module InvariantTheory PiTensorProduct
open scoped TensorProduct

variable {R : Type*} [CommRing R] {F : Type} [Field F] [CharZero F] [IsAlgClosed F]
  [Algebra R F] {ι : Type*} [Fintype ι] (E : ι → Type*)
  [∀ i, AddCommGroup (E i)] [∀ i, Module R (E i)]
  [∀ i, Module.Finite R (E i)] [∀ i, Module.Projective R (E i)]
  {V : Type*} [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Projective R V]

attribute [local instance] scalarExtendedTargetAddCommGroup

/-- Every compatible rectangular degree of a Plücker-invariant power detects
the actual determinant pairing over the original coefficient ring. -/
theorem canonicalPairing_ne_zero_of_plucker_invariant
    (A : V →ₗ[R] (⨂[R] i, E i)) {n s l m r : ℕ} {a k : ι → ℕ}
    (hspos : 0 < s) (hapos : ∀ i, 0 < a i) (hl : 0 < l) (hk : ∀ i, 0 < k i)
    (t : ∀ i, OAI.Saxl.Tableau n (Specht.rectangle (a i) (k i)))
    (v : OAI.Saxl.Tableau n (Specht.rectangle s l))
    (ha : ∀ i (q : PrimeSpectrum R), Module.rankAtStalk (Dual R (E i)) q = a i)
    (hs : ∀ q : PrimeSpectrum R, Module.rankAtStalk V q = s)
    (bV : Basis (Fin s) F (F ⊗[R] V))
    (bE : ∀ i, Basis (Fin (a i)) F (Dual F (F ⊗[R] E i)))
    {p : SymmetricAlgebra F (Dual F (⋀[F]^s (⨂[F] i, F ⊗[R] E i)))}
    (hp : p ∈ homogeneousPolynomials F (⋀[F]^s (⨂[F] i, F ⊗[R] E i)) m)
    (hi : ∀ g, polynomialPullback (exteriorPower.map s
      (specialLinearTensorRepresentation F (fun i => F ⊗[R] E i) g)) p = p)
    (hpA : polynomialEval (exteriorPower.ιMulti F s (fun j =>
      ((Tensor.baseChangeEquiv R F E).toLinearMap ∘ₗ A.baseChange F) (bV j))) p ≠ 0)
    (hn : (s * m) * r = n) : canonicalPairing E hk t ha hl v hs A ≠ 0 := by
  have hq := homogeneousInvariants_pow _
    (pluckerPolynomialPullback_mem_invariants
      (specialLinearTensorRepresentation F (fun i => F ⊗[R] E i)) bV hp hi) r
  rw [hn] at hq
  apply canonicalPairing_ne_zero_of_baseChange_invariant E t hk ha hl v hs hspos hapos
    bE bV A hq
  simpa only [map_pow] using
    pow_ne_zero r (polynomialEval_pluckerPolynomialPullback_ne_zero bV hpA)

/-- An actual positive-degree Plücker invariant gives nonzero original
canonical pairings at every positive multiple of one common rectangular degree. -/
theorem exists_canonicalPairing_nonzero_sequence
    (A : V →ₗ[R] (⨂[R] i, E i)) {s m : ℕ} {a : ι → ℕ}
    (hspos : 0 < s) (hapos : ∀ i, 0 < a i) (hm : 0 < m)
    (ha : ∀ i (q : PrimeSpectrum R), Module.rankAtStalk (Dual R (E i)) q = a i)
    (hs : ∀ q : PrimeSpectrum R, Module.rankAtStalk V q = s)
    (bV : Basis (Fin s) F (F ⊗[R] V))
    (bE : ∀ i, Basis (Fin (a i)) F (Dual F (F ⊗[R] E i)))
    {p : SymmetricAlgebra F (Dual F (⋀[F]^s (⨂[F] i, F ⊗[R] E i)))}
    (hp : p ∈ homogeneousPolynomials F (⋀[F]^s (⨂[F] i, F ⊗[R] E i)) m)
    (hi : ∀ g, polynomialPullback (exteriorPower.map s
      (specialLinearTensorRepresentation F (fun i => F ⊗[R] E i) g)) p = p)
    (hpA : polynomialEval (exteriorPower.ιMulti F s (fun j =>
      ((Tensor.baseChangeEquiv R F E).toLinearMap ∘ₗ A.baseChange F) (bV j))) p ≠ 0) :
    ∃ d₀ : ℕ, 0 < d₀ ∧ s ∣ d₀ ∧ (∀ i, a i ∣ d₀) ∧
      ∀ r : ℕ, 0 < r → ∃ (l : ℕ) (k : ι → ℕ) (hl : 0 < l) (hk : ∀ i, 0 < k i)
        (t : ∀ i, OAI.Saxl.Tableau (d₀ * r) (Specht.rectangle (a i) (k i)))
        (v : OAI.Saxl.Tableau (d₀ * r) (Specht.rectangle s l)),
        canonicalPairing E hk t ha hl v hs A ≠ 0 := by
  classical
  let P := ∏ i, a i
  have hP : 0 < P := Finset.prod_pos (fun i _ => hapos i)
  let d₀ := (s * m) * P
  have hd : 0 < d₀ := Nat.mul_pos (Nat.mul_pos hspos hm) hP
  have hsd : s ∣ d₀ := ⟨m * P, by dsimp [d₀]; ac_rfl⟩
  have had (i) : a i ∣ d₀ :=
    (Finset.dvd_prod_of_mem a (Finset.mem_univ i)).trans
      ⟨s * m, by dsimp [d₀, P]; ac_rfl⟩
  refine ⟨d₀, hd, hsd, had, ?_⟩
  intro r hr
  have hn : 0 < d₀ * r := Nat.mul_pos hd hr
  obtain ⟨l, hlEq⟩ := hsd.trans (show d₀ ∣ d₀ * r from ⟨r, rfl⟩)
  have hl : 0 < l := Nat.pos_of_mul_pos_left (hlEq ▸ hn)
  have hkex (i) : a i ∣ d₀ * r := had i |>.trans ⟨r, rfl⟩
  choose k hkEq using hkex
  have hk (i) : 0 < k i := Nat.pos_of_mul_pos_left (hkEq i ▸ hn)
  let t i : OAI.Saxl.Tableau (d₀ * r) (Specht.rectangle (a i) (k i)) :=
    (finCongr (hkEq i)).trans (Specht.rectangleTableau (a i) (k i))
  let v : OAI.Saxl.Tableau (d₀ * r) (Specht.rectangle s l) :=
    (finCongr hlEq).trans (Specht.rectangleTableau s l)
  refine ⟨l, k, hl, hk, t, v, ?_⟩
  apply canonicalPairing_ne_zero_of_plucker_invariant E A hspos hapos hl hk t v ha hs
    bV bE hp hi hpA (r := P * r)
  dsimp [d₀]
  exact (Nat.mul_assoc _ _ _).symm

end BostConjecture.Geometry
