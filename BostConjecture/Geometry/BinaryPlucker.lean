module

public import BostConjecture.Tensor.TwoFactors
public import BostConjecture.Geometry.PluckerNonvanishing

/-! # The binary Plücker action in the canonical finite-family tensor model -/

@[expose] public section

noncomputable section

namespace BostConjecture.Geometry

open Module InvariantTheory PiTensorProduct
open scoped TensorProduct

section Transport

variable {F : Type} [Field F] (E : Unit ⊕ Unit → Type*)
  [∀ i, AddCommGroup (E i)] [∀ i, Module F (E i)]

attribute [local instance] tensorTargetAddCommGroup

/-- The two-factor decomposition intertwines the actual independent SL actions. -/
theorem twoFactorEquiv_specialLinear (g : ∀ i, SpecialLinearGroup F (E i)) :
    (Tensor.twoFactorEquiv F E).toLinearMap ∘ₗ specialLinearTensorRepresentation F E g =
      tensorSpecialLinearRepresentation F (E (.inl ())) (E (.inr ()))
        (g (.inl ()), g (.inr ())) ∘ₗ (Tensor.twoFactorEquiv F E).toLinearMap :=
  Tensor.twoFactorEquiv_map (fun i => (g i : E i →ₗ[F] E i))

/-- A binary Plücker invariant pulls back to an actual finite-family invariant. -/
theorem twoFactor_plucker_invariant {s m : ℕ}
    {p : SymmetricAlgebra F (Dual F (⋀[F]^s (E (.inl ()) ⊗[F] E (.inr ()))))}
    (hp : p ∈ homogeneousInvariants
      (pluckerRepresentation F (E (.inl ())) (E (.inr ())) s) m) :
    polynomialPullback (exteriorPower.map s (Tensor.twoFactorEquiv F E).toLinearMap) p ∈
        homogeneousPolynomials F (⋀[F]^s (⨂[F] i, E i)) m ∧
      ∀ g, polynomialPullback (exteriorPower.map s
          (specialLinearTensorRepresentation F E g))
        (polynomialPullback (exteriorPower.map s
          (Tensor.twoFactorEquiv F E).toLinearMap) p) =
        polynomialPullback (exteriorPower.map s
          (Tensor.twoFactorEquiv F E).toLinearMap) p := by
  refine ⟨polynomialPullback_mem_homogeneous _ hp.1, ?_⟩
  intro g
  have hi := (mem_homogeneousInvariants_iff _ _ _).mp hp |>.2
    (g (.inl ()), g (.inr ()))
  change polynomialPullback
    (exteriorPower.map s (tensorSpecialLinearRepresentation F _ _
      (g (.inl ()), g (.inr ())))) p = p at hi
  have he := congrArg (exteriorPower.map s) (twoFactorEquiv_specialLinear E g)
  simp only [exteriorPower.map_comp] at he
  rw [← AlgHom.comp_apply, ← polynomialPullback_comp, he,
    polynomialPullback_comp, AlgHom.comp_apply, hi]

/-- The polynomial transported above has exactly the corresponding evaluation. -/
theorem twoFactor_plucker_eval {s : ℕ}
    (p : SymmetricAlgebra F (Dual F (⋀[F]^s (E (.inl ()) ⊗[F] E (.inr ())))))
    (x : Fin s → ⨂[F] i, E i) :
    polynomialEval (exteriorPower.ιMulti F s x)
      (polynomialPullback (exteriorPower.map s (Tensor.twoFactorEquiv F E).toLinearMap) p) =
        polynomialEval (exteriorPower.ιMulti F s (fun j => Tensor.twoFactorEquiv F E (x j))) p := by
  simp [Function.comp_def]

end Transport

section ScalarExtension

variable {R : Type*} [CommRing R] {F : Type} [Field F]
  [Algebra R F] [CharZero F] [IsAlgClosed F]
  {E : Unit ⊕ Unit → Type*} [∀ i, AddCommGroup (E i)] [∀ i, Module R (E i)]
  [∀ i, Module.Finite R (E i)] [∀ i, Module.Projective R (E i)]
  {V : Type*} [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Projective R V]

attribute [local instance] scalarExtendedTargetAddCommGroup

/-- The canonical binary Plücker invariant supplies the original-ring sequence
of actual finite-family determinant pairings. -/
theorem exists_canonicalPairing_nonzero_sequence_of_binary_invariant
    (A : V →ₗ[R] (⨂[R] i, E i)) {s m : ℕ} {a : Unit ⊕ Unit → ℕ}
    (hspos : 0 < s) (hapos : ∀ i, 0 < a i) (hm : 0 < m)
    (ha : ∀ i (q : PrimeSpectrum R), Module.rankAtStalk (Dual R (E i)) q = a i)
    (hs : ∀ q : PrimeSpectrum R, Module.rankAtStalk V q = s)
    (bV : Basis (Fin s) F (F ⊗[R] V))
    (bE : ∀ i, Basis (Fin (a i)) F (Dual F (F ⊗[R] E i)))
    {p : SymmetricAlgebra F
      (Dual F (⋀[F]^s ((F ⊗[R] E (.inl ())) ⊗[F] (F ⊗[R] E (.inr ())))))}
    (hp : p ∈ homogeneousInvariants
      (pluckerRepresentation F (F ⊗[R] E (.inl ())) (F ⊗[R] E (.inr ())) s) m)
    (hpA : polynomialEval (exteriorPower.ιMulti F s (fun j =>
      Tensor.twoFactorEquiv F (fun i => F ⊗[R] E i)
        (((Tensor.baseChangeEquiv R F E).toLinearMap ∘ₗ A.baseChange F) (bV j)))) p ≠ 0) :
    ∃ d₀ : ℕ, 0 < d₀ ∧ s ∣ d₀ ∧ (∀ i, a i ∣ d₀) ∧
      ∀ r : ℕ, 0 < r → ∃ (l : ℕ) (k : Unit ⊕ Unit → ℕ) (hl : 0 < l)
        (hk : ∀ i, 0 < k i)
        (t : ∀ i, OAI.Saxl.Tableau (d₀ * r) (Specht.rectangle (a i) (k i)))
        (v : OAI.Saxl.Tableau (d₀ * r) (Specht.rectangle s l)),
        canonicalPairing E hk t ha hl v hs A ≠ 0 := by
  obtain ⟨hq, hi⟩ := twoFactor_plucker_invariant (fun i => F ⊗[R] E i) hp
  apply exists_canonicalPairing_nonzero_sequence E A hspos hapos hm ha hs bV bE hq hi
  rwa [twoFactor_plucker_eval]

end ScalarExtension

end BostConjecture.Geometry
