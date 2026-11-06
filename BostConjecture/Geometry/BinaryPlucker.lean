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

end BostConjecture.Geometry
