module

public import BostConjecture.Geometry.PluckerPolynomial
public import BostConjecture.Geometry.PolynomialPolarization
public import BostConjecture.InvariantTheory.PluckerAction
public import Mathlib.Algebra.CharZero.Infinite

/-! # Invariant Hom tensors from actual Plücker invariants

The actual Plücker pullback feeds the normalized symmetric tensor lift.
All powers retain nonzero evaluation. This does not yet identify the
regrouped tensors with rectangular determinant-isotypic factors.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Geometry

open Module PiTensorProduct InvariantTheory exteriorPower
open scoped TensorProduct

variable {F : Type} [Field F] {X : Type*} [AddCommGroup X] [Module F X]

/-- Powers multiply the intrinsic homogeneous degree. -/
theorem homogeneousPolynomials_pow {d : ℕ}
    {p : SymmetricAlgebra F (Dual F X)}
    (hp : p ∈ homogeneousPolynomials F X d) (r : ℕ) :
    p ^ r ∈ homogeneousPolynomials F X (d * r) := by
  induction r with
  | zero => simp [homogeneousPolynomials]
  | succ r ih =>
    rw [pow_succ', Nat.mul_succ, Nat.add_comm, homogeneousPolynomials, pow_add]
    exact Submodule.mul_mem_mul hp ih

/-- Homogeneous invariants remain invariant under taking powers. -/
theorem homogeneousInvariants_pow {G : Type*} [Group G]
    (ρ : Representation F G X) {d : ℕ}
    {p : SymmetricAlgebra F (Dual F X)}
    (hp : p ∈ homogeneousInvariants ρ d) (r : ℕ) :
    p ^ r ∈ homogeneousInvariants ρ (d * r) := by
  apply (mem_homogeneousInvariants_iff _ _ _).mpr
  refine ⟨homogeneousPolynomials_pow hp.1 r, ?_⟩
  intro g
  rw [map_pow, (mem_homogeneousInvariants_iff _ _ _).mp hp |>.2 g]

variable {V : Type*} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] [FiniteDimensional F X] [CharZero F]

/-- Actual invariant tensor detection in every multiple of the pulled-back
degree, with the canonical tensor-duality evaluation. -/
theorem exists_plucker_invariant_tensor {G : Type*} [Group G]
    (ρ : Representation F G X) {s m : ℕ} (b : Basis (Fin s) F V)
    {p : SymmetricAlgebra F (Dual F (⋀[F]^s X))}
    (hp : p ∈ homogeneousPolynomials F (⋀[F]^s X) m)
    (hi : ∀ g, polynomialPullback (exteriorPower.map s (ρ g)) p = p)
    {A : V →ₗ[F] X} (hA : polynomialEval (ιMulti F s (fun i => A (b i))) p ≠ 0)
    (r : ℕ) :
    ∃ u : ⨂[F] (_ : Fin ((s * m) * r)), Dual F (V →ₗ[F] X),
      polynomialTensorMap F (V →ₗ[F] X) ((s * m) * r) u =
          (pluckerPolynomialPullback b p) ^ r ∧
      (∀ g, PiTensorProduct.map (fun _ : Fin ((s * m) * r) =>
        ((homSpecialLinearRepresentation (V := V) ρ) g⁻¹).dualMap) u = u) ∧
      dualDistribEquivOfProjective F (fun _ : Fin ((s * m) * r) => V →ₗ[F] X) u
        (tprod F fun _ => A) ≠ 0 := by
  apply exists_invariant_tensor_evaluation_ne_zero
    (homSpecialLinearRepresentation (V := V) ρ)
    (homogeneousInvariants_pow _ (pluckerPolynomialPullback_mem_invariants ρ b hp hi) r)
  simpa using pow_ne_zero r hA

section TensorAction

variable {U W : Type*} [AddCommGroup U] [Module F U] [AddCommGroup W] [Module F W]

/-- The independent special-linear action on the actual binary tensor product. -/
def tensorSpecialLinearRepresentation (F : Type*) [Field F]
    (U W : Type*) [AddCommGroup U] [Module F U] [AddCommGroup W] [Module F W] :
    Representation F (SpecialLinearGroup F U × SpecialLinearGroup F W) (U ⊗[F] W) :=
  Representation.tprod
    ((LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
      SpecialLinearGroup.toLinearEquiv).comp (MonoidHom.fst _ _))
    ((LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
      SpecialLinearGroup.toLinearEquiv).comp (MonoidHom.snd _ _))

omit [CharZero F] in
@[simp]
theorem tensorSpecialLinearRepresentation_apply
    (g : SpecialLinearGroup F U × SpecialLinearGroup F W) :
    tensorSpecialLinearRepresentation F U W g =
      TensorProduct.map (g.1 : U →ₗ[F] U) (g.2 : W →ₗ[F] W) := rfl

omit [CharZero F] in
/-- BALANCED's actual Plücker action agrees with the exterior action of the
independent tensor representation. -/
theorem pluckerRepresentation_eq_map (s : ℕ)
    (g : SpecialLinearGroup F U × SpecialLinearGroup F W) :
    pluckerRepresentation F U W s g =
      exteriorPower.map s (tensorSpecialLinearRepresentation F U W g) := rfl

variable [FiniteDimensional F U] [FiniteDimensional F W]

/-- The concrete product-SL Plücker invariant is consumed, without an assumed
intertwining interface, to obtain Hom-dual invariant tensors. -/
theorem exists_tensorSL_plucker_invariant_tensor {s m : ℕ} (b : Basis (Fin s) F V)
    {p : SymmetricAlgebra F (Dual F (⋀[F]^s (U ⊗[F] W)))}
    (hp : p ∈ homogeneousInvariants (pluckerRepresentation F U W s) m)
    {A : V →ₗ[F] U ⊗[F] W}
    (hA : polynomialEval (ιMulti F s (fun i => A (b i))) p ≠ 0) (r : ℕ) :
    ∃ u : ⨂[F] (_ : Fin ((s * m) * r)), Dual F (V →ₗ[F] U ⊗[F] W),
      polynomialTensorMap F (V →ₗ[F] U ⊗[F] W) ((s * m) * r) u =
          (pluckerPolynomialPullback b p) ^ r ∧
      (∀ g, PiTensorProduct.map (fun _ : Fin ((s * m) * r) =>
        ((homSpecialLinearRepresentation (V := V)
          (tensorSpecialLinearRepresentation F U W)) g⁻¹).dualMap) u = u) ∧
      dualDistribEquivOfProjective F (fun _ : Fin ((s * m) * r) => V →ₗ[F] U ⊗[F] W) u
        (tprod F fun _ => A) ≠ 0 := by
  apply exists_plucker_invariant_tensor (tensorSpecialLinearRepresentation F U W) b hp.1
    (fun g => (mem_homogeneousInvariants_iff _ _ _).mp hp |>.2 g) hA r

end TensorAction

end BostConjecture.Geometry
