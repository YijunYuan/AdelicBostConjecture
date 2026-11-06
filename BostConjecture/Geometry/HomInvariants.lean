module

public import BostConjecture.Geometry.HomTensor
public import BostConjecture.Geometry.PluckerPolynomial
public import BostConjecture.Geometry.PolynomialPolarization
public import BostConjecture.Geometry.IndependentInvariants

/-! # Nonzero Hom pairing on independent invariant factors

The actual invariant polynomial is lifted, regrouped, and restricted to the
independent invariant subspaces. No invariant-space equality is assumed.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Geometry

open Module PiTensorProduct InvariantTheory
open scoped TensorProduct

variable {F : Type} {G V W : Type*} [Field F] [Group G]
  [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

/-- The tensor-power action induced by an existing representation. -/
def tensorPowerRepresentation (ρ : Representation F G V) (d : ℕ) :
    Representation F G (⨂[F] (_ : Fin d), V) where
  toFun g := PiTensorProduct.map fun _ => ρ g
  map_one' := by simp
  map_mul' g h := by simp only [map_mul, PiTensorProduct.map_mul]

variable [FiniteDimensional F V] [FiniteDimensional F W] [CharZero F]

set_option maxHeartbeats 800000 in
/-- A nonzero invariant Hom polynomial detects a nonzero canonical pairing on
source special-linear invariants and dual-target invariants separately. -/
theorem exists_independent_invariant_pairing
    (ρ : Representation F G W) (A : V →ₗ[F] W) {d : ℕ}
    {p : SymmetricAlgebra F (Dual F (V →ₗ[F] W))}
    (hp : p ∈ homogeneousInvariants (homSpecialLinearRepresentation ρ) d)
    (hpA : polynomialEval A p ≠ 0) :
    ∃ (v : ⨂[F] (_ : Fin d), V) (ℓ : ⨂[F] (_ : Fin d), Dual F W),
      (∀ h : SpecialLinearGroup F V,
        PiTensorProduct.map (fun _ => (h : V →ₗ[F] V)) v = v) ∧
      (∀ g : G, PiTensorProduct.map (fun _ => (ρ g⁻¹).dualMap) ℓ = ℓ) ∧
      Tensor.tensorPowerPairing A v ℓ ≠ 0 := by
  obtain ⟨u, hu, hufix, _⟩ := exists_invariant_tensor_evaluation_ne_zero
    (homSpecialLinearRepresentation ρ) hp hpA
  obtain ⟨z, _, hz, hzfix⟩ := exists_regrouped_hom_tensor A u (by rwa [hu])
  let σ : Representation F (SpecialLinearGroup F V) V :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
      SpecialLinearGroup.toLinearEquiv
  let σd := tensorPowerRepresentation σ d
  let τd := tensorPowerRepresentation ρ.dual d
  have hfix (h : SpecialLinearGroup F V) (g : G) :
      TensorProduct.map (σd h) (τd g) z = z := by
    apply hzfix (h : V →ₗ[F] V) (ρ g⁻¹)
    have he : ((ρ g⁻¹).compRight F).comp ((h : V →ₗ[F] V).lcomp F W) =
        homSpecialLinearRepresentation ρ (g, h)⁻¹ := by
      ext A x
      simp [homSpecialLinearRepresentation_apply]
    rw [he]
    exact hufix (g, h)
  obtain ⟨y, hy⟩ := (exists_independent_invariants_iff
    (F := F) (G := SpecialLinearGroup F V) (H := G)
    (A := ⨂[F] (_ : Fin d), V) (B := ⨂[F] (_ : Fin d), Dual F W) σd τd z).mpr hfix
  have hex : ∃ (v : σd.invariants) (ℓ : τd.invariants),
      Tensor.tensorPowerPairing A v.val ℓ.val ≠ 0 := by
    by_contra! hall
    have hzero : (TensorProduct.lift (Tensor.tensorPowerPairing A)).comp
        (TensorProduct.map σd.invariants.subtype τd.invariants.subtype) = 0 := by
      apply TensorProduct.ext
      intro v ℓ
      exact hall v ℓ
    apply hz
    rw [← hy]
    exact LinearMap.congr_fun hzero y
  obtain ⟨v, ℓ, hvℓ⟩ := hex
  exact ⟨v.val, ℓ.val, v.property, ℓ.property, hvℓ⟩

end BostConjecture.Geometry
