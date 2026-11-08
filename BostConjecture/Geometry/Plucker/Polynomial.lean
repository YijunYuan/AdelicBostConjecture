/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Geometry.Polynomial.Tensor
public import BostConjecture.Geometry.Determinant.Coordinates
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.LinearAlgebra.SpecialLinearGroup

/-!
# Actual polynomial pullback along the Plücker map

The wedge of the images of a frame gives a homogeneous polynomial map on
the existing space of linear maps. Tensor duality constructs its pullback
on symmetric algebras, with its evaluation and degree identities.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Geometry

open Module PiTensorProduct InvariantTheory exteriorPower
open scoped TensorProduct

variable {F V X : Type*} [Field F]
  [AddCommGroup V] [Module F V] [AddCommGroup X] [Module F X]

/-- Over an infinite field, intrinsic polynomials on a finite-dimensional
space are determined by their evaluations on actual vectors. -/
theorem polynomial_ext [Infinite F] [FiniteDimensional F X]
    {p q : SymmetricAlgebra F (Dual F X)}
    (h : ∀ x : X, polynomialEval x p = polynomialEval x q) : p = q := by
  classical
  let b := Module.finBasis F X
  let e := SymmetricAlgebra.equivMvPolynomial b.dualBasis
  apply e.injective
  apply MvPolynomial.funext
  intro a
  have he : (MvPolynomial.aeval a).comp e.toAlgHom =
      polynomialEval (∑ i, a i • b i) := by
    apply SymmetricAlgebra.algHom_ext
    apply b.dualBasis.ext
    intro i
    change MvPolynomial.aeval a (e (SymmetricAlgebra.ι F _ (b.dualBasis i))) =
      polynomialEval (∑ j, a j • b j) (SymmetricAlgebra.ι F _ (b.dualBasis i))
    simp only [e, SymmetricAlgebra.equivMvPolynomial_ι_apply, MvPolynomial.aeval_X,
      polynomialEval_ι]
    simp [Finsupp.single_apply]
  have he' (r : SymmetricAlgebra F (Dual F X)) :
      MvPolynomial.eval a (e r) = polynomialEval (∑ i, a i • b i) r := DFunLike.congr_fun he r
  simpa only [he', he'] using h _

variable [FiniteDimensional F X] {s : ℕ}

/-- The degree-`s` polynomial associated to a linear form on the exterior
power and a frame in the source. -/
def pluckerLinearPolynomial (v : Fin s → V) :
    Dual F (⋀[F]^s X) →ₗ[F] SymmetricAlgebra F (Dual F (V →ₗ[F] X)) :=
  (polynomialTensorMap F (V →ₗ[F] X) s).comp
    ((PiTensorProduct.map (fun i => (LinearMap.applyₗ (R := F) (M₂ := X) (v i)).dualMap)).comp
      ((dualDistribEquivOfProjective F (fun _ : Fin s => X)).symm.toLinearMap.comp
        (PiTensorProduct.lift (ιMulti F s).toMultilinearMap).dualMap))

/-- Algebra pullback along the actual wedge of a frame's images. -/
def pluckerPolynomialPullback (v : Fin s → V) :
    SymmetricAlgebra F (Dual F (⋀[F]^s X)) →ₐ[F]
      SymmetricAlgebra F (Dual F (V →ₗ[F] X)) :=
  SymmetricAlgebra.lift (pluckerLinearPolynomial v)

@[simp]
theorem pluckerPolynomialPullback_ι (v : Fin s → V) (ℓ : Dual F (⋀[F]^s X)) :
    pluckerPolynomialPullback v (SymmetricAlgebra.ι F _ ℓ) =
      pluckerLinearPolynomial v ℓ :=
  SymmetricAlgebra.lift_ι_apply _ _

private theorem polynomialEval_tensorMap_frame (v : Fin s → V) (A : V →ₗ[F] X)
    (u : ⨂[F] (_ : Fin s), Dual F X) :
    polynomialEval A (polynomialTensorMap F (V →ₗ[F] X) s
      (PiTensorProduct.map (fun i =>
        (LinearMap.applyₗ (R := F) (M₂ := X) (v i)).dualMap) u)) =
      dualDistribEquivOfProjective F (fun _ : Fin s => X) u
        (tprod F fun i => A (v i)) := by
  induction u using PiTensorProduct.induction_on with
  | smul_tprod r ℓ => simp [finprod_eq_prod_of_fintype]
  | add u w hu hw => simp only [map_add, LinearMap.add_apply, hu, hw]

@[simp]
theorem polynomialEval_pluckerLinearPolynomial (v : Fin s → V)
    (ℓ : Dual F (⋀[F]^s X)) (A : V →ₗ[F] X) :
    polynomialEval A (pluckerLinearPolynomial v ℓ) =
      ℓ (ιMulti F s (fun i => A (v i))) := by
  simp only [pluckerLinearPolynomial, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [polynomialEval_tensorMap_frame, LinearEquiv.apply_symm_apply]
  simp

/-- Evaluation is evaluation at the actual exterior image of the frame. -/
@[simp]
theorem polynomialEval_pluckerPolynomialPullback (v : Fin s → V)
    (p : SymmetricAlgebra F (Dual F (⋀[F]^s X))) (A : V →ₗ[F] X) :
    polynomialEval A (pluckerPolynomialPullback v p) =
      polynomialEval (ιMulti F s (fun i => A (v i))) p := by
  have h : (polynomialEval A).comp (pluckerPolynomialPullback v) =
      polynomialEval (ιMulti F s (fun i => A (v i))) := by
    apply SymmetricAlgebra.algHom_ext
    ext ℓ
    simp
  exact DFunLike.congr_fun h p

theorem pluckerLinearPolynomial_mem_homogeneous (v : Fin s → V)
    (ℓ : Dual F (⋀[F]^s X)) :
    pluckerLinearPolynomial v ℓ ∈ homogeneousPolynomials F (V →ₗ[F] X) s := by
  rw [← range_polynomialTensorMap]
  exact ⟨_, rfl⟩

/-- The Plücker substitution multiplies homogeneous degrees by the frame length. -/
theorem pluckerPolynomialPullback_mem_homogeneous (v : Fin s → V) {m : ℕ}
    {p : SymmetricAlgebra F (Dual F (⋀[F]^s X))}
    (hp : p ∈ homogeneousPolynomials F (⋀[F]^s X) m) :
    pluckerPolynomialPullback v p ∈ homogeneousPolynomials F (V →ₗ[F] X) (s * m) := by
  induction hp using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    simpa only [AlgHom.commutes, homogeneousPolynomials, mul_zero, pow_zero] using
      (Submodule.algebraMap_mem (R := F) (A := SymmetricAlgebra F (Dual F (V →ₗ[F] X))) r)
  | add p q m hp hq ihp ihq =>
    simpa using (homogeneousPolynomials F (V →ₗ[F] X) (s * m)).add_mem ihp ihq
  | mem_mul l hl m p hp ih =>
    obtain ⟨ℓ, rfl⟩ := hl
    simp only [map_mul, pluckerPolynomialPullback_ι]
    rw [Nat.mul_succ, Nat.add_comm, homogeneousPolynomials, pow_add]
    exact Submodule.mul_mem_mul (pluckerLinearPolynomial_mem_homogeneous v ℓ) ih

/-- Determinant-one source changes preserve its top basis wedge. -/
theorem map_basis_wedge_of_det_eq_one (b : Basis (Fin s) F V)
    (h : V →ₗ[F] V) (hh : LinearMap.det h = 1) :
    exteriorPower.map s h (ιMulti F s b) = ιMulti F s b := by
  apply (determinantCoordinates b).injective
  simp [Basis.det_comp, hh]

variable [FiniteDimensional F V] [Infinite F]

/-- The actual Plücker substitution intertwines target maps and determinant-one
source maps on the entire polynomial algebra. -/
theorem pluckerPolynomialPullback_naturality (b : Basis (Fin s) F V)
    (g : X →ₗ[F] X) (h : V →ₗ[F] V) (hh : LinearMap.det h = 1)
    (p : SymmetricAlgebra F (Dual F (⋀[F]^s X))) :
    polynomialPullback ((LinearMap.llcomp F V X X g).comp
        ((LinearMap.llcomp F V V X).flip h))
        (pluckerPolynomialPullback b p) =
      pluckerPolynomialPullback b (polynomialPullback (exteriorPower.map s g) p) := by
  apply polynomial_ext
  intro A
  simp only [polynomialEval_pullback, polynomialEval_pluckerPolynomialPullback]
  congr 2
  have he := congrArg (exteriorPower.map s (g.comp A))
    (map_basis_wedge_of_det_eq_one b h hh)
  simpa [exteriorPower.map_apply_ιMulti, Function.comp_def] using he

omit [FiniteDimensional F X] [FiniteDimensional F V] [Infinite F] in
/-- The canonical Hom action with independent target representation and special
linear source action, using Mathlib's linear Hom representation. -/
def homSpecialLinearRepresentation {G : Type*} [Group G] (ρ : Representation F G X) :
    Representation F (G × SpecialLinearGroup F V) (V →ₗ[F] X) :=
  Representation.linHom
    ((LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
      SpecialLinearGroup.toLinearEquiv).comp (MonoidHom.snd G (SpecialLinearGroup F V)))
    (ρ.comp (MonoidHom.fst G (SpecialLinearGroup F V)))

omit [FiniteDimensional F X] [FiniteDimensional F V] [Infinite F] in
@[simp]
theorem homSpecialLinearRepresentation_apply {G : Type*} [Group G]
    (ρ : Representation F G X) (g : G × SpecialLinearGroup F V) (A : V →ₗ[F] X) :
    homSpecialLinearRepresentation ρ g A =
      (ρ g.1).comp (A.comp ((g.2⁻¹ : SpecialLinearGroup F V) : V →ₗ[F] V)) := rfl

/-- A homogeneous exterior invariant pulls back to an invariant for the actual
independent target/source action on Hom. -/
theorem pluckerPolynomialPullback_mem_invariants {G : Type*} [Group G]
    (ρ : Representation F G X) (b : Basis (Fin s) F V) {m : ℕ}
    {p : SymmetricAlgebra F (Dual F (⋀[F]^s X))}
    (hp : p ∈ homogeneousPolynomials F (⋀[F]^s X) m)
    (hi : ∀ g, polynomialPullback (exteriorPower.map s (ρ g)) p = p) :
    pluckerPolynomialPullback b p ∈ homogeneousInvariants
      (homSpecialLinearRepresentation (V := V) ρ) (s * m) := by
  apply (mem_homogeneousInvariants_iff _ _ _).mpr
  refine ⟨pluckerPolynomialPullback_mem_homogeneous b hp, ?_⟩
  intro g
  have hh : LinearMap.det (((g.2⁻¹ : SpecialLinearGroup F V) : V ≃ₗ[F] V).toLinearMap) = 1 := by
    rw [← LinearEquiv.coe_det, SpecialLinearGroup.det_coe, Units.val_one]
  have he := pluckerPolynomialPullback_naturality b (ρ g.1)
    ((g.2⁻¹ : SpecialLinearGroup F V) : V →ₗ[F] V) hh p
  rwa [hi] at he

omit [FiniteDimensional F V] [Infinite F] in
/-- The pullback preserves nonzero evaluation at the specified linear map. -/
theorem polynomialEval_pluckerPolynomialPullback_ne_zero (v : Fin s → V)
    {p : SymmetricAlgebra F (Dual F (⋀[F]^s X))} {A : V →ₗ[F] X}
    (hp : polynomialEval (ιMulti F s (fun i => A (v i))) p ≠ 0) :
    polynomialEval A (pluckerPolynomialPullback v p) ≠ 0 := by
  simpa using hp

end BostConjecture.Geometry
