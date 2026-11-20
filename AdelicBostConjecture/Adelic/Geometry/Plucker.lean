/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import AdelicBostConjecture.Adelic.Geometry.Polynomial
public import ArakelovGeometry.InvariantTheory.Plucker
public import AdelicBostConjecture.Geometry.Plucker.Nonvanishing

/-!
# From geometric Plücker semistability to determinant pairings

The coordinate invariant over the algebraic closure is converted to the intrinsic
invariant used by the integral determinant construction. The tensor actions agree
on the full product of special linear groups, and the scalar-extension maps agree
on pure tensors. Thus the resulting nonzero pairing is the existing pairing of the
original linear map, with no change of coefficient field in its conclusion.
-/

@[expose] public section

noncomputable section

namespace AdelicBostConjecture.Adelic.Geometry

open Module AdelicBostConjecture.InvariantTheory AdelicBostConjecture.Geometry
open scoped TensorProduct

variable {K G V W : Type*} [Field K] [Infinite K] [Group G]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- A Plücker-semistable map admits an intrinsic invariant nonzero at the wedge
of any source basis; the invariant acts on the actual target exterior power. -/
theorem exists_homogeneousInvariant_of_isPluckerSemistable
    (ρ : Representation K G W) (A : V →ₗ[K] W) {s : ℕ} (b : Basis (Fin s) K V)
    (h : ArakelovGeometry.InvariantTheory.IsPluckerSemistable ρ A) :
    ∃ (m : ℕ) (p : SymmetricAlgebra K (Dual K (⋀[K]^s W))), 0 < m ∧
      p ∈ homogeneousInvariants (ArakelovGeometry.InvariantTheory.exteriorRepresentation s ρ) m ∧
      polynomialEval (exteriorPower.ιMulti K s (fun j ↦ A (b j))) p ≠ 0 := by
  have hr : Module.finrank K V = s := by simpa using Module.finrank_eq_card_basis b
  subst s
  unfold ArakelovGeometry.InvariantTheory.IsPluckerSemistable at h
  obtain ⟨η, hη, hp⟩ := h
  obtain ⟨c, rfl⟩ := (determinantCoordinates b).symm.surjective η
  have hc : c ≠ 0 := by
    intro hc
    exact hη (by simp [hc])
  rw [determinantCoordinates_symm_apply, map_smul] at hp
  have hp' := (ArakelovGeometry.InvariantTheory.isPolynomialSemistable_smul_iff
    _ _ _ hc).mp hp
  rw [exteriorPower.map_apply_ιMulti] at hp'
  exact (isPolynomialSemistable_iff_exists_homogeneousInvariant _ _ _).mp hp'

/-- Plücker semistability pulls back through an intertwining target map and a
source isomorphism, allowing different acting groups. The commuting square
identifies the actual linear maps whose determinant points are tested. -/
theorem isPluckerSemistable_of_intertwining
    {H U Z : Type*} [Group H] [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    [AddCommGroup Z] [Module K Z] [FiniteDimensional K Z]
    (ρ : Representation K G W) (τ : Representation K H Z)
    (A : U →ₗ[K] Z) (B : V →ₗ[K] W) (e : U ≃ₗ[K] V) (f : Z →ₗ[K] W)
    (hf : ∀ g, ∃ h, f ∘ₗ τ g = ρ h ∘ₗ f)
    (hAB : f ∘ₗ A = B ∘ₗ e.toLinearMap)
    (hB : ArakelovGeometry.InvariantTheory.IsPluckerSemistable ρ B) :
    ArakelovGeometry.InvariantTheory.IsPluckerSemistable τ A := by
  let b := Module.finBasis K U
  obtain ⟨m, p, hm, hp, hpB⟩ :=
    exists_homogeneousInvariant_of_isPluckerSemistable ρ B (b.map e) hB
  obtain ⟨hp, hi⟩ := (mem_homogeneousInvariants_iff _ _ _).mp hp
  let q := polynomialPullback (exteriorPower.map (Module.finrank K U) f) p
  have hq : q ∈ homogeneousInvariants
      (ArakelovGeometry.InvariantTheory.exteriorRepresentation (Module.finrank K U) τ) m := by
    apply (mem_homogeneousInvariants_iff _ _ _).mpr
    refine ⟨polynomialPullback_mem_homogeneous _ hp, ?_⟩
    intro g
    obtain ⟨h, hh⟩ := hf g
    have he := congrArg (exteriorPower.map (Module.finrank K U)) hh
    simp only [exteriorPower.map_comp] at he
    change polynomialPullback (exteriorPower.map (Module.finrank K U) (τ g))
      (polynomialPullback (exteriorPower.map (Module.finrank K U) f) p) = q
    rw [← AlgHom.comp_apply, ← polynomialPullback_comp, he,
      polynomialPullback_comp, AlgHom.comp_apply]
    exact congrArg (polynomialPullback (exteriorPower.map (Module.finrank K U) f)) (hi h)
  have hqA : polynomialEval (exteriorPower.ιMulti K (Module.finrank K U)
      (fun j ↦ A (b j))) q ≠ 0 := by
    rw [polynomialEval_pullback, exteriorPower.map_apply_ιMulti]
    convert hpB using 1
    congr 3
    funext j
    exact LinearMap.congr_fun hAB (b j)
  refine ⟨exteriorPower.ιMulti K (Module.finrank K U) b, ?_, ?_⟩
  · intro hz
    have hz' := congrArg (determinantCoordinates b) hz
    simp [Basis.det_self] at hz'
  · rw [exteriorPower.map_apply_ιMulti]
    exact (isPolynomialSemistable_iff_exists_homogeneousInvariant _ _ _).mpr
      ⟨m, q, hm, hq, hqA⟩

section Tensor

variable {K : Type*} [Field K] {ι : Type*}
  (E : ι → Type*) [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]

/-- Both libraries use the same action of the full product of special linear groups. -/
theorem tensorSLRepresentation_eq :
    ArakelovGeometry.InvariantTheory.tensorSLRepresentation E =
      specialLinearTensorRepresentation K E := by
  ext g x
  rfl

/-- The two scalar-extension equivalences agree on every tensor, not just on a
chosen frame. This identifies the original linear maps in the two APIs. -/
theorem tensorBaseChangeEquiv_eq [Finite ι] (L : Type*) [Field L] [Algebra K L] :
    ArakelovGeometry.tensorBaseChangeEquiv K L E = Tensor.baseChangeEquiv K L E := by
  apply LinearEquiv.toLinearMap_injective
  apply TensorProduct.AlgebraTensorModule.ext
  intro c z
  induction z using PiTensorProduct.induction_on with
  | smul_tprod a x =>
    simp only [TensorProduct.tmul_smul,
      LinearEquiv.coe_coe, LinearMap.map_smul_of_tower,
      ArakelovGeometry.tensorBaseChangeEquiv_tmul_tprod, Tensor.baseChangeEquiv_tmul]
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]

end Tensor

end AdelicBostConjecture.Adelic.Geometry
