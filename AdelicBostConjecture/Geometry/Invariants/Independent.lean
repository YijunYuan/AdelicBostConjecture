/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RingTheory.Flat.Basic

/-!
# Tensor invariants for independent group actions

The coordinate argument uses Mathlib's canonical tensor basis equivalence.
No finiteness of the acting groups and no averaging hypothesis is used.
-/

@[expose] public section

noncomputable section

namespace AdelicBostConjecture.Geometry

open Module TensorProduct

variable {R G V W : Type*} [CommRing R] [Group G]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

private theorem tensorRightCoefficients_map {J : Type*} [DecidableEq J]
    (b : Basis J R W) (f : V →ₗ[R] V) (z : V ⊗[R] W) (j : J) :
    equivFinsuppOfBasisRight b (TensorProduct.map f LinearMap.id z) j =
      f (equivFinsuppOfBasisRight b z j) := by
  induction z using TensorProduct.inductionOn with
  | tmul x y => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

/-- If the second module is free, fixed vectors for the first action are exactly
the tensors with coefficients in its invariant submodule. -/
theorem exists_invariants_tensor_iff [Module.Free R W]
    (ρ : Representation R G V) (z : V ⊗[R] W) :
    (∃ y : ρ.invariants ⊗[R] W,
      TensorProduct.map ρ.invariants.subtype LinearMap.id y = z) ↔
      ∀ g, TensorProduct.map (ρ g) LinearMap.id z = z := by
  classical
  constructor
  · rintro ⟨y, rfl⟩ g
    induction y using TensorProduct.inductionOn with
    | tmul x w =>
      simp only [TensorProduct.map_tmul, LinearMap.id_apply, Submodule.subtype_apply]
      rw [x.property g]
    | add x y hx hy => simp only [map_add, hx, hy]
  · intro hz
    let b := Module.Free.chooseBasis R W
    let c := equivFinsuppOfBasisRight b z
    have hc (j) : c j ∈ ρ.invariants := by
      intro g
      change ρ g (equivFinsuppOfBasisRight b z j) = equivFinsuppOfBasisRight b z j
      rw [← tensorRightCoefficients_map, hz]
    refine ⟨∑ j ∈ c.support, (⟨c j, hc j⟩ : ρ.invariants) ⊗ₜ[R] b j, ?_⟩
    simp only [map_sum, TensorProduct.map_tmul, Submodule.subtype_apply, LinearMap.id_apply]
    simpa only [equivFinsuppOfBasisRight_symm_apply, Finsupp.sum, c] using
      (equivFinsuppOfBasisRight b).symm_apply_apply z

/-- The right-factor version of the coordinate characterization. -/
theorem exists_tensor_invariants_iff [Module.Free R V]
    (ρ : Representation R G W) (z : V ⊗[R] W) :
    (∃ y : V ⊗[R] ρ.invariants,
      TensorProduct.map LinearMap.id ρ.invariants.subtype y = z) ↔
      ∀ g, TensorProduct.map LinearMap.id (ρ g) z = z := by
  constructor
  · rintro ⟨y, rfl⟩ g
    induction y using TensorProduct.inductionOn with
    | tmul x w =>
      simp only [TensorProduct.map_tmul, LinearMap.id_apply, Submodule.subtype_apply]
      rw [w.property g]
    | add x y hx hy => simp only [map_add, hx, hy]
  · intro hz
    obtain ⟨y, hy⟩ := (exists_invariants_tensor_iff ρ (TensorProduct.comm R V W z)).mpr
      (fun g => by rw [TensorProduct.map_comm, hz])
    refine ⟨TensorProduct.comm R ρ.invariants V y, ?_⟩
    rw [TensorProduct.map_comm, hy, TensorProduct.comm_comm]

section Field

variable {F H A B : Type*} [Field F] [Group H]
  [AddCommGroup A] [Module F A] [AddCommGroup B] [Module F B]
  (ρ : Representation F G A) (τ : Representation F H B)

/-- A tensor fixed under independent actions is a tensor of invariant factors. -/
theorem exists_independent_invariants_iff (z : A ⊗[F] B) :
    (∃ y : ρ.invariants ⊗[F] τ.invariants,
      TensorProduct.map ρ.invariants.subtype τ.invariants.subtype y = z) ↔
      ∀ g h, TensorProduct.map (ρ g) (τ h) z = z := by
  constructor
  · rintro ⟨y, rfl⟩ g h
    induction y using TensorProduct.inductionOn with
    | tmul x w =>
      simp only [TensorProduct.map_tmul, Submodule.subtype_apply]
      rw [x.property g, w.property h]
    | add x y hx hy => simp only [map_add, hx, hy]
  · intro hz
    obtain ⟨x, hx⟩ := (exists_invariants_tensor_iff ρ z).mpr (fun g => by
      simpa only [map_one, Module.End.one_eq_id] using hz g 1)
    have hxfix (h : H) : TensorProduct.map LinearMap.id (τ h) x = x := by
      apply Module.Flat.rTensor_preserves_injective_linearMap
        ρ.invariants.subtype ρ.invariants.injective_subtype
      change TensorProduct.map ρ.invariants.subtype LinearMap.id
          (TensorProduct.map LinearMap.id (τ h) x) =
        TensorProduct.map ρ.invariants.subtype LinearMap.id x
      have hc : TensorProduct.map ρ.invariants.subtype LinearMap.id
          (TensorProduct.map LinearMap.id (τ h) x) =
        TensorProduct.map LinearMap.id (τ h)
          (TensorProduct.map ρ.invariants.subtype LinearMap.id x) := by
        simp only [TensorProduct.map_map, LinearMap.id_comp, LinearMap.comp_id]
      rw [hc, hx]
      simpa only [map_one, Module.End.one_eq_id] using hz 1 h
    obtain ⟨y, hy⟩ := (exists_tensor_invariants_iff τ x).mpr hxfix
    refine ⟨y, ?_⟩
    rw [← hx, ← hy]
    simp only [TensorProduct.map_map, LinearMap.id_comp, LinearMap.comp_id]

end Field

end AdelicBostConjecture.Geometry
