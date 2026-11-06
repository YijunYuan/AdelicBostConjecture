/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Geometry.Invariants.Independent
public import Mathlib.LinearAlgebra.PiTensorProduct.Generators
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Invariants of a finite family of independent tensor factors

The map is the canonical `PiTensorProduct.map` of invariant subspace inclusions.
The proof uses the existing singleton-complement regrouping equivalence and the
two-factor invariant theorem, with no dimension or group-order hypothesis.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Geometry

open Module TensorProduct PiTensorProduct

variable {F ι : Type*} [Field F] {M N : ι → Type*}
  [∀ i, AddCommGroup (M i)] [∀ i, Module F (M i)]
  [∀ i, AddCommGroup (N i)] [∀ i, Module F (N i)]

/-- Tensoring injective linear maps over a field remains injective. -/
theorem piTensor_map_injective (f : ∀ i, M i →ₗ[F] N i)
    (hf : ∀ i, Function.Injective (f i)) : Function.Injective (PiTensorProduct.map f) := by
  choose g hg using fun i => (f i).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (hf i))
  have hcomp : (PiTensorProduct.map g).comp (PiTensorProduct.map f) = LinearMap.id := by
    rw [← PiTensorProduct.map_comp]
    simp only [hg, PiTensorProduct.map_id]
  exact Function.LeftInverse.injective (fun x => LinearMap.congr_fun hcomp x)

/-- Singleton-complement regrouping commutes with every tensor of factor maps. -/
theorem piTensor_split_map [DecidableEq ι] (i₀ : ι)
    (f : ∀ i, M i →ₗ[F] N i) (z : ⨂[F] i, M i) :
    equivPiTensorComplSingletonTensor F N i₀ (PiTensorProduct.map f z) =
      TensorProduct.map (PiTensorProduct.map fun j : ({i₀}ᶜ : Set ι) => f j) (f i₀)
        (equivPiTensorComplSingletonTensor F M i₀ z) := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r x => simp; rfl
  | add x y hx hy => simp only [map_add, hx, hy]

variable {G : ι → Type*} [∀ i, Group (G i)]
  (ρ : ∀ i, Representation F (G i) (M i))

/-- Pure invariant factors, and hence their span, are fixed by the product action. -/
theorem piTensor_invariants_fixed (y : ⨂[F] i, (ρ i).invariants) (g : ∀ i, G i) :
    PiTensorProduct.map (fun i => ρ i (g i))
        (PiTensorProduct.map (fun i => (ρ i).invariants.subtype) y) =
      PiTensorProduct.map (fun i => (ρ i).invariants.subtype) y := by
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    simp only [map_smul, PiTensorProduct.map_tprod, Submodule.subtype_apply]
    congr 2
    funext i
    exact (x i).property (g i)
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The fixed tensors for a finite family of independent actions are exactly the
image of the tensor of the actual invariant subspaces. -/
theorem exists_piTensor_invariants_iff [Finite ι] (z : ⨂[F] i, M i) :
    (∃ y : ⨂[F] i, (ρ i).invariants,
      PiTensorProduct.map (fun i => (ρ i).invariants.subtype) y = z) ↔
      ∀ g : ∀ i, G i, PiTensorProduct.map (fun i => ρ i (g i)) z = z := by
  classical
  constructor
  · rintro ⟨y, rfl⟩ g
    exact piTensor_invariants_fixed ρ y g
  · intro hz
    obtain ⟨n, hι⟩ : ∃ n : ℕ, Nat.card ι = n := ⟨_, rfl⟩
    induction n generalizing ι with
    | zero =>
      have : IsEmpty ι := Finite.card_eq_zero_iff.mp hι
      refine ⟨(isEmptyEquiv ι).symm (isEmptyEquiv ι z), ?_⟩
      apply (isEmptyEquiv ι).injective
      have hmap (y : ⨂[F] i, (ρ i).invariants) :
          isEmptyEquiv ι (PiTensorProduct.map (fun i => (ρ i).invariants.subtype) y) =
            isEmptyEquiv ι y := by
        induction y using PiTensorProduct.induction_on with
        | smul_tprod r x => simp
        | add x y hx hy => simp only [map_add, hx, hy]
      rw [hmap, LinearEquiv.apply_symm_apply]
    | succ n hn =>
      have : Nonempty ι := (Nat.card_pos_iff.mp (by omega)).left
      let i₀ := Classical.arbitrary ι
      let J := ({i₀}ᶜ : Set ι)
      have hJ : Nat.card J = n := by
        let := Fintype.ofFinite ι
        rw [← Fintype.card_eq_nat_card, Fintype.card_compl_set, Fintype.card_eq_nat_card, hι,
          Fintype.card_unique, add_tsub_cancel_right]
      let τ : Representation F (∀ j : J, G j) (⨂[F] j : J, M j) :=
        { toFun := fun g => PiTensorProduct.map fun j => ρ j (g j)
          map_one' := by simp
          map_mul' := fun g h => by simp only [Pi.mul_apply, map_mul, PiTensorProduct.map_mul] }
      let t : (⨂[F] j : J, (ρ j).invariants) →ₗ[F] τ.invariants :=
        (PiTensorProduct.map fun j : J => (ρ j).invariants.subtype).codRestrict τ.invariants
          (fun y g => piTensor_invariants_fixed (fun j : J => ρ j) y g)
      have ht : Function.Surjective t := by
        intro x
        obtain ⟨y, hy⟩ := hn (fun j : J => ρ j) (x : ⨂[F] j : J, M j) x.property hJ
        exact ⟨y, Subtype.ext hy⟩
      have hz' : ∀ g h, TensorProduct.map (τ g) (ρ i₀ h)
          (equivPiTensorComplSingletonTensor F M i₀ z) =
            equivPiTensorComplSingletonTensor F M i₀ z := by
        intro g h
        have hh := congrArg (equivPiTensorComplSingletonTensor F M i₀)
          (hz (Function.subtypeNeLift i₀ g h))
        rw [piTensor_split_map] at hh
        have hg (j : J) : Function.subtypeNeLift i₀ g h (j : ι) = g j :=
          Function.subtypeNeLift_of_neq i₀ g h j j.property
        simp only [hg] at hh
        rw [Function.subtypeNeLift_self i₀ g h] at hh
        exact hh
      obtain ⟨x, hx⟩ := (exists_independent_invariants_iff τ (ρ i₀)
        (equivPiTensorComplSingletonTensor F M i₀ z)).mpr hz'
      obtain ⟨y, hy⟩ := TensorProduct.map_surjective ht
        (show Function.Surjective (LinearMap.id : (ρ i₀).invariants →ₗ[F] (ρ i₀).invariants)
          from Function.surjective_id) x
      refine ⟨(equivPiTensorComplSingletonTensor F
        (fun i => (ρ i).invariants) i₀).symm y, ?_⟩
      apply (equivPiTensorComplSingletonTensor F M i₀).injective
      rw [piTensor_split_map, LinearEquiv.apply_symm_apply]
      rw [← hx, ← hy, TensorProduct.map_map]
      rfl

/-- The invariant preimage is unique: the canonical finite tensor map is an
isomorphism onto precisely the product-action fixed tensors. -/
theorem existsUnique_piTensor_invariants_iff [Finite ι] (z : ⨂[F] i, M i) :
    (∃! y : ⨂[F] i, (ρ i).invariants,
      PiTensorProduct.map (fun i => (ρ i).invariants.subtype) y = z) ↔
      ∀ g : ∀ i, G i, PiTensorProduct.map (fun i => ρ i (g i)) z = z := by
  constructor
  · intro h
    exact (exists_piTensor_invariants_iff ρ z).mp h.exists
  · intro h
    obtain ⟨y, hy⟩ := (exists_piTensor_invariants_iff ρ z).mpr h
    refine ⟨y, hy, fun y' hy' => ?_⟩
    exact piTensor_map_injective _ (fun i => (ρ i).invariants.injective_subtype)
      (hy'.trans hy.symm)

end BostConjecture.Geometry
