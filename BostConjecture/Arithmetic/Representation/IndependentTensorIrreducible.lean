/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Representation.Density
public import Mathlib.LinearAlgebra.Contraction

/-!
# Irreducibility for independent tensor factors

The action of the product monoid is Mathlib's tensor representation after
precomposition with the two projections. Over an algebraically closed field,
irreducibility follows from the actual full endomorphism algebras of the factors.
-/

@[expose] public section

noncomputable section

open scoped MonoidAlgebra
open TensorProduct

namespace BostConjecture.Arithmetic

variable {k G H V W : Type*}

/-- The tensor action of two independently acting monoids. -/
def independentTensorRepresentation [CommSemiring k] [Monoid G] [Monoid H]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    (ρ : Representation k G V) (τ : Representation k H W) :
    Representation k (G × H) (V ⊗[k] W) :=
  Representation.tprod (ρ.comp (MonoidHom.fst G H)) (τ.comp (MonoidHom.snd G H))

variable [Field k] [Monoid G] [Monoid H]
variable [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- Independent irreducible actions have an irreducible tensor product. -/
theorem isIrreducible_independentTensor (ρ : Representation k G V)
    (τ : Representation k H W) [FiniteDimensional k V] [FiniteDimensional k W]
    [IsAlgClosed k] [Representation.IsIrreducible ρ] [Representation.IsIrreducible τ] :
    Representation.IsIrreducible (independentTensorRepresentation ρ τ) := by
  let : Nontrivial V := IsSimpleModule.nontrivial k[G] ρ.asModule
  let : Nontrivial W := IsSimpleModule.nontrivial k[H] τ.asModule
  let : Nontrivial (V ⊗[k] W) := Module.nontrivial_of_finrank_pos (R := k) (by
    rw [Module.finrank_tensorProduct]
    exact Nat.mul_pos (Module.finrank_pos) (Module.finrank_pos))
  let : Nontrivial (Subrepresentation (independentTensorRepresentation ρ τ)) :=
    ⟨⟨⊥, ⊤, fun he => bot_ne_top (congrArg Subrepresentation.toSubmodule he)⟩⟩
  constructor
  intro P
  have ht (f : Module.End k V) (g : Module.End k W) (x : V ⊗[k] W) (hx : x ∈ P) :
      TensorProduct.map f g x ∈ P := by
    change TensorProduct.map f g x ∈ P.toSubmodule
    obtain ⟨a, rfl⟩ := representation_asAlgebraHom_surjective ρ f
    obtain ⟨b, rfl⟩ := representation_asAlgebraHom_surjective τ g
    induction a using MonoidAlgebra.induction_on with
    | of a =>
      induction b using MonoidAlgebra.induction_on with
      | of b =>
        rw [Representation.asAlgebraHom_of, Representation.asAlgebraHom_of]
        exact P.apply_mem_toSubmodule (a, b) hx
      | add b c hb hc =>
        simpa only [map_add, TensorProduct.map_add_right, LinearMap.add_apply] using
          P.toSubmodule.add_mem hb hc
      | smul c b hb =>
        simpa only [map_smul, TensorProduct.map_smul_right, LinearMap.smul_apply] using
          P.toSubmodule.smul_mem c hb
    | add a b ha hb =>
      simpa only [map_add, TensorProduct.map_add_left, LinearMap.add_apply] using
        P.toSubmodule.add_mem ha hb
    | smul c a ha =>
      simpa only [map_smul, TensorProduct.map_smul_left, LinearMap.smul_apply] using
        P.toSubmodule.smul_mem c ha
  have hEnd (f : Module.End k (V ⊗[k] W)) (x : V ⊗[k] W) (hx : x ∈ P) : f x ∈ P := by
    change f x ∈ P.toSubmodule
    obtain ⟨t, rfl⟩ := (homTensorHomEquiv k V W V W).surjective f
    induction t using TensorProduct.inductionOn with
    | tmul f g => exact ht f g x hx
    | add a b ha hb => simpa using P.toSubmodule.add_mem ha hb
  let Q : Submodule (Module.End k (V ⊗[k] W)) (V ⊗[k] W) :=
    { P.toSubmodule.toAddSubmonoid with smul_mem' := fun f x hx => hEnd f x hx }
  rcases eq_bot_or_eq_top Q with hQ | hQ
  · left
    apply Subrepresentation.toSubmodule_injective
    ext x
    exact show x ∈ Q ↔ x ∈ (⊥ : Submodule (Module.End k (V ⊗[k] W)) (V ⊗[k] W)) from
      by rw [hQ]
  · right
    apply Subrepresentation.toSubmodule_injective
    ext x
    exact show x ∈ Q ↔ x ∈ (⊤ : Submodule (Module.End k (V ⊗[k] W)) (V ⊗[k] W)) from
      by rw [hQ]

end BostConjecture.Arithmetic
