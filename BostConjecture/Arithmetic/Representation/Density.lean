/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.RepresentationTheory.Irreducible

/-!
# Full endomorphism algebra of an irreducible representation

This is the finite-dimensional consequence of Mathlib's Jacobson density
theorem and Schur's lemma over an algebraically closed field.
-/

@[expose] public section

noncomputable section

open scoped MonoidAlgebra

namespace BostConjecture.Arithmetic

variable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]

/-- An irreducible action over an algebraically closed field spans every endomorphism. -/
theorem representation_asAlgebraHom_surjective (ρ : Representation k G V)
    [FiniteDimensional k V] [IsAlgClosed k] [Representation.IsIrreducible ρ] :
    Function.Surjective ρ.asAlgebraHom := by
  let : Module.Finite (Module.End k[G] ρ.asModule) ρ.asModule :=
    Module.Finite.of_restrictScalars_finite k _ _
  intro f
  let f₀ : Module.End k ρ.asModule :=
    ρ.asModuleEquiv.symm.toLinearMap ∘ₗ f ∘ₗ ρ.asModuleEquiv.toLinearMap
  let f' : Module.End (Module.End k[G] ρ.asModule) ρ.asModule :=
    { f₀.toAddMonoidHom with
      map_smul' := by
        intro a x
        obtain ⟨c, rfl⟩ :=
          (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed k).surjective a
        exact f₀.map_smul c x }
  obtain ⟨a, ha⟩ := Module.Finite.toModuleEnd_moduleEnd_surjective f'
  refine ⟨a, ?_⟩
  ext x
  exact congrArg ρ.asModuleEquiv
    (congrArg (fun u : Module.End (Module.End k[G] ρ.asModule) ρ.asModule =>
      u (ρ.asModuleEquiv.symm x)) ha)

/-- The action operators span the full endomorphism space. -/
theorem span_representation_eq_top (ρ : Representation k G V)
    [FiniteDimensional k V] [IsAlgClosed k] [Representation.IsIrreducible ρ] :
    Submodule.span k (Set.range ρ) = ⊤ := by
  apply top_unique
  intro f hf
  clear hf
  obtain ⟨a, rfl⟩ := representation_asAlgebraHom_surjective ρ f
  induction a using MonoidAlgebra.induction_on with
  | of g =>
    rw [Representation.asAlgebraHom_of]
    exact Submodule.subset_span (Set.mem_range_self g)
  | add a b ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
  | smul c a ha => simpa only [map_smul] using Submodule.smul_mem _ c ha

/-- A nonzero representation spanning every endomorphism is irreducible. -/
theorem isIrreducible_of_span_eq_top (ρ : Representation k G V) [Nontrivial V]
    (hspan : Submodule.span k (Set.range ρ) = ⊤) : Representation.IsIrreducible ρ := by
  let : Nontrivial (Subrepresentation ρ) :=
    ⟨⟨⊥, ⊤, fun he => bot_ne_top (congrArg Subrepresentation.toSubmodule he)⟩⟩
  constructor
  intro P
  have hEnd (f : Module.End k V) (x : V) (hx : x ∈ P) : f x ∈ P.toSubmodule := by
    have hf : f ∈ Submodule.span k (Set.range ρ) := hspan.symm ▸ Submodule.mem_top
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨g, rfl⟩ := hf
      exact P.apply_mem_toSubmodule g hx
    | zero => simp
    | add f g _ _ hf hg => exact P.toSubmodule.add_mem hf hg
    | smul a f _ hf => exact P.toSubmodule.smul_mem a hf
  let Q : Submodule (Module.End k V) V :=
    { P.toSubmodule.toAddSubmonoid with smul_mem' := fun f x hx => hEnd f x hx }
  rcases eq_bot_or_eq_top Q with hQ | hQ
  · left
    apply Subrepresentation.toSubmodule_injective
    ext x
    exact show x ∈ Q ↔ x ∈ (⊥ : Submodule (Module.End k V) V) from by rw [hQ]
  · right
    apply Subrepresentation.toSubmodule_injective
    ext x
    exact show x ∈ Q ↔ x ∈ (⊤ : Submodule (Module.End k V) V) from by rw [hQ]

end BostConjecture.Arithmetic
