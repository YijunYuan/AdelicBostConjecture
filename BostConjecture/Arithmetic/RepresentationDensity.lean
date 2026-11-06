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

end BostConjecture.Arithmetic
