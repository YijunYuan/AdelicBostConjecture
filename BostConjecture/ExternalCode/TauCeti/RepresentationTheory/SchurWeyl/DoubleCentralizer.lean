/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# The semisimple image double centralizer, with only its restriction-of-scalars helper

Selected from TauCeti; see BostConjecture/ExternalCode/TauCeti/Provenance/SchurWeyl/PROVENANCE.md.

## Source

Adapted from <https://github.com/TauCetiProject/TauCeti>, revision
`b3b0334ab9203d9faee4b2f34cd75161463ecdd0`.
Original sources:
* `TauCeti/LinearAlgebra/End/Centralizer.lean`.
* `TauCeti/RingTheory/Semisimple/DoubleCentralizer.lean`.

The original declaration namespaces and license notices are retained, except for
project-specific adaptations documented in `CONTRIBUTIONS.md`.
-/

@[expose] public section

namespace Subalgebra

variable {K N : Type*} [CommSemiring K] [AddCommMonoid N] [Module K N]

/-- An endomorphism linear over a subalgebra of `Module.End K N` lies in its centralizer after
restricting scalars to `K`. -/
theorem restrictScalars_mem_centralizer (A : Subalgebra K (Module.End K N))
    (g : Module.End A N) :
    g.restrictScalars K ∈ centralizer K (A : Set (Module.End K N)) := by
  refine (mem_centralizer_iff K).2 fun a ha => ?_
  ext m
  exact (g.map_smul ⟨a, ha⟩ m).symm

end Subalgebra

section EndSubalgebra

variable {K : Type*} [CommRing K] {N : Type*} [AddCommGroup N] [Module K N]
  (A : Subalgebra K (Module.End K N))

/-- **The double centralizer theorem inside an endomorphism algebra.** Let `A` be a `K`-subalgebra
of `Module.End K N`, and suppose `N` is semisimple as an `A`-module and finite over
`Module.End A N`. Then `A` is its own double centralizer: an endomorphism commuting with everything
that commutes with `A` already lies in `A`.

The inclusion `A ≤ A''` is formal (`Subalgebra.le_centralizer_centralizer`); the content is the
reverse one, which is Jacobson density. The centralizer `A'` is the ring of `A`-linear
endomorphisms of `N`, so an element of `A''` is an `A'`-linear endomorphism, and density writes
every such endomorphism as the action of an element of `A`.

Finiteness is over `Module.End A N`, the hypothesis density actually needs; a caller with a finite
`K`-module `N` gets it from `Module.Finite.of_restrictScalars_finite`. -/
theorem _root_.Subalgebra.centralizer_centralizer_of_isSemisimpleModule
    [Module.Finite (Module.End A N) N] [IsSemisimpleModule A N] :
    Subalgebra.centralizer K
        (Subalgebra.centralizer K (A : Set (Module.End K N)) : Set (Module.End K N)) = A := by
  refine le_antisymm (fun x hx => ?_) (Subalgebra.le_centralizer_centralizer K)
  rw [Subalgebra.mem_centralizer_iff] at hx
  -- `x` commutes with every `A`-linear endomorphism, so it is `A'`-linear.
  let f : Module.End (Module.End A N) N :=
    { toFun := x
      map_add' := x.map_add
      map_smul' := fun g m => by
        -- Evaluating the commutation of `x` with `g.restrictScalars K` at `m` gives
        -- `x (g m) = g (x m)`, which is the required `A'`-linearity once the scalar action of
        -- `Module.End ↥A N` on `N` is `Module.End.smul_def` and the restriction of scalars is
        -- `LinearMap.coe_restrictScalars`.
        have h := congrArg (fun t : Module.End K N => t m)
          (hx _ (A.restrictScalars_mem_centralizer g))
        simpa only [Module.End.smul_def, RingHom.id_apply, Module.End.mul_apply,
          LinearMap.coe_restrictScalars] using h.symm }
  obtain ⟨a, ha⟩ := Module.Finite.toModuleEnd_moduleEnd_surjective (R := A) (M := N) f
  have hx' : x = (a : Module.End K N) := by
    ext m
    exact (congrArg (fun t : Module.End (Module.End A N) N => t m) ha).symm
  exact hx' ▸ a.2

/-- **The double centralizer theorem for the image of a semisimple algebra.** The image of a
semisimple `K`-algebra `S` in `Module.End K N` is its own double centralizer when `N` is finite
over the endomorphism ring of the image's action.

The image is a quotient of `S`, hence semisimple, so `N` is a semisimple module over it and
`Subalgebra.centralizer_centralizer_of_isSemisimpleModule` applies. A caller with a finite
`K`-module gets the required finiteness from `Module.Finite.of_restrictScalars_finite`. It is the
image and not `S` that is recovered: the representation `S → Module.End K N` need not be
injective. -/
theorem _root_.AlgHom.centralizer_centralizer_range
    {S : Type*} [Ring S] [Algebra K S] [IsSemisimpleRing S] (ρ : S →ₐ[K] Module.End K N)
    [Module.Finite (Module.End ρ.range N) N] :
    Subalgebra.centralizer K
        (Subalgebra.centralizer K (ρ.range : Set (Module.End K N)) : Set (Module.End K N)) =
      ρ.range := by
  have : IsSemisimpleRing ρ.range :=
    RingHom.isSemisimpleRing_of_surjective ρ.rangeRestrict.toRingHom
      (AlgHom.rangeRestrict_surjective _)
  have : IsSemisimpleModule ρ.range N := IsSemisimpleRing.isSemisimpleModule
  exact Subalgebra.centralizer_centralizer_of_isSemisimpleModule _

end EndSubalgebra
