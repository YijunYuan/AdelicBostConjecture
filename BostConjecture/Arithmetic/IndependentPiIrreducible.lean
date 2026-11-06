module

public import BostConjecture.LinearAlgebra.PiTensorProduct.Projective
public import BostConjecture.Arithmetic.RepresentationDensity
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import Mathlib.LinearAlgebra.PiTensorProduct.Generators

/-!
# Irreducibility of a finite independent tensor action

The action operators span the full endomorphism algebra by the canonical
finite tensor Hom equivalence and tensor products of spanning sets.
-/

@[expose] public section

noncomputable section

open TensorProduct PiTensorProduct

namespace BostConjecture.Arithmetic

variable {k ι : Type*} {G V : ι → Type*}

/-- Componentwise action on the actual finite tensor module. -/
def independentPiRepresentation [CommRing k] [∀ i, Monoid (G i)]
    [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    (ρ : ∀ i, Representation k (G i) (V i)) :
    Representation k (∀ i, G i) (⨂[k] i, V i) where
  toFun g := PiTensorProduct.map (fun i => ρ i (g i))
  map_one' := by simp only [Pi.one_apply, map_one, PiTensorProduct.map_one]
  map_mul' g h := by simp only [Pi.mul_apply, map_mul, PiTensorProduct.map_mul]

variable [Field k] [Fintype ι] [∀ i, Monoid (G i)]
variable [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
variable [∀ i, FiniteDimensional k (V i)] [IsAlgClosed k]

/-- The finite independent action spans all endomorphisms of its tensor module. -/
theorem span_independentPiRepresentation_eq_top (ρ : ∀ i, Representation k (G i) (V i))
    [∀ i, Representation.IsIrreducible (ρ i)] :
    Submodule.span k (Set.range (independentPiRepresentation ρ)) = ⊤ := by
  have hs := PiTensorProduct.submodule_span_eq_top (fun i => span_representation_eq_top (ρ i))
  have he := congrArg (Submodule.map (piTensorHomEquiv k V V).toLinearMap) hs
  rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, LinearEquiv.range] at he
  simpa only [independentPiRepresentation, MonoidHom.coe_mk, OneHom.coe_mk,
    Function.comp_def, LinearEquiv.coe_coe, piTensorHomEquiv_apply,
    piTensorHomMap_tprod_eq_map] using he

/-- Finite independent tensor products of irreducible representations are irreducible. -/
theorem isIrreducible_independentPi (ρ : ∀ i, Representation k (G i) (V i))
    [∀ i, Representation.IsIrreducible (ρ i)] :
    Representation.IsIrreducible (independentPiRepresentation ρ) := by
  let : ∀ i, Nontrivial (V i) := fun i =>
    IsSimpleModule.nontrivial (MonoidAlgebra k (G i)) (ρ i).asModule
  let b := Basis.piTensorProduct (fun i => Module.Free.chooseBasis k (V i))
  let : Nontrivial (⨂[k] i, V i) := b.repr.symm.injective.nontrivial
  exact isIrreducible_of_span_eq_top _ (span_independentPiRepresentation_eq_top ρ)

end BostConjecture.Arithmetic
