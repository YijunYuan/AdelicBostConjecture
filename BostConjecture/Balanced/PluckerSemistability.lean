module

public import BostConjecture.Balanced.OrbitNorm
public import BostConjecture.InvariantTheory.Semistability
public import BostConjecture.InvariantTheory.OrbitImage
public import BostConjecture.InvariantTheory.ComplexClosure.Comparison

/-!
# Geometric semistability of the actual balanced Plücker vector

The polynomial-image closure comparison converts the established orbit norm
bound into the canonical geometric semistability conclusion. Construction of
an invariant polynomial is a separate obligation in the full orbit criterion.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Balanced

open Module exteriorPower InvariantTheory
open scoped TensorProduct

variable {U W : Type*} [NormedAddCommGroup U] [InnerProductSpace ℂ U]
  [FiniteDimensional ℂ U] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [FiniteDimensional ℂ W]

/-- The actual Plücker orbit has the same Euclidean and polynomial Zariski closures. -/
theorem closure_pluckerOrbit_eq_polynomialZariskiClosure (s : ℕ)
    (z : ⋀[ℂ]^s (U ⊗[ℂ] W)) :
    closure (Set.range fun g => pluckerRepresentation ℂ U W s g z) =
      polynomialZariskiClosure (K := ℂ)
        (Set.range fun g => pluckerRepresentation ℂ U W s g z) := by
  classical
  let : LinearOrder (Fin (Module.finrank ℂ U) × Fin (Module.finrank ℂ W)) :=
    LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective
  let bU := Module.finBasis ℂ U
  let bW := Module.finBasis ℂ W
  have he := closure_polynomial_image_zeroLocus (E := ⋀[ℂ]^s (U ⊗[ℂ] W))
    ((bU.tensorProduct bW).exteriorPower s)
    (specialLinearPairIdeal ℂ (Fin (Module.finrank ℂ U)) (Fin (Module.finrank ℂ W)))
    (pluckerOrbitPolynomial bU bW s z)
  rwa [pluckerOrbit_polynomial_image bU bW s z] at he

/-- Balanced orthogonal projections give geometric semistability of their actual
Plücker vectors. The invariant-polynomial form of the criterion is proved separately. -/
theorem IsBalanced.isGeometricallySemistable_plucker {s : ℕ}
    {S : Submodule ℂ (U ⊗[ℂ] W)} (hS : IsBalanced S)
    (v : OrthonormalBasis (Fin s) ℂ S) :
    IsGeometricallySemistable (pluckerRepresentation ℂ U W s)
      (ιMulti ℂ s (fun i => (v i : U ⊗[ℂ] W))) := by
  change (0 : ⋀[ℂ]^s (U ⊗[ℂ] W)) ∉ polynomialZariskiClosure _
  rw [← closure_pluckerOrbit_eq_polynomialZariskiClosure]
  exact hS.zero_not_mem_closure_plucker_orbit v

/-- Every nonzero vector on the balanced Plücker line is geometrically semistable. -/
theorem IsBalanced.isGeometricallySemistable_plucker_line {s : ℕ}
    {S : Submodule ℂ (U ⊗[ℂ] W)} (hS : IsBalanced S)
    (v : OrthonormalBasis (Fin s) ℂ S) {z : ⋀[ℂ]^s (U ⊗[ℂ] W)}
    (hz : z ∈ Submodule.span ℂ {ιMulti ℂ s (fun i => (v i : U ⊗[ℂ] W))})
    (hz0 : z ≠ 0) : IsGeometricallySemistable (pluckerRepresentation ℂ U W s) z :=
  (hS.isGeometricallySemistable_plucker v).of_mem_span_singleton hz hz0

end BostConjecture.Balanced
