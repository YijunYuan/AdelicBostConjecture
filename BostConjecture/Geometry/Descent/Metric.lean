/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Geometry.Descent.Embedding
public import BostConjecture.Geometry.Determinant.Metric

/-!
# Metric preservation on complex fibers of the projective determinant inclusion

The actual global map is identified with its free formula by scalar extension.
The local isometry therefore applies to every complex fiber, with the existing
Gram determinant and Hilbert tensor forms and the canonical lattice form.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Geometry

open Module
open scoped TensorProduct

variable {R M : Type*} [CommRing R] [Algebra R ℂ]
  [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
  [c : InnerProductSpace.Core ℂ (ℂ ⊗[R] M)] {n a k : ℕ}

local instance : NormedAddCommGroup (ℂ ⊗[R] M) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ℂ ⊗[R] M)

local instance : InnerProductSpace ℂ (ℂ ⊗[R] M) :=
  InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (ℂ ⊗[R] M))

/-- The global determinant inclusion preserves the prescribed form on every
complex fiber. Both scalar-extension identifications are canonical. -/
theorem projectiveDeterminantMap_inner (hk : 0 < k)
    (t : OAI.Saxl.Tableau n (Specht.rectangle a k))
    (ha : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = a)
    (b : OrthonormalBasis (Fin a) ℂ (ℂ ⊗[R] M))
    (x y : ℂ ⊗[R] ((⨂[R] (_ : Fin k), ⋀[R]^a M) ⊗[R]
      (R ⊗[ℤ] Specht.orbitLattice t))) :
    (Tensor.hilbertCore (fun _ : Fin n => ℂ ⊗[R] M)).inner
      (Tensor.baseChangeEquiv R ℂ (fun _ : Fin n => M)
        ((projectiveDeterminantMap hk t ha).baseChange ℂ x))
      (Tensor.baseChangeEquiv R ℂ (fun _ : Fin n => M)
        ((projectiveDeterminantMap hk t ha).baseChange ℂ y)) =
    (Tensor.binaryCore
      (Tensor.tensorCore (fun _ : Fin k => Arithmetic.ComplexDeterminant.core b))
      (latticeComplexCore t)).inner
      (determinantTwistBaseChangeEquiv (Specht.orbitLattice t) k a x)
      (determinantTwistBaseChangeEquiv (Specht.orbitLattice t) k a y) := by
  rw [projectiveDeterminantMap_baseChange_of_basis hk t ha b.toBasis]
  simpa only [determinantChart, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply] using freeDeterminantMap_inner hk t b
      (determinantTwistBaseChangeEquiv (Specht.orbitLattice t) k a x)
      (determinantTwistBaseChangeEquiv (Specht.orbitLattice t) k a y)

end BostConjecture.Geometry
