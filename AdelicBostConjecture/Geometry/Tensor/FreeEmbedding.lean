/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import AdelicBostConjecture.Geometry.Tensor.Realization

/-!
# The scalar-extended integral lattice in a finite free tensor power

The integral orbit-lattice inclusion is extended to a commutative ring and
transported through the canonical tensor basis. Flatness over the integers
ensures injectivity. Determinant covariance and the overlap identity apply
to this actual scalar-extended lattice, not only to its coordinate span.
-/

@[expose] public section

noncomputable section

namespace AdelicBostConjecture.Geometry

open Module
open scoped TensorProduct

variable {R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {n a k : ℕ}

/-- The integral orbit-lattice inclusion after scalar extension, realized in
the actual tensor power using a frame. -/
def freeLatticeMap (hk : 0 < k) (t : OAI.Saxl.Tableau n (Specht.rectangle a k))
    (b : Basis (Fin a) R M) :
    R ⊗[ℤ] Specht.orbitLattice t →ₗ[R] (⨂[R] (_ : Fin n), M) :=
  (tensorCoordinates n b).symm.toLinearMap ∘ₗ
    (LinearEquiv.funCongrLeft R R (Specht.rectangleAlphabetEquiv hk).symm).toLinearMap ∘ₗ
    (TensorProduct.piScalarRight ℤ R R _).toLinearMap ∘ₗ
    (Specht.orbitLattice t).subtype.baseChange R

@[simp]
theorem freeLatticeMap_tmul (hk : 0 < k)
    (t : OAI.Saxl.Tableau n (Specht.rectangle a k)) (b : Basis (Fin a) R M)
    (r : R) (x : Specht.orbitLattice t) :
    freeLatticeMap hk t b (r ⊗ₜ[ℤ] x) =
      r • (tensorCoordinates n b).symm
        (fun w => (x.val ((Specht.rectangleAlphabetEquiv hk).symm w) : R)) := by
  apply (tensorCoordinates n b).injective
  ext w
  simp [freeLatticeMap, mul_comm]

/-- Flatness preserves the actual integral inclusion, before transport to the
tensor basis. -/
theorem freeLatticeMap_injective [Module.Flat ℤ R] (hk : 0 < k)
    (t : OAI.Saxl.Tableau n (Specht.rectangle a k)) (b : Basis (Fin a) R M) :
    Function.Injective (freeLatticeMap hk t b) :=
  (tensorCoordinates n b).symm.injective.comp <|
    (LinearEquiv.funCongrLeft R R (Specht.rectangleAlphabetEquiv hk).symm).injective.comp <|
    (TensorProduct.piScalarRight ℤ R R _).injective.comp <|
    Module.Flat.lTensor_preserves_injective_linearMap (M := R)
      (Specht.orbitLattice t).subtype (Submodule.injective_subtype _)

/-- Naturality of the scalar-extended integral realization with determinant
weight, for arbitrary linear maps between framed modules. -/
theorem map_freeLatticeMap (hk : 0 < k)
    (t : OAI.Saxl.Tableau n (Specht.rectangle a k))
    (b : Basis (Fin a) R M) (c : Basis (Fin a) R N) (f : M →ₗ[R] N)
    (z : R ⊗[ℤ] Specht.orbitLattice t) :
    PiTensorProduct.map (fun _ => f) (freeLatticeMap hk t b z) =
      (LinearMap.toMatrix b c f).det ^ k • freeLatticeMap hk t c z := by
  induction z using TensorProduct.inductionOn with
  | tmul r x =>
    simp only [freeLatticeMap_tmul, map_smul]
    rw [map_tensorCoordinates_symm_of_mem_span hk t b c f
      (Submodule.subset_span ⟨x, rfl⟩), smul_comm]
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]

/-- The overlap identity holds on the scalar-extended integral lattice itself. -/
theorem freeLatticeMap_change_basis (hk : 0 < k)
    (t : OAI.Saxl.Tableau n (Specht.rectangle a k))
    (b c : Basis (Fin a) R M) (z : R ⊗[ℤ] Specht.orbitLattice t) :
    freeLatticeMap hk t b z =
      (LinearMap.toMatrix b c (LinearMap.id : M →ₗ[R] M)).det ^ k •
        freeLatticeMap hk t c z := by
  simpa using map_freeLatticeMap hk t b c LinearMap.id z

end AdelicBostConjecture.Geometry
