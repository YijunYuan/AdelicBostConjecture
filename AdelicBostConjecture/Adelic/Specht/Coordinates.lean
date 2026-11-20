/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import AdelicBostConjecture.Specht.Lattice.Integral
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Word coordinates of the constant Specht module

The integral orbit lattice is extended to the base field without changing its
word-coordinate inclusion. These maps also describe its actual completed fibres.
-/

@[expose] public section
noncomputable section

namespace AdelicBostConjecture.Specht

open Module
open scoped TensorProduct

variable (R : Type*) [CommRing R] {n : ℕ} {μ : YoungDiagram}

/-- Scalar extension of the actual integral word-coordinate inclusion. -/
def wordCoordinates (t : OAI.Saxl.Tableau n μ) :
    R ⊗[ℤ] orbitLattice t →ₗ[R] ((Fin n → Fin (μ.colLen 0)) → R) :=
  (TensorProduct.piScalarRight ℤ R R _).toLinearMap.comp
    ((orbitLattice t).subtype.baseChange R)

@[simp]
theorem wordCoordinates_tmul (t : OAI.Saxl.Tableau n μ) (r : R)
    (x : orbitLattice t) (w : Fin n → Fin (μ.colLen 0)) :
    wordCoordinates R t (r ⊗ₜ[ℤ] x) w = r * (x.val w : R) := by
  simp [wordCoordinates, mul_comm]

/-- No quotient is introduced when the integral lattice is extended to a flat ring. -/
theorem wordCoordinates_injective [Module.Flat ℤ R] (t : OAI.Saxl.Tableau n μ) :
    Function.Injective (wordCoordinates R t) :=
  (TensorProduct.piScalarRight ℤ R R _).injective.comp
    (Module.Flat.lTensor_preserves_injective_linearMap
      (orbitLattice t).subtype Subtype.val_injective)

/-- The complex specialization is the existing checked Specht complexification. -/
theorem wordCoordinates_complex (t : OAI.Saxl.Tableau n μ) :
    wordCoordinates ℂ t = complexification t := rfl

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- Word coordinates on the actual completed scalar extension. -/
def fibreWordCoordinates (t : OAI.Saxl.Tableau n μ) :
    L ⊗[K] (K ⊗[ℤ] orbitLattice t) →ₗ[L] ((Fin n → Fin (μ.colLen 0)) → L) :=
  (TensorProduct.piScalarRight K L L _).toLinearMap.comp
    ((wordCoordinates K t).baseChange L)

@[simp]
theorem fibreWordCoordinates_tmul (t : OAI.Saxl.Tableau n μ) (z : L)
    (x : K ⊗[ℤ] orbitLattice t) (w : Fin n → Fin (μ.colLen 0)) :
    fibreWordCoordinates (K := K) t (z ⊗ₜ[K] x) w =
      z * algebraMap K L (wordCoordinates K t x w) := by
  simp [fibreWordCoordinates, Algebra.smul_def, mul_comm]

theorem fibreWordCoordinates_injective [CharZero K] (t : OAI.Saxl.Tableau n μ) :
    Function.Injective (fibreWordCoordinates (K := K) (L := L) t) :=
  (TensorProduct.piScalarRight K L L _).injective.comp
    (Module.Flat.lTensor_preserves_injective_linearMap
      (wordCoordinates K t) (wordCoordinates_injective K t))

/-- The coordinate basis after extension gives the actual word coefficients. -/
theorem fibreWordCoordinates_eq_basis (t : OAI.Saxl.Tableau n μ)
    (x : L ⊗[K] (K ⊗[ℤ] orbitLattice t)) :
    fibreWordCoordinates t x =
      ((Pi.basisFun K (Fin n → Fin (μ.colLen 0))).baseChange L).equivFun
        ((wordCoordinates K t).baseChange L x) := by
  induction x using TensorProduct.inductionOn with
  | tmul z x =>
    ext w
    simp [Basis.equivFun_apply, Basis.baseChange_repr_tmul, Algebra.smul_def, mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Cancelling the intermediate field preserves the original integral realization. -/
theorem fibreWordCoordinates_cancel (t : OAI.Saxl.Tableau n μ)
    (x : L ⊗[K] (K ⊗[ℤ] orbitLattice t)) :
    fibreWordCoordinates t x = wordCoordinates L t
      (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ K L L (orbitLattice t) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul z x =>
    induction x using TensorProduct.inductionOn with
    | tmul r y =>
      ext w
      simp [Algebra.smul_def, mul_comm, mul_left_comm]
    | add x y hx hy => simp_all only [TensorProduct.tmul_add, map_add]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The completed lattice coordinates commute with cancellation of the
intermediate ground field. -/
theorem fibreBasisCoordinates_cancel {ι : Type*} [Finite ι]
    (t : OAI.Saxl.Tableau n μ) (b : Basis ι ℤ (orbitLattice t))
    (x : L ⊗[K] (K ⊗[ℤ] orbitLattice t)) :
    ((b.baseChange K).baseChange L).equivFun x = (b.baseChange L).equivFun
      (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ K L L (orbitLattice t) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul z x =>
    induction x using TensorProduct.inductionOn with
    | tmul r y =>
      ext i
      simp [Basis.equivFun_apply, Basis.baseChange_repr_tmul, Algebra.smul_def, mul_assoc]
    | add x y hx hy => simp_all only [TensorProduct.tmul_add, map_add]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The lattice permutation action commutes with the completed fibre identification. -/
theorem fibreOrbitAction_cancel (t : OAI.Saxl.Tableau n μ) (g : Equiv.Perm (Fin n))
    (x : L ⊗[K] (K ⊗[ℤ] orbitLattice t)) :
    TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ K L L (orbitLattice t)
        (((orbitAction t g).baseChange K).baseChange L x) =
      (orbitAction t g).baseChange L
        (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ K L L (orbitLattice t) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul z x =>
    induction x using TensorProduct.inductionOn with
    | tmul r y => simp
    | add x y hx hy => simp_all only [TensorProduct.tmul_add, map_add]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Permuting tensor positions permutes the actual word coefficients. -/
theorem wordCoordinates_orbitAction (t : OAI.Saxl.Tableau n μ) (g : Equiv.Perm (Fin n))
    (x : R ⊗[ℤ] orbitLattice t) (w : Fin n → Fin (μ.colLen 0)) :
    wordCoordinates R t ((orbitAction t g).baseChange R x) w =
      wordCoordinates R t x (w ∘ g) := by
  induction x using TensorProduct.inductionOn with
  | tmul r x => simp [orbitAction, wordRepInt]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

end AdelicBostConjecture.Specht
