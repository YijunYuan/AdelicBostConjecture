/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.InvariantTheory.SpecialLinear.Coordinates
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Scalar extension of the special-linear coordinate algebra

Tensoring the determinant-one quotient extends its two defining equations.
The equivalence below uses the existing tensor–quotient and polynomial
scalar-extension equivalences, with an explicit formula on representatives.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.InvariantTheory

open scoped TensorProduct

variable (K L ι κ : Type*) [CommRing K] [CommRing L] [Algebra K L]
  [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [Fintype κ] [DecidableEq κ] in
@[simp]
theorem map_specialLinearLeftRelation :
    MvPolynomial.map (algebraMap K L) (specialLinearLeftRelation K ι κ) =
      specialLinearLeftRelation L ι κ := by
  unfold specialLinearLeftRelation
  rw [map_sub, map_one, RingHom.map_det]
  congr 2
  ext i j
  simp

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem map_specialLinearRightRelation :
    MvPolynomial.map (algebraMap K L) (specialLinearRightRelation K ι κ) =
      specialLinearRightRelation L ι κ := by
  unfold specialLinearRightRelation
  rw [map_sub, map_one, RingHom.map_det]
  congr 2
  ext i j
  simp

/-- The two determinant equations generate exactly the extended ideal. -/
theorem map_specialLinearPairIdeal :
    (specialLinearPairIdeal K ι κ).map (MvPolynomial.map (algebraMap K L)) =
      specialLinearPairIdeal L ι κ := by
  simp [specialLinearPairIdeal, Ideal.map_span, Set.image_insert_eq]

theorem map_tensor_specialLinearPairIdeal :
    ((specialLinearPairIdeal K ι κ).map
      (Algebra.TensorProduct.includeRight :
        MvPolynomial ((ι × ι) ⊕ (κ × κ)) K →ₐ[K]
          L ⊗[K] MvPolynomial ((ι × ι) ⊕ (κ × κ)) K).toRingHom).map
      (MvPolynomial.algebraTensorAlgEquiv K L).toRingEquiv.toRingHom =
        specialLinearPairIdeal L ι κ := by
  rw [Ideal.map_map]
  have h : (MvPolynomial.algebraTensorAlgEquiv K L).toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeRight :
        MvPolynomial ((ι × ι) ⊕ (κ × κ)) K →ₐ[K]
          L ⊗[K] MvPolynomial ((ι × ι) ⊕ (κ × κ)) K).toRingHom =
      MvPolynomial.map (algebraMap K L) := by
    apply RingHom.ext
    intro p
    change MvPolynomial.algebraTensorAlgEquiv K L (1 ⊗ₜ[K] p) = _
    simp
  simpa only [h] using map_specialLinearPairIdeal K L ι κ

/-- Scalar extension commutes with the actual determinant-one quotient algebra. -/
def specialLinearPairBaseChangeEquiv :
    L ⊗[K] SpecialLinearPairCoordinateRing K ι κ ≃ₐ[L]
      SpecialLinearPairCoordinateRing L ι κ :=
  (Algebra.TensorProduct.tensorQuotientEquiv L
    (MvPolynomial ((ι × ι) ⊕ (κ × κ)) K) L (specialLinearPairIdeal K ι κ)).trans
    (Ideal.quotientEquivAlg _ _ (MvPolynomial.algebraTensorAlgEquiv K L)
      (map_tensor_specialLinearPairIdeal K L ι κ).symm)

@[simp]
theorem specialLinearPairBaseChangeEquiv_tmul_mk (l : L)
    (p : MvPolynomial ((ι × ι) ⊕ (κ × κ)) K) :
    specialLinearPairBaseChangeEquiv K L ι κ
      (l ⊗ₜ[K] Ideal.Quotient.mkₐ K (specialLinearPairIdeal K ι κ) p) =
      l • Ideal.Quotient.mkₐ L (specialLinearPairIdeal L ι κ)
        (MvPolynomial.map (algebraMap K L) p) := by
  change Ideal.Quotient.mkₐ L (specialLinearPairIdeal L ι κ)
    (MvPolynomial.algebraTensorAlgEquiv K L (l ⊗ₜ[K] p)) = _
  simp

end BostConjecture.InvariantTheory
