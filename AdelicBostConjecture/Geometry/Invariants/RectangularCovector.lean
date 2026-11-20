/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import AdelicBostConjecture.Geometry.Tensor.FreeEmbedding

/-!
# The bilinear covector of the rectangular polytabloid

This is the coefficient pairing in the canonical tensor basis, over a generic
commutative ring. Its transpose covariance and integer square normalization
supply the rank-one operator used in rectangular invariant detection.
-/

@[expose] public section

noncomputable section

namespace AdelicBostConjecture.Geometry

open Module PiTensorProduct
open scoped TensorProduct

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n a k : ℕ}

/-- The actual rectangular polytabloid in a framed tensor power. -/
def rectangularTensor (hk : 0 < k) (t : OAI.Saxl.Tableau n (Specht.rectangle a k))
    (b : Basis (Fin a) R M) : ⨂[R] (_ : Fin n), M :=
  (tensorCoordinates n b).symm
    (fun w => (Specht.polytabloidInt t ((Specht.rectangleAlphabetEquiv hk).symm w) : R))

/-- The bilinear coefficient covector, with no conjugation or metric choice. -/
def rectangularCovector (hk : 0 < k) (t : OAI.Saxl.Tableau n (Specht.rectangle a k))
    (b : Basis (Fin a) R M) : Module.Dual R (⨂[R] (_ : Fin n), M) where
  toFun x := ∑ w, (Specht.polytabloidInt t ((Specht.rectangleAlphabetEquiv hk).symm w) : R) *
    tensorCoordinates n b x w
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum, mul_left_comm]

@[simp]
theorem rectangularCovector_apply (hk : 0 < k)
    (t : OAI.Saxl.Tableau n (Specht.rectangle a k)) (b : Basis (Fin a) R M)
    (x : ⨂[R] (_ : Fin n), M) :
    rectangularCovector hk t b x = ∑ w,
      (Specht.polytabloidInt t ((Specht.rectangleAlphabetEquiv hk).symm w) : R) *
        tensorCoordinates n b x w := rfl

/-- The integer square sum gives a nonzero normalization in characteristic zero. -/
theorem rectangularCovector_tensor (hk : 0 < k)
    (t : OAI.Saxl.Tableau n (Specht.rectangle a k)) (b : Basis (Fin a) R M) :
    rectangularCovector hk t b (rectangularTensor hk t b) = (a.factorial : R) ^ k := by
  rw [rectangularCovector_apply, rectangularTensor, LinearEquiv.apply_symm_apply]
  simp only [← pow_two]
  have h : ∑ w, (Specht.polytabloidInt t w : R) ^ 2 =
      (Nat.card (OAI.Saxl.columnGroup t) : R) := by
    simpa only [Int.cast_sum, Int.cast_pow, Int.cast_natCast] using
      congrArg (fun z : ℤ => (z : R)) (Specht.sum_polytabloidInt_sq t)
  rw [← (Specht.rectangleAlphabetEquiv hk).symm.sum_comp] at h
  rw [h, Specht.card_rectangle_columnGroup]
  push_cast
  rfl

/-- The polytabloid lies in the actual scalar-extended integral lattice. -/
theorem rectangularTensor_mem_range (hk : 0 < k)
    (t : OAI.Saxl.Tableau n (Specht.rectangle a k)) (b : Basis (Fin a) R M) :
    rectangularTensor hk t b ∈ LinearMap.range (freeLatticeMap hk t b) := by
  refine ⟨1 ⊗ₜ[ℤ] ⟨Specht.polytabloidInt t, Specht.polytabloidInt_mem_orbitLattice t⟩, ?_⟩
  simp [rectangularTensor]

/-- Transpose covariance turns the actual polytabloid into a covariant covector. -/
theorem rectangularCovector_map (hk : 0 < k)
    (t : OAI.Saxl.Tableau n (Specht.rectangle a k)) (b : Basis (Fin a) R M)
    (f : M →ₗ[R] M) (x : ⨂[R] (_ : Fin n), M) :
    rectangularCovector hk t b (PiTensorProduct.map (fun _ => f) x) =
      (LinearMap.toMatrix b b f).det ^ k * rectangularCovector hk t b x := by
  let u := LinearMap.toMatrix b b f
  let z := fun w => (Specht.polytabloidInt t ((Specht.rectangleAlphabetEquiv hk).symm w) : R)
  rw [rectangularCovector_apply, tensorCoordinates_map]
  change (∑ w, z w * Specht.wordTensorAction n u (tensorCoordinates n b x) w) = _
  have htranspose : (∑ w, z w * Specht.wordTensorAction n u (tensorCoordinates n b x) w) =
      ∑ v, Specht.wordTensorAction n u.transpose z v * tensorCoordinates n b x v := by
    simp only [Specht.wordTensorAction, LinearMap.coe_mk, AddHom.coe_mk,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v hv
    apply Finset.sum_congr rfl
    intro w hw
    simp only [Matrix.transpose_apply]
    ring
  rw [htranspose, Specht.wordTensorAction_polytabloid hk t u.transpose]
  simp [rectangularCovector_apply, Matrix.det_transpose, Finset.mul_sum, mul_assoc, u]

end AdelicBostConjecture.Geometry
