/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.InvariantTheory.SpecialLinear.UnitaryDensity
public import BostConjecture.InvariantTheory.SpecialLinear.Detection

/-!
# Special-unitary detection of special-linear coordinate functions

The determinant normalization retraction sends unitary matrices to special
unitary matrices. Polynomial detection on unitary pairs then descends through
the existing localized coordinate retraction.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.InvariantTheory

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Polynomial detection on the product of the two compact unitary groups. -/
theorem polynomial_eq_zero_of_eval_unitary_pair
    (p : MvPolynomial ((ι × ι) ⊕ (κ × κ)) ℂ)
    (hp : ∀ (u : Matrix.unitaryGroup ι ℂ) (v : Matrix.unitaryGroup κ ℂ),
      MvPolynomial.eval (Sum.elim (Function.uncurry (u : Matrix ι ι ℂ))
        (Function.uncurry (v : Matrix κ κ ℂ))) p = 0) : p = 0 := by
  have hleft (v : Matrix.unitaryGroup κ ℂ) (x : ι × ι → ℂ) :
      MvPolynomial.eval (Sum.elim x (Function.uncurry (v : Matrix κ κ ℂ))) p = 0 := by
    let f : (ι × ι) ⊕ (κ × κ) → MvPolynomial (ι × ι) ℂ :=
      Sum.elim MvPolynomial.X (fun ij => MvPolynomial.C (v ij.1 ij.2))
    have he (y : ι × ι → ℂ) :
        MvPolynomial.eval y (MvPolynomial.eval₂ MvPolynomial.C f p) =
          MvPolynomial.eval (Sum.elim y (Function.uncurry (v : Matrix κ κ ℂ))) p := by
      rw [← MvPolynomial.eval_assoc]
      apply congrArg (fun y => MvPolynomial.eval y p)
      funext i
      cases i <;> simp [f, Function.uncurry]
    have hq := polynomial_eq_zero_of_eval_unitary
      (MvPolynomial.eval₂ MvPolynomial.C f p) (fun u => by rw [he]; exact hp u v)
    rw [← he, hq, map_zero]
  apply MvPolynomial.funext
  intro a
  let f : (ι × ι) ⊕ (κ × κ) → MvPolynomial (κ × κ) ℂ :=
    Sum.elim (fun ij => MvPolynomial.C (a (Sum.inl ij))) MvPolynomial.X
  have he (y : κ × κ → ℂ) :
      MvPolynomial.eval y (MvPolynomial.eval₂ MvPolynomial.C f p) =
        MvPolynomial.eval (Sum.elim (fun ij => a (Sum.inl ij)) y) p := by
    rw [← MvPolynomial.eval_assoc]
    apply congrArg (fun y => MvPolynomial.eval y p)
    funext i
    cases i <;> simp [f]
  have hq := polynomial_eq_zero_of_eval_unitary
    (MvPolynomial.eval₂ MvPolynomial.C f p) (fun v => by rw [he]; exact hleft v _)
  have h := he (fun ij => a (Sum.inr ij))
  have ha : Sum.elim (fun ij => a (Sum.inl ij)) (fun ij => a (Sum.inr ij)) = a := by
    funext i
    cases i <;> rfl
  simpa only [hq, map_zero, ha] using h.symm

/-- Normalizing a unitary matrix's determinant preserves unitarity. -/
theorem normalizeDetMatrix_mem_unitary (i₀ : ι) (u : Matrix.unitaryGroup ι ℂ) :
    (normalizeDetMatrix i₀ (u : Matrix ι ι ℂ)
      ((Matrix.isUnit_iff_isUnit_det _).mp (Unitary.isUnit_coe (U := u))) : Matrix ι ι ℂ) ∈
        Matrix.unitaryGroup ι ℂ := by
  let hdet := (Matrix.isUnit_iff_isUnit_det _).mp (Unitary.isUnit_coe (U := u))
  change Matrix.diagonal (fun i => if i = i₀ then (↑hdet.unit⁻¹ : ℂ) else 1) *
    (u : Matrix ι ι ℂ) ∈ Matrix.unitaryGroup ι ℂ
  apply (Matrix.unitaryGroup ι ℂ).mul_mem _ u.property
  rw [Matrix.diagonal_mem_unitary, Pi.mem_unitary_iff]
  intro i
  split_ifs
  · have hd := Matrix.det_of_mem_unitary u.property
    have hi : (↑hdet.unit⁻¹ : ℂ) = (↑u : Matrix ι ι ℂ).det⁻¹ := by
      simp
    rw [hi]
    constructor <;> simp only [star_inv₀, ← mul_inv, hd.1, hd.2, inv_one]
  · exact (unitary ℂ).one_mem

/-- Row normalization commutes with coefficient homomorphisms. -/
theorem map_normalizeDetMatrix_eq {A B : Type*} [CommRing A] [CommRing B]
    (i₀ : ι) (M : Matrix ι ι A) (hM : IsUnit M.det) (f : A →+* B) :
    (normalizeDetMatrix i₀ M hM : Matrix ι ι A).map f =
      (normalizeDetMatrix i₀ (M.map f)
        (by change IsUnit (f.mapMatrix M).det
            simpa only [← RingHom.map_det] using hM.map f) : Matrix ι ι B) := by
  let hN : IsUnit (M.map f).det := by
    change IsUnit (f.mapMatrix M).det
    simpa only [← RingHom.map_det] using hM.map f
  have hu : Units.map f hM.unit = hN.unit := Units.ext (by
    change f (↑hM.unit : A) = (↑hN.unit : B)
    rw [hM.unit_spec, hN.unit_spec]
    exact f.map_det M)
  have hi : f (↑hM.unit⁻¹ : A) = (↑hN.unit⁻¹ : B) := by
    simpa using congrArg (fun u : Bˣ => (↑u⁻¹ : B)) hu
  apply Matrix.ext
  intro i j
  change f ((Matrix.diagonal (fun k => if k = i₀ then (↑hM.unit⁻¹ : A) else 1) * M :
    Matrix ι ι A) i j) =
    (Matrix.diagonal (fun k => if k = i₀ then (↑hN.unit⁻¹ : B) else 1) *
      M.map f : Matrix ι ι B) i j
  simp only [Matrix.diagonal_mul, map_mul, Matrix.map_apply]
  split_ifs <;> simp_all

/-- Evaluation of the principal-open denominator is the product of the two determinants. -/
theorem aeval_matrixPairDeterminant (a : ((ι × ι) ⊕ (κ × κ)) → ℂ) :
    MvPolynomial.aeval a (matrixPairDeterminant ℂ ι κ) =
      (Matrix.of fun i j : ι => a (Sum.inl (i, j))).det *
      (Matrix.of fun i j : κ => a (Sum.inr (i, j))).det := by
  simp only [matrixPairDeterminant, specialLinearLeftRelation,
    specialLinearRightRelation, sub_add_cancel, map_mul]
  congr 1 <;> rw [← AlgHom.coe_toRingHom, RingHom.map_det] <;>
    congr 1 <;> ext i j <;> simp

/-- The determinant denominator never vanishes on a pair of unitary matrices. -/
theorem aeval_matrixPairDeterminant_unitary_ne_zero
    (u : Matrix.unitaryGroup ι ℂ) (v : Matrix.unitaryGroup κ ℂ) :
    MvPolynomial.aeval (Sum.elim (Function.uncurry (u : Matrix ι ι ℂ))
      (Function.uncurry (v : Matrix κ κ ℂ))) (matrixPairDeterminant ℂ ι κ) ≠ 0 := by
  rw [aeval_matrixPairDeterminant]
  exact mul_ne_zero
    ((Matrix.isUnit_iff_isUnit_det _).mp (Unitary.isUnit_coe (U := u))).ne_zero
    ((Matrix.isUnit_iff_isUnit_det _).mp (Unitary.isUnit_coe (U := v))).ne_zero

/-- Evaluation on unitary pairs detects the localized coordinate algebra of GL pairs. -/
theorem localizationPolynomialEval_detects_unitary_pair
    {z : SpecialLinearPairOpen ℂ ι κ}
    (hz : ∀ (u : Matrix.unitaryGroup ι ℂ) (v : Matrix.unitaryGroup κ ℂ),
      localizationPolynomialEval (matrixPairDeterminant ℂ ι κ)
        (Sum.elim (Function.uncurry (u : Matrix ι ι ℂ))
          (Function.uncurry (v : Matrix κ κ ℂ)))
        (aeval_matrixPairDeterminant_unitary_ne_zero u v) z = 0) : z = 0 := by
  obtain ⟨n, p, hzp⟩ := IsLocalization.Away.surj (matrixPairDeterminant ℂ ι κ) z
  have hp : p = 0 := polynomial_eq_zero_of_eval_unitary_pair p (by
    intro u v
    have he := congrArg
      (localizationPolynomialEval (matrixPairDeterminant ℂ ι κ)
        (Sum.elim (Function.uncurry (u : Matrix ι ι ℂ))
          (Function.uncurry (v : Matrix κ κ ℂ)))
        (aeval_matrixPairDeterminant_unitary_ne_zero u v)) hzp
    simpa only [map_mul, hz u v, zero_mul, localizationPolynomialEval_algebraMap,
      MvPolynomial.aeval_eq_eval] using he.symm)
  rw [hp, map_zero] at hzp
  obtain ⟨u, hu⟩ := IsLocalization.Away.algebraMap_pow_isUnit (matrixPairDeterminant ℂ ι κ) n
    (S := SpecialLinearPairOpen ℂ ι κ)
  rw [← hu] at hzp
  calc
    z = (z * (u : SpecialLinearPairOpen ℂ ι κ)) * ↑u⁻¹ := by simp [mul_assoc]
    _ = 0 := by rw [hzp, zero_mul]

/-- Special-unitary pairs detect the actual coordinate algebra of special-linear pairs.
The chosen indices are available in the positive-dimensional case needed for a nonzero
subspace of a tensor product. -/
theorem specialLinearPairEval_detects_of_unitary (i₀ : ι) (j₀ : κ)
    {a : SpecialLinearPairCoordinateRing ℂ ι κ}
    (ha : ∀ g : Matrix.SpecialLinearGroup ι ℂ × Matrix.SpecialLinearGroup κ ℂ,
      (g.1 : Matrix ι ι ℂ) ∈ Matrix.unitaryGroup ι ℂ →
      (g.2 : Matrix κ κ ℂ) ∈ Matrix.unitaryGroup κ ℂ →
      specialLinearPairEval g a = 0) : a = 0 := by
  apply specialLinearNormalization_injective ℂ ι κ i₀ j₀
  rw [map_zero]
  apply localizationPolynomialEval_detects_unitary_pair
  intro u v
  let f := localizationPolynomialEval (matrixPairDeterminant ℂ ι κ)
    (Sum.elim (Function.uncurry (u : Matrix ι ι ℂ))
      (Function.uncurry (v : Matrix κ κ ℂ)))
    (aeval_matrixPairDeterminant_unitary_ne_zero u v)
  let e := f.comp (specialLinearNormalization ℂ ι κ i₀ j₀)
  have hl : (universalLeftMatrix ℂ ι κ).map f = (u : Matrix ι ι ℂ) := by
    ext i j
    simp [universalLeftMatrix, f, Function.uncurry]
  have hr : (universalRightMatrix ℂ ι κ).map f = (v : Matrix κ κ ℂ) := by
    ext i j
    simp [universalRightMatrix, f, Function.uncurry]
  have hpl : ((specialLinearPairPoint e).1 : Matrix ι ι ℂ) =
      (normalizeDetMatrix i₀ (universalLeftMatrix ℂ ι κ)
        (isUnit_det_universalLeftMatrix ℂ ι κ) :
        Matrix ι ι (SpecialLinearPairOpen ℂ ι κ)).map f := by
    ext i j
    change f (specialLinearPairEval (K := ℂ)
      (normalizeDetMatrix i₀ (universalLeftMatrix ℂ ι κ) (isUnit_det_universalLeftMatrix ℂ ι κ),
       normalizeDetMatrix j₀ (universalRightMatrix ℂ ι κ) (isUnit_det_universalRightMatrix ℂ ι κ))
      (Ideal.Quotient.mkₐ ℂ (specialLinearPairIdeal ℂ ι κ) (MvPolynomial.X (Sum.inl (i, j))))) = _
    rw [specialLinearPairEval_mk]
    simp only [MvPolynomial.aeval_X, Sum.elim_inl]
    rfl
  have hpr : ((specialLinearPairPoint e).2 : Matrix κ κ ℂ) =
      (normalizeDetMatrix j₀ (universalRightMatrix ℂ ι κ)
        (isUnit_det_universalRightMatrix ℂ ι κ) :
        Matrix κ κ (SpecialLinearPairOpen ℂ ι κ)).map f := by
    ext i j
    change f (specialLinearPairEval (K := ℂ)
      (normalizeDetMatrix i₀ (universalLeftMatrix ℂ ι κ) (isUnit_det_universalLeftMatrix ℂ ι κ),
       normalizeDetMatrix j₀ (universalRightMatrix ℂ ι κ) (isUnit_det_universalRightMatrix ℂ ι κ))
      (Ideal.Quotient.mkₐ ℂ (specialLinearPairIdeal ℂ ι κ) (MvPolynomial.X (Sum.inr (i, j))))) = _
    rw [specialLinearPairEval_mk]
    simp only [MvPolynomial.aeval_X, Sum.elim_inr]
    rfl
  change (universalLeftMatrix ℂ ι κ).map f.toRingHom = (u : Matrix ι ι ℂ) at hl
  change (universalRightMatrix ℂ ι κ).map f.toRingHom = (v : Matrix κ κ ℂ) at hr
  have h := ha (specialLinearPairPoint e) (by
    rw [hpl]
    have hn := map_normalizeDetMatrix_eq i₀ (universalLeftMatrix ℂ ι κ)
      (isUnit_det_universalLeftMatrix ℂ ι κ) f.toRingHom
    have hn' := congrArg (fun M : Matrix ι ι ℂ => M ∈ Matrix.unitaryGroup ι ℂ) hn
    apply Eq.mpr hn'
    simpa only [hl] using normalizeDetMatrix_mem_unitary i₀ u) (by
    rw [hpr]
    have hn := map_normalizeDetMatrix_eq j₀ (universalRightMatrix ℂ ι κ)
      (isUnit_det_universalRightMatrix ℂ ι κ) f.toRingHom
    have hn' := congrArg (fun M : Matrix κ κ ℂ => M ∈ Matrix.unitaryGroup κ ℂ) hn
    apply Eq.mpr hn'
    simpa only [hr] using normalizeDetMatrix_mem_unitary j₀ v)
  rwa [specialLinearPairEval_point] at h

end BostConjecture.InvariantTheory
