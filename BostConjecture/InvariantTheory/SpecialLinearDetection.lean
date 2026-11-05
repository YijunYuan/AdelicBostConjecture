module

public import BostConjecture.InvariantTheory.SpecialLinearCoordinates
public import BostConjecture.InvariantTheory.LocalizationDetection

/-!
# Rational-point detection for pairs of special linear groups

The determinant-one coordinate algebra embeds into the polynomial algebra
localized at the product of determinants, using determinant normalization
of one row of each universal matrix. Principal-open detection then applies.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.InvariantTheory

section Normalize

variable {A B ι : Type*} [CommRing A] [CommRing B] [Fintype ι] [DecidableEq ι]

/-- Normalize one row of an invertible matrix so that its determinant is one. -/
def normalizeDetMatrix (i₀ : ι) (M : Matrix ι ι A) (hM : IsUnit M.det) :
    Matrix.SpecialLinearGroup ι A :=
  ⟨Matrix.diagonal (fun i => if i = i₀ then (↑hM.unit⁻¹ : A) else 1) * M, by
    rw [Matrix.det_mul, Matrix.det_diagonal]
    simp only [Finset.prod_ite_eq', Finset.mem_univ, ite_true]
    simpa only [hM.unit_spec] using hM.unit.inv_mul⟩

/-- A specialization on which the determinant is one cancels the normalization. -/
theorem map_normalizeDetMatrix (i₀ : ι) (M : Matrix ι ι A) (hM : IsUnit M.det)
    (f : A →+* B) (hf : f M.det = 1) :
    (normalizeDetMatrix i₀ M hM : Matrix ι ι A).map f = M.map f := by
  have hu : f (↑hM.unit : A) = 1 := by simpa only [hM.unit_spec] using hf
  have hi : f (↑hM.unit⁻¹ : A) = 1 := by
    have h := congrArg f hM.unit.inv_mul
    simpa only [map_mul, hu, mul_one, map_one] using h
  change (Matrix.diagonal _ * M).map f = M.map f
  rw [Matrix.map_mul]
  have hd : (Matrix.diagonal (fun i => if i = i₀ then (↑hM.unit⁻¹ : A) else 1)).map f =
      (1 : Matrix ι ι B) := by
    ext i j
    by_cases h : i = j <;> simp [h, Matrix.one_apply, hi, apply_ite]
  rw [hd, Matrix.one_mul]

end Normalize

section Retraction

variable (K ι κ : Type*) [Field K] [Fintype ι] [Fintype κ]
  [DecidableEq ι] [DecidableEq κ]

/-- The polynomial cutting out the complement of the two general linear groups. -/
def matrixPairDeterminant : MvPolynomial ((ι × ι) ⊕ (κ × κ)) K :=
  (specialLinearLeftRelation K ι κ + 1) * (specialLinearRightRelation K ι κ + 1)

/-- The coordinate algebra of the principal open of two invertible matrices. -/
abbrev SpecialLinearPairOpen := Localization.Away (matrixPairDeterminant K ι κ)

theorem quotient_leftRelation :
    Ideal.Quotient.mkₐ K (specialLinearPairIdeal K ι κ) (specialLinearLeftRelation K ι κ) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

theorem quotient_rightRelation :
    Ideal.Quotient.mkₐ K (specialLinearPairIdeal K ι κ) (specialLinearRightRelation K ι κ) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

theorem quotient_matrixPairDeterminant :
    Ideal.Quotient.mkₐ K (specialLinearPairIdeal K ι κ) (matrixPairDeterminant K ι κ) = 1 := by
  rw [matrixPairDeterminant, map_mul, map_add, map_add, quotient_leftRelation,
    quotient_rightRelation, map_one, zero_add, one_mul]

/-- Restriction of functions on the general-linear open to determinant-one matrices. -/
def specialLinearOpenQuotient :
    SpecialLinearPairOpen K ι κ →ₐ[K] SpecialLinearPairCoordinateRing K ι κ :=
  IsLocalization.Away.liftAlgHom (matrixPairDeterminant K ι κ)
    (f := Ideal.Quotient.mkₐ K (specialLinearPairIdeal K ι κ))
    (by rw [quotient_matrixPairDeterminant]; exact isUnit_one)

@[simp]
theorem specialLinearOpenQuotient_algebraMap
    (p : MvPolynomial ((ι × ι) ⊕ (κ × κ)) K) :
    specialLinearOpenQuotient K ι κ (algebraMap _ (SpecialLinearPairOpen K ι κ) p) =
      Ideal.Quotient.mkₐ K (specialLinearPairIdeal K ι κ) p := by
  exact IsLocalization.Away.lift_eq _
    (show IsUnit (Ideal.Quotient.mkₐ K (specialLinearPairIdeal K ι κ)
      (matrixPairDeterminant K ι κ)) from by
        rw [quotient_matrixPairDeterminant]; exact isUnit_one) p

/-- The first universal matrix on the general-linear principal open. -/
def universalLeftMatrix : Matrix ι ι (SpecialLinearPairOpen K ι κ) :=
  fun i j => algebraMap (MvPolynomial ((ι × ι) ⊕ (κ × κ)) K) (SpecialLinearPairOpen K ι κ)
    (MvPolynomial.X (Sum.inl (i, j)))

/-- The second universal matrix on the general-linear principal open. -/
def universalRightMatrix : Matrix κ κ (SpecialLinearPairOpen K ι κ) :=
  fun i j => algebraMap (MvPolynomial ((ι × ι) ⊕ (κ × κ)) K) (SpecialLinearPairOpen K ι κ)
    (MvPolynomial.X (Sum.inr (i, j)))

theorem det_universalLeftMatrix :
    (universalLeftMatrix K ι κ).det = algebraMap _ (SpecialLinearPairOpen K ι κ)
      (specialLinearLeftRelation K ι κ + 1) := by
  rw [specialLinearLeftRelation, sub_add_cancel]
  exact (RingHom.map_det
    (algebraMap (MvPolynomial ((ι × ι) ⊕ (κ × κ)) K) (SpecialLinearPairOpen K ι κ))
    (Matrix.of fun i j : ι => MvPolynomial.X (Sum.inl (i, j)))).symm

theorem det_universalRightMatrix :
    (universalRightMatrix K ι κ).det = algebraMap _ (SpecialLinearPairOpen K ι κ)
      (specialLinearRightRelation K ι κ + 1) := by
  rw [specialLinearRightRelation, sub_add_cancel]
  exact (RingHom.map_det
    (algebraMap (MvPolynomial ((ι × ι) ⊕ (κ × κ)) K) (SpecialLinearPairOpen K ι κ))
    (Matrix.of fun i j : κ => MvPolynomial.X (Sum.inr (i, j)))).symm

theorem isUnit_det_universalLeftMatrix : IsUnit (universalLeftMatrix K ι κ).det := by
  rw [det_universalLeftMatrix]
  exact IsLocalization.Away.isUnit_of_dvd (matrixPairDeterminant K ι κ) (dvd_mul_right _ _)

theorem isUnit_det_universalRightMatrix : IsUnit (universalRightMatrix K ι κ).det := by
  rw [det_universalRightMatrix]
  exact IsLocalization.Away.isUnit_of_dvd (matrixPairDeterminant K ι κ) (dvd_mul_left _ _)

/-- Pullback by the row-normalization retraction from GL pairs to SL pairs. -/
def specialLinearNormalization (i₀ : ι) (j₀ : κ) :
    SpecialLinearPairCoordinateRing K ι κ →ₐ[K] SpecialLinearPairOpen K ι κ :=
  specialLinearPairEval
    (normalizeDetMatrix i₀ (universalLeftMatrix K ι κ) (isUnit_det_universalLeftMatrix K ι κ),
     normalizeDetMatrix j₀ (universalRightMatrix K ι κ) (isUnit_det_universalRightMatrix K ι κ))

theorem specialLinearOpenQuotient_det_left :
    specialLinearOpenQuotient K ι κ (universalLeftMatrix K ι κ).det = 1 := by
  rw [det_universalLeftMatrix, specialLinearOpenQuotient_algebraMap, map_add,
    quotient_leftRelation, map_one, zero_add]

theorem specialLinearOpenQuotient_det_right :
    specialLinearOpenQuotient K ι κ (universalRightMatrix K ι κ).det = 1 := by
  rw [det_universalRightMatrix, specialLinearOpenQuotient_algebraMap, map_add,
    quotient_rightRelation, map_one, zero_add]

/-- Restriction to determinant-one matrices is a left inverse to normalization pullback. -/
theorem specialLinearOpenQuotient_comp_normalization (i₀ : ι) (j₀ : κ) :
    (specialLinearOpenQuotient K ι κ).comp (specialLinearNormalization K ι κ i₀ j₀) =
      AlgHom.id K (SpecialLinearPairCoordinateRing K ι κ) := by
  let q := Ideal.Quotient.mkₐ K (specialLinearPairIdeal K ι κ)
  let r := specialLinearOpenQuotient K ι κ
  have hl := map_normalizeDetMatrix i₀ (universalLeftMatrix K ι κ)
    (isUnit_det_universalLeftMatrix K ι κ) r.toRingHom
    (specialLinearOpenQuotient_det_left K ι κ)
  have hr := map_normalizeDetMatrix j₀ (universalRightMatrix K ι κ)
    (isUnit_det_universalRightMatrix K ι κ) r.toRingHom
    (specialLinearOpenQuotient_det_right K ι κ)
  have h : (r.comp (specialLinearNormalization K ι κ i₀ j₀)).comp q = q := by
    apply MvPolynomial.algHom_ext
    intro ij
    cases ij with
    | inl ij =>
      have hc := congrArg (fun M : Matrix ι ι (SpecialLinearPairCoordinateRing K ι κ) =>
        M ij.1 ij.2) hl
      change r ((normalizeDetMatrix i₀ (universalLeftMatrix K ι κ)
        (isUnit_det_universalLeftMatrix K ι κ)) ij.1 ij.2) = q (MvPolynomial.X (Sum.inl ij))
      exact hc.trans (specialLinearOpenQuotient_algebraMap K ι κ _)
    | inr ij =>
      have hc := congrArg (fun M : Matrix κ κ (SpecialLinearPairCoordinateRing K ι κ) =>
        M ij.1 ij.2) hr
      change r ((normalizeDetMatrix j₀ (universalRightMatrix K ι κ)
        (isUnit_det_universalRightMatrix K ι κ)) ij.1 ij.2) = q (MvPolynomial.X (Sum.inr ij))
      exact hc.trans (specialLinearOpenQuotient_algebraMap K ι κ _)
  ext a
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective K (specialLinearPairIdeal K ι κ) a
  exact DFunLike.congr_fun h p

theorem specialLinearNormalization_injective (i₀ : ι) (j₀ : κ) :
    Function.Injective (specialLinearNormalization K ι κ i₀ j₀) := by
  apply Function.LeftInverse.injective (f := specialLinearNormalization K ι κ i₀ j₀)
    (g := specialLinearOpenQuotient K ι κ)
  intro a
  exact DFunLike.congr_fun (specialLinearOpenQuotient_comp_normalization K ι κ i₀ j₀) a

theorem matrixPairDeterminant_ne_zero : matrixPairDeterminant K ι κ ≠ 0 := by
  intro h
  have he := congrArg
    (specialLinearPairEval (K := K)
      ((1 : Matrix.SpecialLinearGroup ι K), (1 : Matrix.SpecialLinearGroup κ K)))
    (quotient_matrixPairDeterminant K ι κ)
  rw [h, map_zero, map_zero, map_one] at he
  exact zero_ne_one he

/-- Actual rational special-linear points detect their coordinate algebra over an infinite field. -/
theorem specialLinearPairEval_detects [Infinite K] (i₀ : ι) (j₀ : κ)
    {a : SpecialLinearPairCoordinateRing K ι κ}
    (ha : ∀ g : Matrix.SpecialLinearGroup ι K × Matrix.SpecialLinearGroup κ K,
      specialLinearPairEval g a = 0) : a = 0 := by
  apply specialLinearNormalization_injective K ι κ i₀ j₀
  rw [map_zero]
  apply localizationPolynomialEval_detects (matrixPairDeterminant_ne_zero K ι κ)
  intro x hx
  let e := (localizationPolynomialEval (matrixPairDeterminant K ι κ) x hx).comp
    (specialLinearNormalization K ι κ i₀ j₀)
  have h := ha (specialLinearPairPoint e)
  rw [specialLinearPairEval_point] at h
  exact h

end Retraction

end BostConjecture.InvariantTheory
