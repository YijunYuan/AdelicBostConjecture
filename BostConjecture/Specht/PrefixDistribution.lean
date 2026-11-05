module

public import BostConjecture.Specht.ShiftedShapes
public import BostConjecture.Specht.PrefixWeights

/-!
# Normalizing the rectangular prefix distribution

The actual prefix fibers partition the standard tableaux. Via the shifted
shape equivalence this evaluates the labelled squared-Vandermonde mass.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Specht

open OAI.Saxl Finset

/-- The prefix shape as an element of the finite set of rectangular subdiagrams. -/
def rectanglePrefixShape (a k m l : ℕ)
    (T : {T : Tableau (m + l) (rectangle a k) // IsStandard T}) : RectangleShape a k m :=
  ⟨prefixShape T.property m (Nat.le_add_right m l),
    prefixShape_le T.property m (Nat.le_add_right m l),
    card_prefixShape T.property m (Nat.le_add_right m l)⟩

/-- The actual prefix fibers partition all standard rectangular tableaux. -/
theorem sum_card_rectanglePrefix (a k m l : ℕ) :
    ∑ μ : RectangleShape a k m,
      Nat.card {T : {T : Tableau (m + l) (rectangle a k) // IsStandard T} //
        prefixShape T.property m (Nat.le_add_right m l) = μ.val} =
      Fintype.card {T : Tableau (m + l) (rectangle a k) // IsStandard T} := by
  classical
  have h := Fintype.card_congr (Equiv.sigmaFiberEquiv (rectanglePrefixShape a k m l))
  simpa only [Fintype.card_sigma, rectanglePrefixShape, Subtype.ext_iff,
    Nat.card_eq_fintype_card] using h

private theorem prod_shiftedDifferences_fin (μ : YoungDiagram) (a : ℕ) :
    (∏ r ∈ range a, ∏ j ∈ Ioo r a,
      ((shiftedRowLength μ a r - shiftedRowLength μ a j : ℕ) : ℝ)) =
    ∏ i : Fin a, ∏ j ∈ Ioi i,
      ((shiftedRowLength μ a i.val - shiftedRowLength μ a j.val : ℕ) : ℝ) := by
  have h (r : ℕ) : Ioo r a = (range a).filter (r < ·) := by ext j; simp; omega
  simp_rw [h, prod_filter]
  rw [← Fin.prod_univ_eq_prod_range]
  apply prod_congr rfl
  intro i _
  rw [← Fin.prod_univ_eq_prod_range, ← prod_filter]
  congr 1
  ext j
  simp

/-- The squared determinant is the positive shifted-difference product squared. -/
theorem det_vandermonde_shifted_sq (μ : YoungDiagram) (a : ℕ) :
    (Matrix.vandermonde (fun i : Fin a => (shiftedRowLength μ a i.val : ℝ))).det ^ 2 =
      (∏ r ∈ range a, ∏ j ∈ Ioo r a,
        ((shiftedRowLength μ a r - shiftedRowLength μ a j : ℕ) : ℝ)) ^ 2 := by
  rw [prod_shiftedDifferences_fin, Matrix.det_vandermonde]
  simp_rw [← prod_pow]
  apply prod_congr rfl
  intro i _
  apply prod_congr rfl
  intro j hj
  have hij' : i < j := mem_Ioi.mp hj
  have hij := shiftedRowLength_strictAnti μ hij' j.isLt
  rw [Nat.cast_sub hij.le]
  ring

/-- The weight of a shifted shape is the actual fiber count times a common factor. -/
theorem occupancyWeight_rectangleShape (a k m l : ℕ) (hml : m + l = a * k)
    (μ : RectangleShape a k m) :
    occupancyWeight (rectangleShapeOccupancy μ).val =
      (Nat.card {T : {T : Tableau (m + l) (rectangle a k) // IsStandard T} //
        prefixShape T.property m (Nat.le_add_right m l) = μ.val} : ℝ) *
        ((k + a - 1).factorial : ℝ) ^ a /
      ((m.factorial : ℝ) * (l.factorial : ℝ) *
        ((a * (k + a - 1)).choose (m + staircaseSum a) : ℝ)) := by
  have hl : (rectangleComplement μ.val a k).card = l := by
    have hc := card_add_card_rectangleComplement μ.property.1
    rw [μ.property.2] at hc
    omega
  have hc := card_rectanglePrefix_mul_factorial_pow μ.property.1 μ.property.2 hl
  have hc' :
      (Nat.card {T : {T : Tableau (m + l) (rectangle a k) // IsStandard T} //
        prefixShape T.property m (Nat.le_add_right m l) = μ.val} : ℝ) *
        ((k + a - 1).factorial : ℝ) ^ a =
      ((m.factorial : ℝ) * (l.factorial : ℝ) *
        (∏ r ∈ range a, ∏ j ∈ Ioo r a,
          ((shiftedRowLength μ.val a r - shiftedRowLength μ.val a j : ℕ) : ℝ)) ^ 2) *
        (∏ r ∈ range a, ((k + a - 1).choose (shiftedRowLength μ.val a r) : ℝ)) := by
    exact_mod_cast hc
  unfold occupancyWeight occupancyMass
  simp_rw [rectangleShapeOccupancy_apply]
  rw [det_vandermonde_shifted_sq,
    Fin.prod_univ_eq_prod_range (fun r => ((k + a - 1).choose (shiftedRowLength μ.val a r) : ℝ)), hc']
  have hm : (m.factorial : ℝ) ≠ 0 := by positivity
  have hl' : (l.factorial : ℝ) ≠ 0 := by positivity
  rw [div_mul_eq_div_div]
  field_simp

/-- Exact normalization in terms of the checked rectangular tableau count. -/
theorem sum_occupancyWeight_eq_tableau_count (a k m l : ℕ) (hml : m + l = a * k) :
    ∑ b : Occupancy a (k + a - 1) (m + staircaseSum a), occupancyWeight b =
      (a.factorial : ℝ) *
        (Fintype.card {T : Tableau (m + l) (rectangle a k) // IsStandard T} : ℝ) *
        ((k + a - 1).factorial : ℝ) ^ a /
      ((m.factorial : ℝ) * (l.factorial : ℝ) *
        ((a * (k + a - 1)).choose (m + staircaseSum a) : ℝ)) := by
  rw [sum_occupancyWeight_eq_factorial_mul_sorted,
    ← (rectangleShapeEquivSortedOccupancy a k m).sum_comp]
  simp_rw [show ∀ μ : RectangleShape a k m,
    (rectangleShapeEquivSortedOccupancy a k m) μ = rectangleShapeOccupancy μ from fun _ => rfl,
    occupancyWeight_rectangleShape a k m l hml]
  rw [← sum_div, ← sum_mul]
  have hc :
      (∑ μ : RectangleShape a k m,
        (Nat.card {T : {T : Tableau (m + l) (rectangle a k) // IsStandard T} //
          prefixShape T.property m (Nat.le_add_right m l) = μ.val} : ℝ)) =
      (Fintype.card {T : Tableau (m + l) (rectangle a k) // IsStandard T} : ℝ) := by
    exact_mod_cast sum_card_rectanglePrefix a k m l
  rw [hc]
  ring

end BostConjecture.Specht
