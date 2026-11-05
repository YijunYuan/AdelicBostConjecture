module

public import BostConjecture.Specht.PrefixDistribution
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# Closed rectangular prefix normalizer

The shifted hook count and a finite factorial identity evaluate the
Vandermonde-weighted labelled occupancy sum.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Specht

open OAI.Saxl Finset

private theorem rowLen_empty (r : ℕ) : (⊥ : YoungDiagram).rowLen r = 0 := by
  apply eq_of_forall_lt_iff
  intro q
  rw [← YoungDiagram.mem_iff_lt_rowLen]
  simp

private theorem colLen_empty : (⊥ : YoungDiagram).colLen 0 = 0 := by
  apply eq_of_forall_lt_iff
  intro r
  rw [← YoungDiagram.mem_iff_lt_colLen]
  simp

/-- The rectangular shifted Vandermonde is the fixed staircase factorial product. -/
theorem shiftedVandermonde_rectangle (a k : ℕ) :
    (∏ r ∈ range a, ∏ j ∈ Ioo r a,
      (shiftedRowLength (rectangle a k) a r - shiftedRowLength (rectangle a k) a j)) =
    ∏ j ∈ range a, j.factorial := by
  have h := hookProduct_mul_shiftedVandermonde (⊥ : YoungDiagram) (a := a)
    (by rw [colLen_empty]; exact Nat.zero_le a)
  simp only [YoungDiagram.cells_bot, prod_empty, one_mul] at h
  calc
    _ = ∏ r ∈ range a, ∏ j ∈ Ioo r a,
        (shiftedRowLength (⊥ : YoungDiagram) a r - shiftedRowLength (⊥ : YoungDiagram) a j) := by
      apply prod_congr rfl
      intro r hr
      apply prod_congr rfl
      intro j hj
      have hr' := mem_range.mp hr
      have hj' := (mem_Ioo.mp hj).2
      simp only [shiftedRowLength, rowLen_rectangle hr', rowLen_rectangle hj', rowLen_empty]
      omega
    _ = ∏ r ∈ range a, (a - 1 - r).factorial := by
      rw [h]
      apply prod_congr rfl
      intro r _
      simp only [shiftedRowLength, rowLen_empty, zero_add]
      congr 1
      omega
    _ = _ := prod_range_reflect Nat.factorial a

/-- Shifted row factorials in a rectangle are a reversed consecutive product. -/
theorem shiftedFactorials_rectangle (a k : ℕ) :
    (∏ r ∈ range a, (shiftedRowLength (rectangle a k) a r).factorial) =
      ∏ j ∈ range a, (k + j).factorial := by
  calc
    _ = ∏ r ∈ range a, (k + (a - 1 - r)).factorial := by
      apply prod_congr rfl
      intro r hr
      have hr' := mem_range.mp hr
      rw [shiftedRowLength, rowLen_rectangle hr']
      congr 1
      omega
    _ = _ := prod_range_reflect (fun j => (k + j).factorial) a

/-- The rectangular tableau count in ordinary consecutive factorials. -/
theorem card_standard_rectangle_eq_factorials (a : ℕ) {k : ℕ} (hk : 0 < k) :
    (Fintype.card {T : Tableau (a * k) (rectangle a k) // IsStandard T} : ℝ) =
      ((a * k).factorial : ℝ) * (∏ j ∈ range a, (j.factorial : ℝ)) /
        (∏ j ∈ range a, ((k + j).factorial : ℝ)) := by
  have h := card_standard_mul_shiftedFactorials (rectangle a k) (card_rectangle a k)
    (show (rectangle a k).colLen 0 ≤ a by rw [colLen_rectangle hk])
  rw [shiftedFactorials_rectangle, shiftedVandermonde_rectangle] at h
  apply (eq_div_iff (by positivity)).mpr
  exact_mod_cast h

/-- The factorial ratio appearing in the normalizer is a polynomial product. -/
theorem factorial_pow_eq_shiftedFactorials_mul_powers {k : ℕ} (hk : 0 < k) (a : ℕ) :
    (k + a - 1).factorial ^ a =
      (∏ j ∈ range a, (k + j).factorial) * (∏ j ∈ range a, (k + j) ^ j) := by
  induction a with
  | zero => simp
  | succ a ih =>
    have hf : (k + a).factorial = (k + a) * (k + a - 1).factorial := by
      have hp : k + a = (k + a - 1) + 1 := by omega
      conv_lhs => rw [hp, Nat.factorial_succ]
      congr 1
      omega
    simp only [Nat.add_succ_sub_one, prod_range_succ, pow_succ]
    calc
      _ = ((k + a - 1).factorial ^ a) * ((k + a) ^ a) * (k + a).factorial := by
        rw [hf, mul_pow]
        ring
      _ = _ := by rw [ih]; ring

/-- Closed finite-product normalizer of the labelled Vandermonde law. -/
theorem sum_occupancyWeight_eq_closed (a : ℕ) {k : ℕ} (hk : 0 < k)
    (m l : ℕ) (hml : m + l = a * k) :
    ∑ b : Occupancy a (k + a - 1) (m + staircaseSum a), occupancyWeight b =
      (a.factorial : ℝ) * (∏ j ∈ range a, (j.factorial : ℝ)) *
        (∏ j ∈ range a, (k + j : ℝ) ^ j) * ((a * k).choose m : ℝ) /
        ((a * (k + a - 1)).choose (m + staircaseSum a) : ℝ) := by
  rw [sum_occupancyWeight_eq_tableau_count a k m l hml, hml,
    card_standard_rectangle_eq_factorials a hk]
  have hf : ((k + a - 1).factorial : ℝ) ^ a =
      (∏ j ∈ range a, ((k + j).factorial : ℝ)) *
        (∏ j ∈ range a, (k + j : ℝ) ^ j) := by
    exact_mod_cast factorial_pow_eq_shiftedFactorials_mul_powers hk a
  have hb : ((a * k).factorial : ℝ) =
      ((a * k).choose m : ℝ) * (m.factorial : ℝ) * (l.factorial : ℝ) := by
    have h := Nat.choose_mul_factorial_mul_factorial (show m ≤ a * k by omega)
    have hs : a * k - m = l := by omega
    rw [hs] at h
    exact_mod_cast h.symm
  rw [hf, hb]
  have hm : (m.factorial : ℝ) ≠ 0 := by positivity
  have hl : (l.factorial : ℝ) ≠ 0 := by positivity
  have hp : (∏ j ∈ range a, ((k + j).factorial : ℝ)) ≠ 0 := by positivity
  field_simp

theorem staircaseSum_eq (a : ℕ) : staircaseSum a = a * (a - 1) / 2 := by
  unfold staircaseSum
  rw [Fin.sum_univ_eq_sum_range (fun i => a - i - 1) a]
  have hs : (∑ i ∈ range a, (a - i - 1)) = ∑ i ∈ range a, (a - 1 - i) := by
    apply sum_congr rfl
    intro i _
    omega
  rw [hs, sum_range_reflect (fun i => i), sum_range_id]

theorem two_mul_staircaseSum (a : ℕ) : 2 * staircaseSum a = a * (a - 1) := by
  have hs : staircaseSum a = ∑ i ∈ range a, i := by
    rw [staircaseSum_eq, sum_range_id]
  rw [hs, mul_comm, sum_range_id_mul_two]

theorem rectangle_occupancy_population (a k : ℕ) :
    a * (k + a - 1) = a * k + 2 * staircaseSum a := by
  rw [two_mul_staircaseSum]
  cases a with
  | zero => simp
  | succ a => simp only [Nat.add_succ_sub_one, Nat.add_sub_cancel]; ring

/-- The rectangular tableau set has positive cardinality, from its checked hook count. -/
theorem card_standard_rectangle_pos (a : ℕ) {k : ℕ} (hk : 0 < k) :
    0 < (Fintype.card {T : Tableau (a * k) (rectangle a k) // IsStandard T} : ℝ) := by
  rw [card_standard_rectangle_eq_factorials a hk]
  positivity

/-- The weighted normalizer is strictly positive throughout the valid prefix range. -/
theorem sum_occupancyWeight_pos (a : ℕ) {k : ℕ} (hk : 0 < k)
    (m l : ℕ) (hml : m + l = a * k) :
    0 < ∑ b : Occupancy a (k + a - 1) (m + staircaseSum a), occupancyWeight b := by
  rw [sum_occupancyWeight_eq_tableau_count a k m l hml, hml]
  have hF := card_standard_rectangle_pos a hk
  have hA : m + staircaseSum a ≤ a * (k + a - 1) := by
    rw [rectangle_occupancy_population]
    omega
  have hC : (0 : ℝ) < ((a * (k + a - 1)).choose (m + staircaseSum a) : ℝ) := by
    exact_mod_cast Nat.choose_pos hA
  positivity

/-- The actual uniform tableau prefix law is obtained by weighting and sorting
the labelled occupancy law. -/
theorem rectanglePrefix_probability_eq_weighted (a : ℕ) {k : ℕ} (hk : 0 < k)
    (m l : ℕ) (hml : m + l = a * k) (μ : RectangleShape a k m) :
    (Nat.card {T : {T : Tableau (m + l) (rectangle a k) // IsStandard T} //
      prefixShape T.property m (Nat.le_add_right m l) = μ.val} : ℝ) /
      (Fintype.card {T : Tableau (m + l) (rectangle a k) // IsStandard T} : ℝ) =
    (a.factorial : ℝ) * occupancyWeight (rectangleShapeOccupancy μ).val /
      (∑ b : Occupancy a (k + a - 1) (m + staircaseSum a), occupancyWeight b) := by
  have hF : (Fintype.card {T : Tableau (m + l) (rectangle a k) // IsStandard T} : ℝ) ≠ 0 := by
    rw [hml]
    exact (card_standard_rectangle_pos a hk).ne'
  have hA : m + staircaseSum a ≤ a * (k + a - 1) := by
    rw [rectangle_occupancy_population]
    omega
  have hC : ((a * (k + a - 1)).choose (m + staircaseSum a) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hA).ne'
  have ha : (a.factorial : ℝ) ≠ 0 := by positivity
  have hm : (m.factorial : ℝ) ≠ 0 := by positivity
  have hl : (l.factorial : ℝ) ≠ 0 := by positivity
  have hp : ((k + a - 1).factorial : ℝ) ^ a ≠ 0 := by positivity
  rw [occupancyWeight_rectangleShape a k m l hml,
    sum_occupancyWeight_eq_tableau_count a k m l hml]
  field_simp

end BostConjecture.Specht
