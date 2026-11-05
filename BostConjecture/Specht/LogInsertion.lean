module

public import BostConjecture.Specht.PrefixEvent
public import BostConjecture.Specht.Seminormal

/-!
# Logarithmic insertion estimates for the actual seminormal product
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Specht

open OAI.Saxl Finset

private theorem log_ratio_bounds {x : ℝ} (hx : 2 ≤ x) :
    0 ≤ Real.log (x / (x - 1)) ∧
      Real.log (x / (x - 1)) ≤ Real.log 2 ∧
      Real.log (x / (x - 1)) ≤ 1 / (x - 1) := by
  have hd : 0 < x - 1 := by linarith
  have hp : 0 < x / (x - 1) := div_pos (by linarith) hd
  refine ⟨Real.log_nonneg ((le_div_iff₀ hd).mpr (by linarith)),
    Real.log_le_log hp ((div_le_iff₀ hd).mpr (by linarith)), ?_⟩
  calc
    _ ≤ x / (x - 1) - 1 := Real.log_le_sub_one_of_pos hp
    _ = _ := by field_simp; ring

/-- The log of an insertion is the sum of the logs of its positive factors. -/
theorem log_prefixInsertionFactor {n : ℕ} {μ : YoungDiagram} {t : Tableau n μ}
    (ht : IsStandard t) (m : Fin n) :
    Real.log (prefixInsertionFactor t m) = ∑ r ∈ range (t m).val.1,
      Real.log ((prefixAxialDistance t m r : ℝ) / ((prefixAxialDistance t m r : ℝ) - 1)) := by
  apply Real.log_prod
  intro r hr
  have hd : (2 : ℝ) ≤ prefixAxialDistance t m r := by
    exact_mod_cast two_le_prefixAxialDistance ht m r (mem_range.mp hr)
  exact (div_pos (by linarith) (by linarith : (0 : ℝ) < prefixAxialDistance t m r - 1)).ne'

/-- Uniform nonnegativity of every logarithmic insertion. -/
theorem log_prefixInsertionFactor_nonneg {n : ℕ} {μ : YoungDiagram} {t : Tableau n μ}
    (ht : IsStandard t) (m : Fin n) : 0 ≤ Real.log (prefixInsertionFactor t m) := by
  rw [log_prefixInsertionFactor ht]
  apply sum_nonneg
  intro r hr
  exact (log_ratio_bounds (by exact_mod_cast two_le_prefixAxialDistance ht m r (mem_range.mp hr))).1

/-- The uniform logarithmic insertion bound in a rectangle with `a` rows. -/
theorem log_prefixInsertionFactor_le {n a k : ℕ} {t : Tableau n (rectangle a k)}
    (ht : IsStandard t) (m : Fin n) :
    Real.log (prefixInsertionFactor t m) ≤ (a - 1 : ℕ) * Real.log 2 := by
  rw [log_prefixInsertionFactor ht]
  calc
    _ ≤ ∑ _r ∈ range (t m).val.1, Real.log 2 := sum_le_sum (fun r hr =>
      (log_ratio_bounds (by exact_mod_cast two_le_prefixAxialDistance ht m r (mem_range.mp hr))).2.1)
    _ = ((t m).val.1 : ℝ) * Real.log 2 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by
      exact_mod_cast Nat.le_sub_one_of_lt (mem_rectangle.mp (t m).property).1)
        (Real.log_nonneg (by norm_num))

/-- An insertion's axial distance is the difference of the actual preceding
prefix's shifted row lengths. -/
theorem prefixAxialDistance_eq_shifted {n a k : ℕ} {t : Tableau n (rectangle a k)}
    (ht : IsStandard t) (m : Fin n) {r : ℕ} (hr : r < (t m).val.1) :
    (prefixAxialDistance t m r : ℝ) =
      (shiftedRowLength (prefixShape ht m.val (Nat.le_of_lt m.isLt)) a r : ℝ) -
      (shiftedRowLength (prefixShape ht m.val (Nat.le_of_lt m.isLt)) a (t m).val.1 : ℝ) := by
  have hrow := (mem_rectangle.mp (t m).property).1
  have hs (i : ℕ) (hi : i < a) :
      shiftedRowLength (prefixShape ht m.val (Nat.le_of_lt m.isLt)) a i + i + 1 =
        prefixRowCount t m i + a := by
    rw [shiftedRowLength, ← prefixRowCount_eq_rowLen_prefixShape ht]
    omega
  have hsr : (shiftedRowLength (prefixShape ht m.val (Nat.le_of_lt m.isLt)) a r : ℝ) + r + 1 =
      prefixRowCount t m r + a := by exact_mod_cast hs r (hr.trans hrow)
  have hss : (shiftedRowLength (prefixShape ht m.val (Nat.le_of_lt m.isLt)) a (t m).val.1 : ℝ) +
      (t m).val.1 + 1 = (t m).val.2 + a := by
    exact_mod_cast (by simpa only [prefixRowCount_self ht] using hs (t m).val.1 hrow)
  unfold prefixAxialDistance
  push_cast
  linarith

/-- When the preceding prefix has no bounded gap, each logarithmic insertion is small. -/
theorem log_prefixInsertionFactor_le_of_not_gap {n a k : ℕ} {t : Tableau n (rectangle a k)}
    (ht : IsStandard t) (m : Fin n) {L : ℝ} (hL : 2 ≤ L)
    (hgap : ¬ HasSmallGap (fun i : Fin a =>
      (shiftedRowLength (prefixShape ht m.val (Nat.le_of_lt m.isLt)) a i.val : ℝ)) L) :
    Real.log (prefixInsertionFactor t m) ≤ (a - 1 : ℕ) / (L - 1) := by
  rw [log_prefixInsertionFactor ht]
  have hrow := (mem_rectangle.mp (t m).property).1
  calc
    _ ≤ ∑ _r ∈ range (t m).val.1, 1 / (L - 1) := by
      apply sum_le_sum
      intro r hr
      have hr' := mem_range.mp hr
      have hd : (2 : ℝ) ≤ prefixAxialDistance t m r := by
        exact_mod_cast two_le_prefixAxialDistance ht m r hr'
      have hsmall : L < (prefixAxialDistance t m r : ℝ) := by
        apply lt_of_not_ge
        intro hle
        apply hgap
        refine ⟨⟨r, hr'.trans hrow⟩, ⟨(t m).val.1, hrow⟩, hr', ?_⟩
        rw [abs_sub_comm, ← prefixAxialDistance_eq_shifted ht m hr', abs_of_nonneg (by linarith)]
        exact hle
      exact (log_ratio_bounds hd).2.2.trans
        (one_div_le_one_div_of_le (by linarith) (by linarith))
    _ = ((t m).val.1 : ℝ) / (L - 1) := by simp [div_eq_mul_inv]
    _ ≤ _ := div_le_div_of_nonneg_right (by
      exact_mod_cast Nat.le_sub_one_of_lt hrow) (by linarith)

/-- The logarithm of the actual prefix product is the sum of its insertion logarithms. -/
theorem log_prefixNormProduct {n : ℕ} {μ : YoungDiagram} {t : Tableau n μ}
    (ht : IsStandard t) :
    Real.log (prefixNormProduct t) = ∑ m, Real.log (prefixInsertionFactor t m) :=
  Real.log_prod (fun m _ => (prefixInsertionFactor_pos ht m).ne')

end BostConjecture.Specht
