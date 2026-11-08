/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Specht.Seminormal.PrefixNormInitial

/-!
# Seminormal norm and Gram products for the canonical rectangular lattice

The actual monic norm and the concrete prefix product have the same initial
value and legal adjacent ratios. The checked increasing paths identify them.
The integral orbit lattice then inherits the standard Gram upper bound.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Specht

open OAI.Saxl
open scoped StandardColex

variable {n : ℕ} {μ : YoungDiagram}

/-- The row count used in the explicit norm product is the row length of the actual prefix shape. -/
theorem prefixRowCount_eq_rowLen_prefixShape {t : Tableau n μ} (ht : IsStandard t)
    (m : Fin n) (r : ℕ) :
    prefixRowCount t m r = (prefixShape ht m.val (Nat.le_of_lt m.isLt)).rowLen r := by
  classical
  rw [prefixRowCount, YoungDiagram.rowLen_eq_card]
  apply Finset.card_bij (fun l _ => (t l).val)
  · intro l hl
    obtain ⟨_, hlm, hlr⟩ := Finset.mem_filter.mp hl
    exact YoungDiagram.mem_row_iff.mpr ⟨
      (mem_prefixShape ht m.val (Nat.le_of_lt m.isLt) (t l)).mpr
        (by simpa only [Equiv.symm_apply_apply, Fin.lt_def] using hlm), hlr⟩
  · intro l hl q hq he
    exact t.injective (Subtype.ext he)
  · intro b hb
    obtain ⟨hb, hbr⟩ := YoungDiagram.mem_row_iff.mp hb
    let c : μ := ⟨b, prefixShape_le ht m.val (Nat.le_of_lt m.isLt) hb⟩
    refine ⟨t.symm c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩, ?_⟩
    · exact (mem_prefixShape ht m.val (Nat.le_of_lt m.isLt) c).mp hb
    · simpa [c] using hbr
    · simp [c]

/-- An increasing legal adjacent swap has its earlier label in the lower row. -/
theorem row_lt_of_standard_adjacent_lt
    (T U : {u : Tableau n μ // IsStandard u}) (i j : Fin n)
    (hij : i.val + 1 = j.val) (hU : U.val = relabel (Equiv.swap i j) T.val) (hTU : T < U) :
    (T.val j).val.1 < (T.val i).val.1 := by
  rcases lt_trichotomy (T.val i).val.1 (T.val j).val.1 with hr | hr | hr
  · have hUT : U < T := (standardColex_lt_iff U T).mpr (by
      simpa only [hU] using tableauColexLT_relabel_adjacent T.val i j hij hr)
    exact (lt_asymm hTU hUT).elim
  · have hw : rowWord U.val = rowWord T.val := by
      rw [hU, rowWord_relabel]
      funext l
      simpa only [Function.comp_apply, Equiv.swap_inv] using Equiv.apply_swap_eq_self (Fin.ext hr) l
    exact (hTU.ne (Subtype.ext (U.property.1.eq_of_rowWord_eq T.property.1 hw)).symm).elim
  · exact hr

/-- The explicit prefix product is the squared norm of the actual monic orthogonal vector. -/
theorem norm_orthogonalStandardBasis_sq_eq_prefixNormProduct (a k : ℕ)
    (t : Tableau (a * k) (rectangle a k))
    (T : {u : Tableau (a * k) (rectangle a k) // IsStandard u}) :
    ‖orthogonalStandardBasis t T‖ ^ 2 = prefixNormProduct T.val := by
  have hp := rectangle_standard_adjacent_path a k T
  induction hp with
  | refl =>
    rw [norm_orthogonalStandardBasis_rectangleColumnTableau_sq,
      prefixNormProduct_rectangleColumnTableau]
  | @tail U V hpath hedge ih =>
    obtain ⟨hUV, i, j, hij, hV⟩ := hedge
    rw [norm_orthogonalStandardBasis_swap_sq t U V i j hij hV hUV, ih,
      hV, prefixNormProduct_relabel_adjacent U.property i j hij
        (row_lt_of_standard_adjacent_lt U V i j hij hV hUV)]

/-- The standard Gram determinant equals the product of the explicit prefix norm factors. -/
theorem det_standard_gram_eq_prod_prefixNormProduct (a k : ℕ)
    (t : Tableau (a * k) (rectangle a k)) :
    (Matrix.gram ℝ (standardRealBasis t)).det =
      ∏ T : {u : Tableau (a * k) (rectangle a k) // IsStandard u}, prefixNormProduct T.val := by
  simpa only [det_standard_gram_eq_prod_orthogonal_norm_sq] using Finset.prod_congr rfl fun T _ =>
    norm_orthogonalStandardBasis_sq_eq_prefixNormProduct a k t T

/-- The explicit seminormal sum bounds the logarithmic covolume of the unchanged orbit lattice. -/
theorem two_mul_log_covolume_le_sum_log_prefixNormProduct (a k : ℕ)
    (t : Tableau (a * k) (rectangle a k)) :
    2 * Real.log (ZLattice.covolume (spanLattice t)) ≤
      ∑ T : {u : Tableau (a * k) (rectangle a k) // IsStandard u},
        Real.log (prefixNormProduct T.val) := by
  simpa only [norm_orthogonalStandardBasis_sq_eq_prefixNormProduct] using
    two_mul_log_covolume_le_sum_log_orthogonal_norm_sq t

/-- Dividing by the actual integral rank gives the uniform standard-tableau average. -/
theorem two_mul_rectangleLogCovolume_le_average_log_prefixNormProduct (a k : ℕ) :
    2 * rectangleLogCovolume a k ≤
      (∑ T : {u : Tableau (a * k) (rectangle a k) // IsStandard u},
        Real.log (prefixNormProduct T.val)) /
          Fintype.card {u : Tableau (a * k) (rectangle a k) // IsStandard u} := by
  have hr : rectangleRank a k =
      Fintype.card {u : Tableau (a * k) (rectangle a k) // IsStandard u} :=
    finrank_orbitLattice_eq_card_standard (rectangleTableau a k)
  simpa only [rectangleLogCovolume, ← mul_div_assoc, ← hr] using div_le_div_of_nonneg_right
    (two_mul_log_covolume_le_sum_log_prefixNormProduct a k (rectangleTableau a k))
    (Nat.cast_nonneg _)

end BostConjecture.Specht
