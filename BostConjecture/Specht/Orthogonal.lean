module

public import BostConjecture.Specht.Basis
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

/-!
# Monic orthogonalization of standard polytabloids

Gram-Schmidt is applied to the actual standard basis in the orthonormal word
metric. The order is a parameter: the adjacent-transposition formula requires
a compatible dominance order and is not asserted here.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Specht

open OAI.Saxl Module InnerProductSpace

variable {n : ℕ} {μ : YoungDiagram}
variable [LinearOrder {t : Tableau n μ // IsStandard t}]
variable [LocallyFiniteOrderBot {t : Tableau n μ // IsStandard t}]

/-- Monic Gram-Schmidt orthogonalization in the real span of the orbit lattice. -/
def orthogonalStandardBasis (t : Tableau n μ) :
    Basis {u : Tableau n μ // IsStandard u} ℝ (realSpan t) :=
  gramSchmidtBasis (standardRealBasis t)

@[simp] theorem orthogonalStandardBasis_apply (t : Tableau n μ)
    (u : {u : Tableau n μ // IsStandard u}) :
    orthogonalStandardBasis t u = gramSchmidt ℝ (standardRealBasis t) u := by
  exact congrFun (coe_gramSchmidtBasis (standardRealBasis t)) u

/-- Distinct orthogonalized standard polytabloids are perpendicular. -/
theorem orthogonalStandardBasis_orthogonal (t : Tableau n μ)
    {u v : {u : Tableau n μ // IsStandard u}} (h : u ≠ v) :
    inner ℝ (orthogonalStandardBasis t u) (orthogonalStandardBasis t v) = 0 := by
  simpa only [orthogonalStandardBasis_apply] using
    gramSchmidt_orthogonal ℝ (standardRealBasis t) h

/-- No vector is discarded by orthogonalizing the standard basis. -/
theorem orthogonalStandardBasis_ne_zero (t : Tableau n μ)
    (u : {u : Tableau n μ // IsStandard u}) : orthogonalStandardBasis t u ≠ 0 :=
  (orthogonalStandardBasis t).ne_zero u

/-- Orthogonalization only uses earlier standard polytabloids. -/
theorem orthogonalStandardBasis_triangular (t : Tableau n μ)
    {u v : {u : Tableau n μ // IsStandard u}} (h : u < v) :
    (standardRealBasis t).repr (orthogonalStandardBasis t u) v = 0 := by
  rw [orthogonalStandardBasis_apply]
  exact gramSchmidt_triangular h (standardRealBasis t)

/-- The coefficient of the original standard polytabloid stays one. -/
theorem orthogonalStandardBasis_monic (t : Tableau n μ)
    (u : {u : Tableau n μ // IsStandard u}) :
    (standardRealBasis t).repr (orthogonalStandardBasis t u) u = 1 := by
  have h := congrArg (fun x => (standardRealBasis t).repr x u)
    (gramSchmidt_def'' ℝ (standardRealBasis t) u)
  simp only [map_add, map_sum, map_smul, Finsupp.add_apply,
    Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul] at h
  have hz : ∀ v ∈ Finset.Iio u,
      (standardRealBasis t).repr (gramSchmidt ℝ (standardRealBasis t) v) u = 0 :=
    fun v hv => gramSchmidt_triangular (Finset.mem_Iio.mp hv) (standardRealBasis t)
  rw [Finset.sum_eq_zero (fun v hv => by rw [hz v hv, mul_zero]), add_zero] at h
  simpa only [Basis.repr_self, Finsupp.single_eq_same, orthogonalStandardBasis_apply] using h.symm

/-- The monic recurrence, without normalizing the output vectors to unit length. -/
theorem orthogonalStandardBasis_eq_sub_sum (t : Tableau n μ)
    (u : {u : Tableau n μ // IsStandard u}) :
    orthogonalStandardBasis t u = standardRealBasis t u -
      ∑ v ∈ Finset.Iio u,
        (inner ℝ (orthogonalStandardBasis t v) (standardRealBasis t u) /
          ‖orthogonalStandardBasis t v‖ ^ 2) • orthogonalStandardBasis t v := by
  apply eq_sub_iff_add_eq.mpr
  simpa only [orthogonalStandardBasis_apply, RCLike.ofReal_real_eq_id, id_eq] using
    (gramSchmidt_def'' ℝ (standardRealBasis t) u).symm

/-- The first vector in the chosen order is unchanged. -/
theorem orthogonalStandardBasis_eq_of_isLeast (t : Tableau n μ)
    (u : {u : Tableau n μ // IsStandard u}) (hu : ∀ v, ¬v < u) :
    orthogonalStandardBasis t u = standardRealBasis t u := by
  rw [orthogonalStandardBasis_eq_sub_sum]
  have he : Finset.Iio u = ∅ := Finset.eq_empty_iff_forall_notMem.mpr
    (fun v hv => hu v (Finset.mem_Iio.mp hv))
  rw [he, Finset.sum_empty, sub_zero]

/-- The basis change is monic triangular and hence has determinant one. -/
theorem det_orthogonalStandardBasis (t : Tableau n μ) :
    (standardRealBasis t).det (orthogonalStandardBasis t) = 1 := by
  classical
  have ht : ((standardRealBasis t).toMatrix (orthogonalStandardBasis t)).IsUpperTriangular :=
    fun _ _ h => orthogonalStandardBasis_triangular t h
  rw [Basis.det_apply, Matrix.det_of_isUpperTriangular ht]
  simp only [Basis.toMatrix_apply, orthogonalStandardBasis_monic, Finset.prod_const_one]

/-- The original vector and its monic orthogonalization have the same projection
onto the latter. -/
theorem inner_orthogonalStandardBasis_standard (t : Tableau n μ)
    (u : {u : Tableau n μ // IsStandard u}) :
    inner ℝ (orthogonalStandardBasis t u) (standardRealBasis t u) =
      ‖orthogonalStandardBasis t u‖ ^ 2 := by
  rw [orthogonalStandardBasis_apply, gramSchmidt_def'' ℝ (standardRealBasis t) u]
  simp only [inner_add_right, inner_sum, inner_smul_right]
  have hz : ∀ v ∈ Finset.Iio u,
      inner ℝ (gramSchmidt ℝ (standardRealBasis t) u)
        (gramSchmidt ℝ (standardRealBasis t) v) = 0 :=
    fun v hv => gramSchmidt_orthogonal ℝ (standardRealBasis t)
      (Finset.mem_Iio.mp hv).ne'
  rw [Finset.sum_eq_zero (fun v hv => by rw [hz v hv, mul_zero]), add_zero,
    real_inner_self_eq_norm_sq]

/-- Monic orthogonalization preserves the standard Gram determinant exactly. -/
theorem det_standard_gram_eq_prod_orthogonal_norm_sq (t : Tableau n μ) :
    (Matrix.gram ℝ (standardRealBasis t)).det =
      ∏ u, ‖orthogonalStandardBasis t u‖ ^ 2 := by
  classical
  let h := finrank_eq_card_basis (standardRealBasis t)
  let o := gramSchmidtOrthonormalBasis h (standardRealBasis t)
  have hi (u : {u : Tableau n μ // IsStandard u}) :
      inner ℝ (o u) (standardRealBasis t u) = ‖orthogonalStandardBasis t u‖ := by
    have hn : gramSchmidtNormed ℝ (standardRealBasis t) u ≠ 0 :=
      (gramSchmidtNormed_linearIndependent (standardRealBasis t).linearIndependent).ne_zero u
    rw [show o u = gramSchmidtNormed ℝ (standardRealBasis t) u from
      gramSchmidtOrthonormalBasis_apply h hn]
    rw [gramSchmidtNormed, ← orthogonalStandardBasis_apply,
      real_inner_smul_left, inner_orthogonalStandardBasis_standard]
    simp only [RCLike.ofReal_real_eq_id, id_eq]
    rw [pow_two, ← mul_assoc, inv_mul_cancel₀
      (norm_ne_zero_iff.mpr (orthogonalStandardBasis_ne_zero t u)), one_mul]
  rw [o.det_gram_eq_norm_det_sq, gramSchmidtOrthonormalBasis_det, Finset.prod_congr rfl
    (fun u _ => hi u), norm_prod, ← Finset.prod_pow]
  simp only [norm_norm]

/-- The canonical orbit covolume is bounded by the actual orthogonal norm product. -/
theorem covolume_sq_le_prod_orthogonal_norm_sq (t : Tableau n μ) :
    ZLattice.covolume (spanLattice t) ^ 2 ≤
      ∏ u, ‖orthogonalStandardBasis t u‖ ^ 2 := by
  rw [← det_standard_gram_eq_prod_orthogonal_norm_sq]
  exact covolume_sq_le_det_standard_gram t

/-- Taking logarithms gives the sum of actual monic orthogonal squared norms. -/
theorem two_mul_log_covolume_le_sum_log_orthogonal_norm_sq (t : Tableau n μ) :
    2 * Real.log (ZLattice.covolume (spanLattice t)) ≤
      ∑ u, Real.log (‖orthogonalStandardBasis t u‖ ^ 2) := by
  have h := two_mul_log_covolume_le_log_det_standard_gram t
  rw [det_standard_gram_eq_prod_orthogonal_norm_sq,
    Real.log_prod (fun u _ => pow_ne_zero 2
      (norm_ne_zero_iff.mpr (orthogonalStandardBasis_ne_zero t u)))] at h
  exact h

end BostConjecture.Specht
