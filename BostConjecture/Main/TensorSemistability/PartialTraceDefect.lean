module

public import BostConjecture.Balanced.ProjectionTrace

/-!
# Self-adjoint partial traces and their scalar defects

These finite-dimensional identities are used by the arithmetic extremal
metric argument, with the actual projection onto a tensor submodule fiber.
Reference: bost_specht_manuscript.pdf, Proposition 7.3, page 13.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Balanced

open scoped InnerProductSpace TensorProduct

variable {U W : Type*} [NormedAddCommGroup U] [InnerProductSpace ℂ U]
    [FiniteDimensional ℂ U] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W]

/-- The right partial trace is contraction in any orthonormal basis. -/
theorem inner_partialTraceRight {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ W) (P : Module.End ℂ (U ⊗[ℂ] W)) (x y : U) :
    inner ℂ x (partialTraceRight ℂ U W P y) =
      ∑ i, inner ℂ (x ⊗ₜ[ℂ] b i) (P (y ⊗ₜ[ℂ] b i)) := by
  obtain ⟨p, rfl⟩ := (homTensorHomEquiv ℂ U W U W).surjective P
  induction p using TensorProduct.inductionOn with
  | tmul A B =>
    change inner ℂ x (partialTraceRight ℂ U W (TensorProduct.map A B) y) =
      ∑ i, inner ℂ (x ⊗ₜ[ℂ] b i) (TensorProduct.map A B (y ⊗ₜ[ℂ] b i))
    rw [partialTraceRight_map, LinearMap.smul_apply, inner_smul_right,
      LinearMap.trace_eq_sum_inner B b]
    simp only [TensorProduct.map_tmul, TensorProduct.inner_tmul]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  | add p q hp hq =>
    simp only [map_add, LinearMap.add_apply, inner_add_right, Finset.sum_add_distrib, hp, hq]

/-- The left partial trace is contraction in any orthonormal basis. -/
theorem inner_partialTraceLeft {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ U) (P : Module.End ℂ (U ⊗[ℂ] W)) (x y : W) :
    inner ℂ x (partialTraceLeft ℂ U W P y) =
      ∑ i, inner ℂ (b i ⊗ₜ[ℂ] x) (P (b i ⊗ₜ[ℂ] y)) := by
  obtain ⟨p, rfl⟩ := (homTensorHomEquiv ℂ U W U W).surjective P
  induction p using TensorProduct.inductionOn with
  | tmul A B =>
    change inner ℂ x (partialTraceLeft ℂ U W (TensorProduct.map A B) y) =
      ∑ i, inner ℂ (b i ⊗ₜ[ℂ] x) (TensorProduct.map A B (b i ⊗ₜ[ℂ] y))
    rw [partialTraceLeft_map, LinearMap.smul_apply, inner_smul_right,
      LinearMap.trace_eq_sum_inner A b]
    simp only [TensorProduct.map_tmul, TensorProduct.inner_tmul]
    rw [Finset.sum_mul]
  | add p q hp hq =>
    simp only [map_add, LinearMap.add_apply, inner_add_right, Finset.sum_add_distrib, hp, hq]

/-- A partial trace preserves self-adjointness. -/
theorem isSymmetric_partialTraceRight (P : Module.End ℂ (U ⊗[ℂ] W))
    (hP : P.IsSymmetric) : (partialTraceRight ℂ U W P).IsSymmetric := by
  intro x y
  let b := stdOrthonormalBasis ℂ W
  rw [← inner_conj_symm, inner_partialTraceRight b, map_sum, inner_partialTraceRight b]
  apply Finset.sum_congr rfl
  intro i _
  exact (inner_conj_symm (𝕜 := ℂ) (P (x ⊗ₜ[ℂ] b i)) (y ⊗ₜ[ℂ] b i)).trans
    (hP _ _)

/-- A partial trace preserves self-adjointness. -/
theorem isSymmetric_partialTraceLeft (P : Module.End ℂ (U ⊗[ℂ] W))
    (hP : P.IsSymmetric) : (partialTraceLeft ℂ U W P).IsSymmetric := by
  intro x y
  let b := stdOrthonormalBasis ℂ U
  rw [← inner_conj_symm, inner_partialTraceLeft b, map_sum, inner_partialTraceLeft b]
  apply Finset.sum_congr rfl
  intro i _
  exact (inner_conj_symm (𝕜 := ℂ) (P (b i ⊗ₜ[ℂ] x)) (b i ⊗ₜ[ℂ] y)).trans
    (hP _ _)

/-- Taking a partial trace does not change the full trace. -/
theorem trace_partialTraceRight (P : Module.End ℂ (U ⊗[ℂ] W)) :
    LinearMap.trace ℂ U (partialTraceRight ℂ U W P) =
      LinearMap.trace ℂ (U ⊗[ℂ] W) P := by
  simpa using trace_partialTraceRight_comp P LinearMap.id

/-- Taking a partial trace does not change the full trace. -/
theorem trace_partialTraceLeft (P : Module.End ℂ (U ⊗[ℂ] W)) :
    LinearMap.trace ℂ W (partialTraceLeft ℂ U W P) =
      LinearMap.trace ℂ (U ⊗[ℂ] W) P := by
  simpa using trace_partialTraceLeft_comp P LinearMap.id

/-- The trace of the actual orthogonal projection is the subspace dimension. -/
theorem trace_starProjection (S : Submodule ℂ U) :
    LinearMap.trace ℂ U S.starProjection.toLinearMap = (Module.finrank ℂ S : ℂ) := by
  let b := stdOrthonormalBasis ℂ S
  have he := trace_starProjection_comp_eq_sum S b LinearMap.id
  have hi (i) : inner ℂ (b i : U) (b i : U) = 1 := by
    change inner ℂ (b i) (b i) = 1
    simp only [b.inner_eq_ite, ite_true]
  simpa only [LinearMap.comp_id, LinearMap.id_apply, hi, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] using he

omit [FiniteDimensional ℂ U] in
/-- Subtracting a real scalar operator preserves self-adjointness. -/
theorem isSymmetric_sub_real_smul_id (T : Module.End ℂ U) (hT : T.IsSymmetric) (a : ℝ) :
    (T - (a : ℂ) • LinearMap.id).IsSymmetric := by
  intro x y
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, hT x y,
    Complex.conj_ofReal]

/-- The scalar defect is traceless when the scalar is its normalized trace. -/
theorem trace_sub_scalar_id (T : Module.End ℂ U) (a : ℂ)
    (hT : LinearMap.trace ℂ U T = a * (Module.finrank ℂ U : ℂ)) :
    LinearMap.trace ℂ U (T - a • LinearMap.id) = 0 := by
  simp [hT]

omit [FiniteDimensional ℂ U] in
/-- A traceless scalar defect has the same pairing with its operator as with itself. -/
theorem trace_comp_sub_scalar_id (T : Module.End ℂ U) (a : ℂ)
    (hT : LinearMap.trace ℂ U (T - a • LinearMap.id) = 0) :
    LinearMap.trace ℂ U (T.comp (T - a • LinearMap.id)) =
      LinearMap.trace ℂ U ((T - a • LinearMap.id).comp (T - a • LinearMap.id)) := by
  let A := T - a • LinearMap.id
  have he : T = A + a • LinearMap.id := (sub_add_cancel T _).symm
  change LinearMap.trace ℂ U (T.comp A) = LinearMap.trace ℂ U (A.comp A)
  change LinearMap.trace ℂ U A = 0 at hT
  conv_lhs => rw [he]
  simp only [LinearMap.add_comp, map_add, LinearMap.smul_comp, LinearMap.id_comp,
    map_smul, hT, smul_zero, add_zero]

omit [FiniteDimensional ℂ U] in
/-- The squared self-adjoint operator has nonnegative real trace, with the
exact orthonormal-basis norm formula. -/
theorem re_trace_comp_self {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ U) (A : Module.End ℂ U) (hA : A.IsSymmetric) :
    (LinearMap.trace ℂ U (A.comp A)).re = ∑ i, ‖A (b i)‖ ^ 2 := by
  rw [LinearMap.trace_eq_sum_inner _ b, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [LinearMap.comp_apply, ← hA (b i) (A (b i))]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) (A (b i))

theorem re_trace_comp_self_nonneg (A : Module.End ℂ U) (hA : A.IsSymmetric) :
    0 ≤ (LinearMap.trace ℂ U (A.comp A)).re := by
  rw [re_trace_comp_self (stdOrthonormalBasis ℂ U) A hA]
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- Vanishing squared trace forces a self-adjoint operator to vanish. -/
theorem eq_zero_of_re_trace_comp_self_eq_zero (A : Module.End ℂ U) (hA : A.IsSymmetric)
    (hz : (LinearMap.trace ℂ U (A.comp A)).re = 0) : A = 0 := by
  let b := stdOrthonormalBasis ℂ U
  rw [re_trace_comp_self b A hA] at hz
  have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖A (b i)‖)).mp hz
  apply b.toBasis.ext
  intro i
  have he := hi i (Finset.mem_univ i)
  simpa only [OrthonormalBasis.coe_toBasis, LinearMap.zero_apply] using
    norm_eq_zero.mp (sq_eq_zero_iff.mp he)

end BostConjecture.Balanced
