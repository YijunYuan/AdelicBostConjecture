module

public import BostConjecture.Arithmetic.Specht.Bundle
public import BostConjecture.Arithmetic.RestrictionCovolume.Free
public import BostConjecture.Specht.Metric

/-!
# Intrinsic degree of the arithmetic Specht lattice

The actual integral lattice basis has the same Gram determinant in every
archimedean fiber. The intrinsic free-basis degree formula therefore gives
minus the logarithm of the existing lattice covolume.

Reference: `bost_specht_manuscript.pdf`, Lemma 6.1, pages 8–9.
-/

@[expose] public section

noncomputable section

open Module NumberField TensorProduct exteriorPower MeasureTheory

namespace BostConjecture.Arithmetic.Specht

open BostConjecture.Specht

variable {K : Type*} [Field K] [NumberField K] {n : ℕ} {μ : YoungDiagram}

omit [NumberField K] in
/-- The arithmetic Gram entries of integral lattice vectors are the original
integer word Gram entries at every embedding. -/
lemma latticeMetric_inner_integral (t : OAI.Saxl.Tableau n μ) (σ : K →+* ℂ)
    (x y : orbitLattice t) :
    ((latticeMetric (K := K) t).fiber σ).inner
      (fiberSection _ σ ((1 : 𝓞 K) ⊗ₜ[ℤ] x))
      (fiberSection _ σ ((1 : 𝓞 K) ⊗ₜ[ℤ] y)) =
        (∑ w, (x.val w * y.val w : ℤ) : ℂ) := by
  change (Geometry.latticeComplexCore t).inner
    (latticeFiberEquiv t σ (fiberSection _ σ ((1 : 𝓞 K) ⊗ₜ[ℤ] x)))
    (latticeFiberEquiv t σ (fiberSection _ σ ((1 : 𝓞 K) ⊗ₜ[ℤ] y))) = _
  simpa only [latticeFiberEquiv_section, map_one] using
    Geometry.latticeComplexCore_inner_integral t x y

omit [NumberField K] in
/-- Every integral basis wedge has norm equal to the checked lattice covolume. -/
theorem latticeMetric_determinant_norm (t : OAI.Saxl.Tableau n μ)
    (b : Basis (Fin (Module.finrank K (K ⊗[𝓞 K] (𝓞 K ⊗[ℤ] orbitLattice t))))
      ℤ (orbitLattice t)) (σ : K →+* ℂ) :
    (latticeMetric (K := K) t).determinant.sectionNorm σ
      (ιMulti (𝓞 K) _ (b.baseChange (𝓞 K))) = ZLattice.covolume (spanLattice t) := by
  classical
  let h := latticeMetric (K := K) t
  let G := Matrix.of fun i j => ∑ w, (b i).val w * (b j).val w
  have hG : (Matrix.of fun i j => (h.fiber σ).inner
      (fiberSection _ σ (b.baseChange (𝓞 K) i))
      (fiberSection _ σ (b.baseChange (𝓞 K) j))) = G.map (Int.castRingHom ℂ) := by
    ext i j
    simpa [h, G, Basis.baseChange_apply] using latticeMetric_inner_integral t σ (b i) (b j)
  have hs : (h.determinant.sectionNorm σ (ιMulti (𝓞 K) _ (b.baseChange (𝓞 K)))) ^ 2 =
      ZLattice.covolume (spanLattice t) ^ 2 := by
    rw [← h.norm_det_gram_eq_sectionNorm_sq, hG]
    rw [show (G.map (Int.castRingHom ℂ)).det = (G.det : ℂ) from
      ((Int.castRingHom ℂ).map_det G).symm]
    have hc := covolume_sq_eq_integer_gram t b
    change ‖(G.det : ℂ)‖ = _
    rw [Complex.norm_intCast]
    rw [← hc, abs_of_nonneg (sq_nonneg _)]
  have hx : 0 ≤ h.determinant.sectionNorm σ (ιMulti (𝓞 K) _ (b.baseChange (𝓞 K))) :=
    Real.sqrt_nonneg _
  have hy := ZLattice.covolume_pos (spanLattice t) volume
  nlinarith

/-- Intrinsic normalized degree of the actual scalar-extended Specht lattice. -/
theorem latticeMetric_degree (t : OAI.Saxl.Tableau n μ) :
    (latticeMetric (K := K) t).degree = -Real.log (ZLattice.covolume (spanLattice t)) := by
  let b := (Module.finBasis ℤ (orbitLattice t)).reindex
    (finCongr (lattice_generic_finrank (K := K) t)).symm
  rw [(latticeMetric t).degree_eq_neg_sum_log_of_basis (b.baseChange (𝓞 K))]
  simp only [latticeMetric_determinant_norm, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, NumberField.Embeddings.card]
  have hd : (Module.finrank ℚ K : ℝ) ≠ 0 := by exact_mod_cast
    (ne_of_gt (Module.finrank_pos (R := ℚ) (M := K)))
  field_simp

/-- The lattice correction is the logarithmic covolume divided by its actual rank. -/
theorem latticeMetric_slope (t : OAI.Saxl.Tableau n μ) :
    (latticeMetric (K := K) t).slope =
      -Real.log (ZLattice.covolume (spanLattice t)) / Module.finrank ℤ (orbitLattice t) := by
  rw [HermitianMetric.slope, latticeMetric_degree, lattice_generic_finrank]

/-- For the canonical rectangle, the intrinsic lattice slope is exactly minus
the existing normalized covolume correction used by the Specht asymptotics. -/
theorem rectangle_latticeMetric_slope (a k : ℕ) :
    (latticeMetric (K := K) (rectangleTableau a k)).slope = -rectangleLogCovolume a k := by
  rw [latticeMetric_slope]
  simp only [rectangleLogCovolume, rectangleRank, rectangleLattice, neg_div]

end BostConjecture.Arithmetic.Specht
