module

public import BostConjecture.Arithmetic.Specht.DeterminantTensorMetric
public import BostConjecture.Arithmetic.Specht.FiniteTensorDegree
public import BostConjecture.Arithmetic.Specht.LatticeDegree

/-! # Exact intrinsic slope of the canonical determinant–Specht bundle -/

@[expose] public section

noncomputable section

open Module NumberField TensorProduct

namespace BostConjecture.Arithmetic.Specht

open BostConjecture.Specht

universe u

variable {K M : Type u} [Field K] [NumberField K] [AddCommGroup M] [Module (𝓞 K) M]
  [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M] {n a k : ℕ}

local instance (t : OAI.Saxl.Tableau n (rectangle a k)) :
    AddCommGroup ((⨂[𝓞 K] (_ : Fin k), ⋀[𝓞 K]^a M) ⊗[𝓞 K]
      (𝓞 K ⊗[ℤ] orbitLattice t)) := Module.addCommMonoidToAddCommGroup (𝓞 K)

/-- The actual determinant twist contributes `k` times the intrinsic degree. -/
theorem determinantMetric_line_twist_slope (h : HermitianMetric (K := K) M) (hk : 0 < k)
    (t : OAI.Saxl.Tableau n (rectangle a k))
    (ha : ∀ p : PrimeSpectrum (𝓞 K), Module.rankAtStalk M p = a) :
    (determinantMetric h hk t ha).slope =
      (k : ℝ) * h.degree + (latticeMetric (K := K) t).slope := by
  have hr : Module.finrank K (K ⊗[𝓞 K] M) = a :=
    Geometry.scalarExtension_finrank_of_rankAtStalk ha
  subst a
  rw [determinantMetric_eq_tensor h hk t ha]
  have hp : 0 < Module.finrank K
      (K ⊗[𝓞 K] (⨂[𝓞 K] (_ : Fin k), DeterminantLine (K := K) M)) := by
    simp [piTensor_generic_finrank, determinant_generic_finrank]
  have hl : 0 < Module.finrank K (K ⊗[𝓞 K] (𝓞 K ⊗[ℤ] orbitLattice t)) := by
    let := lattice_generic_nontrivial (K := K) t
    exact Module.finrank_pos
  exact (HermitianMetric.slope_tensor
    (HermitianMetric.piTensor (fun _ : Fin k => h.determinant))
    (latticeMetric (K := K) t) hp hl).trans
      (congrArg (fun z => z + (latticeMetric (K := K) t).slope)
        (determinant_piTensor_slope h k))

/-- Exact intrinsic slope with the actual orbit-lattice covolume correction. -/
theorem determinantMetric_slope (h : HermitianMetric (K := K) M) (hk : 0 < k)
    (t : OAI.Saxl.Tableau n (rectangle a k))
    (ha : ∀ p : PrimeSpectrum (𝓞 K), Module.rankAtStalk M p = a) :
    (determinantMetric h hk t ha).slope = (k : ℝ) * h.degree -
      Real.log (ZLattice.covolume (spanLattice t)) / Module.finrank ℤ (orbitLattice t) := by
  rw [determinantMetric_line_twist_slope, latticeMetric_slope, neg_div, sub_eq_add_neg]

/-- The manuscript's exact normalization for the canonical rectangular bundle,
over an arbitrary number field and without an integral frame. -/
theorem rectangle_determinantMetric_slope (h : HermitianMetric (K := K) M)
    (ha0 : 0 < a) (hk : 0 < k)
    (ha : ∀ p : PrimeSpectrum (𝓞 K), Module.rankAtStalk M p = a) :
    (determinantMetric h hk (rectangleTableau a k) ha).slope =
      (a * k : ℕ) * h.slope - rectangleLogCovolume a k := by
  rw [determinantMetric_line_twist_slope, rectangle_latticeMetric_slope]
  have hr : Module.finrank K (K ⊗[𝓞 K] M) = a :=
    Geometry.scalarExtension_finrank_of_rankAtStalk ha
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt ha0
  unfold HermitianMetric.slope
  rw [hr, Nat.cast_mul]
  field_simp
  ring

/-- The normalized correction is independent of the rectangular tableau. -/
lemma normalized_covolume_eq_rectangle (t : OAI.Saxl.Tableau n (rectangle a k)) :
    Real.log (ZLattice.covolume (spanLattice t)) / Module.finrank ℤ (orbitLattice t) =
      rectangleLogCovolume a k := by
  have hn : n = a * k := by
    simpa using Fintype.card_congr (rectangleCoordinates t)
  subst n
  unfold rectangleLogCovolume rectangleRank rectangleLattice spanLattice realSpan realLattice
  rw [orbitLattice_eq t (rectangleTableau a k)]

/-- Exact slope in any rectangular tableau, in the degree used by the actual
canonical pairings. -/
theorem determinantMetric_slope_of_pos (h : HermitianMetric (K := K) M)
    (ha0 : 0 < a) (hk : 0 < k) (t : OAI.Saxl.Tableau n (rectangle a k))
    (ha : ∀ p : PrimeSpectrum (𝓞 K), Module.rankAtStalk M p = a) :
    (determinantMetric h hk t ha).slope =
      (n : ℝ) * h.slope - rectangleLogCovolume a k := by
  rw [determinantMetric_slope, normalized_covolume_eq_rectangle]
  have hr : Module.finrank K (K ⊗[𝓞 K] M) = a :=
    Geometry.scalarExtension_finrank_of_rankAtStalk ha
  have hn : n = a * k := by simpa using Fintype.card_congr (rectangleCoordinates t)
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt ha0
  unfold HermitianMetric.slope
  rw [hr, hn, Nat.cast_mul]
  field_simp

end BostConjecture.Arithmetic.Specht
