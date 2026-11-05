module

public import BostConjecture.Arithmetic.DegreeNormalization
public import BostConjecture.Arithmetic.LineContraction
public import BostConjecture.Arithmetic.SubmoduleMetric
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

/-!
# Contraction on determinant lines

The determinant norm is the absolute top-wedge coordinate in an orthonormal
frame. Gram--Schmidt and Cauchy--Schwarz bound the determinant of a contraction.
Scalar extension then transfers this inequality to intrinsic arithmetic degree.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct exteriorPower
open scoped InnerProductSpace

namespace BostConjecture.Arithmetic

namespace ComplexDeterminant

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] {r : ℕ}

/-- The determinant norm is the absolute value of its orthonormal coordinate. -/
lemma norm_eq_coordinate (b : OrthonormalBasis (Fin r) ℂ E) (x : ⋀[ℂ]^r E) :
    Real.sqrt (((core b).inner x x).re) = ‖Geometry.determinantCoordinates b.toBasis x‖ := by
  rw [core_inner]
  exact Complex.sq_sqrt_normSq _

/-- Hadamard's bound in an orthonormal frame, with unit-length column bounds. -/
lemma norm_det_le_one (b : OrthonormalBasis (Fin r) ℂ F) (v : Fin r → F)
    (hv : ∀ i, ‖v i‖ ≤ 1) : ‖b.toBasis.det v‖ ≤ 1 := by
  let c := InnerProductSpace.gramSchmidtOrthonormalBasis
    (by simpa using (Module.finrank_eq_card_basis b.toBasis).symm) v
  have he := core_eq b c
  have hn : ‖b.toBasis.det v‖ = ‖c.toBasis.det v‖ := by
    rw [← Geometry.determinantCoordinates_ιMulti, ← Geometry.determinantCoordinates_ιMulti,
      ← norm_eq_coordinate, ← norm_eq_coordinate, he]
  rw [hn, InnerProductSpace.gramSchmidtOrthonormalBasis_det, norm_prod]
  calc
    ∏ i, ‖inner ℂ (c i) (v i)‖ ≤ ∏ _i : Fin r, (1 : ℝ) := by
      apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      intro i _
      simpa only [c.norm_eq_one, one_mul] using (norm_inner_le_norm (c i) (v i)).trans
        (mul_le_mul_of_nonneg_left (hv i) (norm_nonneg (c i)))
    _ = 1 := by simp

/-- A linear contraction contracts the actual top exterior Hermitian norm. -/
lemma norm_map_le (b : OrthonormalBasis (Fin r) ℂ E) (c : OrthonormalBasis (Fin r) ℂ F)
    (f : E →ₗ[ℂ] F) (hf : ∀ x, ‖f x‖ ≤ ‖x‖) (x : ⋀[ℂ]^r E) :
    Real.sqrt (((core c).inner (map r f x) (map r f x)).re) ≤
      Real.sqrt (((core b).inner x x).re) := by
  obtain ⟨a, rfl⟩ := (Geometry.determinantCoordinates b.toBasis).symm.surjective x
  rw [Geometry.determinantCoordinates_symm_apply, map_smul, map_apply_ιMulti]
  rw [norm_eq_coordinate, norm_eq_coordinate]
  simp only [map_smul, Geometry.determinantCoordinates_ιMulti, Module.Basis.det_self,
    smul_eq_mul, mul_one, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg a)
    (norm_det_le_one c (f ∘ b) (fun i => (hf (b i)).trans_eq (b.norm_eq_one i)))

end ComplexDeterminant

end BostConjecture.Arithmetic
