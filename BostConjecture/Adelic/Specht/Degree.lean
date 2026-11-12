/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Adelic.Specht.Bundle
public import BostConjecture.Adelic.Specht.Determinant
public import BostConjecture.Specht.Lattice.Rectangle
public import ArakelovGeometry.AdelicVectorBundle.Slope.Basic
import ArakelovGeometry.Analysis.Determinant.ExactSequence
import ArakelovGeometry.AdelicCurve.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Degree of the constant Specht bundle

The integral basis wedge has norm one at finite places and the actual lattice
covolume at infinite places. Integrating its logarithmic norm computes the
Arakelov degree and slope in this paper, Lemma 6.1.
-/

@[expose] public section
noncomputable section

namespace BostConjecture.Specht

open Module ArakelovGeometry MeasureTheory
open scoped TensorProduct

variable {K : Type*} [Field K] [CharZero K] (S : AdelicStructure K)
  {n : ℕ} {μ : YoungDiagram} (t : OAI.Saxl.Tableau n μ)
  (b : Basis (Fin (Module.finrank K (K ⊗[ℤ] orbitLattice t))) ℤ (orbitLattice t))

/-- The rational determinant section coming from an integral lattice basis. -/
def latticeDetVector : ⋀[K]^(Module.finrank K (K ⊗[ℤ] orbitLattice t))
    (K ⊗[ℤ] orbitLattice t) :=
  _root_.exteriorPower.ιMulti K _ (b.baseChange K)

theorem latticeDetVector_ne_zero : latticeDetVector (K := K) t b ≠ 0 := by
  intro h
  have he := congrArg (determinantCoordinateEquiv (b.baseChange K)) h
  exact one_ne_zero (by simpa only [latticeDetVector,
    determinantCoordinateEquiv_ιMulti, Basis.det_self, map_zero] using he)

omit [CharZero K] in
/-- The rational integral wedge becomes the completed basis wedge. -/
theorem fibre_latticeDetVector (ω : S.Ω) :
    (exteriorBaseChangeEquiv K (S.ϕ ω).Completion (K ⊗[ℤ] orbitLattice t) _).symm
      (_root_.exteriorPower.ιMulti (S.ϕ ω).Completion _
        ((b.baseChange K).baseChange (S.ϕ ω).Completion)) =
      (1 : (S.ϕ ω).Completion) ⊗ₜ[K] latticeDetVector (K := K) t b := by
  apply (exteriorBaseChangeEquiv K (S.ϕ ω).Completion (K ⊗[ℤ] orbitLattice t) _).injective
  simp only [LinearEquiv.apply_symm_apply, latticeDetVector,
    exteriorBaseChangeEquiv_tmul_ιMulti, one_smul]
  congr 1
  ext i
  simp only [Basis.baseChange_apply]

variable [hN : S.IsArchimedeanNormalized]

include hN
/-- The integral determinant section has unit norm at every finite place. -/
theorem latticeDetVector_norm_finite (ω : S.Ω) (hω : ω ∈ S.Ωfin) :
    (latticeNormFamily S t b).determinant.norm ω
      ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] latticeDetVector (K := K) t b) = 1 := by
  rw [← fibre_latticeDetVector S t b ω]
  apply (latticeNormFamily_isHermitian S t b).determinant_norm_completedBasis_eq_one
    (latticeNormFamily S t b) ω ((b.baseChange K).baseChange (S.ϕ ω).Completion)
  · intro i
    rw [latticeNormFamily_norm_finite S t b ω hω]
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro j
    rw [Basis.equivFun_self]
    split_ifs <;> simp
  · intro i
    apply (latticeNormFamily S t b).dual_norm_le ω _ zero_le_one
    intro x
    rw [LinearEquiv.apply_symm_apply, one_mul, latticeNormFamily_norm_finite S t b ω hω]
    simpa only [Basis.coord_apply, Basis.equivFun_apply] using
      (norm_le_pi_norm (((b.baseChange K).baseChange (S.ϕ ω).Completion).equivFun x) i)

/-- At infinity the square of the determinant norm is the square of the
covolume in the original orthonormal word metric. -/
theorem latticeDetVector_norm_sq_infinite (ω : S.Ω) (hω : ω ∈ S.Ωinf) :
    (latticeNormFamily S t b).determinant.norm ω
      ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] latticeDetVector (K := K) t b) ^ 2 =
      ZLattice.covolume (spanLattice t) ^ 2 := by
  classical
  let := hN ω hω
  let := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
  let := (latticeNormFamily S t b).fibreNormedAddCommGroup ω
  let := (latticeNormFamily S t b).fibreNormedSpace ω
  let := (latticeNormFamily S t b).fiberInnerProductSpace ω hω
  let G := Matrix.of fun i j => ∑ w, (b i).val w * (b j).val w
  have hg : Matrix.gram (S.ϕ ω).Completion
      ((b.baseChange K).baseChange (S.ϕ ω).Completion) =
      G.map (Int.castRingHom (S.ϕ ω).Completion) := by
    ext i j
    simp only [Matrix.gram_apply, Basis.baseChange_apply]
    exact latticeNormFamily_inner_integral S t b ω hω (b i) (b j)
  rw [← fibre_latticeDetVector S t b ω,
    NormFamily.determinant_norm_sq_eq_norm_gram (latticeNormFamily S t b) ω hω, hg]
  change ‖((Int.castRingHom (S.ϕ ω).Completion).mapMatrix G).det‖ = _
  rw [← RingHom.map_det]
  change ‖(G.det : (S.ϕ ω).Completion)‖ = _
  rw [← RCLike.ofReal_intCast, RCLike.norm_ofReal]
  have hd : (G.det : ℝ) = ZLattice.covolume (spanLattice t) ^ 2 :=
    (covolume_sq_eq_integer_gram t b).symm
  rw [hd, abs_of_nonneg (sq_nonneg _)]

/-- The actual determinant norm, with its positive square root fixed. -/
theorem latticeDetVector_norm_infinite (ω : S.Ω) (hω : ω ∈ S.Ωinf) :
    (latticeNormFamily S t b).determinant.norm ω
      ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] latticeDetVector (K := K) t b) =
      ZLattice.covolume (spanLattice t) := by
  have hs := latticeDetVector_norm_sq_infinite S t b ω hω
  have hn := (latticeNormFamily S t b).determinant.norm_nonneg ω
    ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] latticeDetVector (K := K) t b)
  have hc := ZLattice.covolume_pos (spanLattice t) volume
  nlinarith

/-- The logarithmic determinant norm is supported on the infinite places. -/
theorem latticeDetVector_logNorm (ω : S.Ω) :
    (latticeNormFamily S t b).determinant.logNorm (latticeDetVector (K := K) t b) ω =
      S.Ωinf.indicator (fun _ => Real.log (ZLattice.covolume (spanLattice t))) ω := by
  classical
  by_cases hω : ω ∈ S.Ωinf
  · simp [NormFamily.logNorm, latticeDetVector_norm_infinite S t b ω hω,
      Set.indicator_of_mem hω]
  · have hf : ω ∈ S.Ωfin := not_not.mp hω
    simp [NormFamily.logNorm, latticeDetVector_norm_finite S t b ω hf,
      Set.indicator_of_notMem hω]

variable [S.IsProper] [hcount : S.HasCommonCountableDenseSubfield]

/-- Degree of the constant Specht lattice with its actual word Gram metric. -/
theorem latticeBundle_degree :
    (latticeBundle S t b).degree =
      -(S.v S.Ωinf).toReal * Real.log (ZLattice.covolume (spanLattice t)) := by
  rw [AdelicVectorBundle.degree_eq_neg_integral _
    ⟨latticeDetVector (K := K) t b, latticeDetVector_ne_zero t b⟩]
  simp_rw [latticeBundle_toNormFamily, latticeDetVector_logNorm S t b]
  rw [integral_indicator S.measurableSet_Ωinf, setIntegral_const]
  simp [Measure.real, neg_mul]

/-- Slope is the normalized logarithmic covolume, weighted by the mass at infinity. -/
theorem latticeBundle_slope :
    (latticeBundle S t b).slope =
      -(S.v S.Ωinf).toReal *
        (Real.log (ZLattice.covolume (spanLattice t)) /
          Module.finrank K (K ⊗[ℤ] orbitLattice t)) := by
  rw [AdelicVectorBundle.slope, latticeBundle_degree]
  exact mul_div_assoc _ _ _

/-- The actual constant bundle has the rectangular covolume correction of this paper,
independently of the tableau chosen to generate its integral orbit lattice. -/
theorem latticeBundle_slope_rectangle {a k : ℕ}
    (t : OAI.Saxl.Tableau n (rectangle a k))
    (b : Basis (Fin (Module.finrank K (K ⊗[ℤ] orbitLattice t))) ℤ (orbitLattice t)) :
    (latticeBundle S t b).slope =
      -(S.v S.Ωinf).toReal * rectangleLogCovolume a k := by
  have hr : Module.finrank K (K ⊗[ℤ] orbitLattice t) =
      Module.finrank ℤ (orbitLattice t) := by
    rw [Module.finrank_eq_card_basis (b.baseChange K), Module.finrank_eq_card_basis b]
  rw [latticeBundle_slope, hr]
  congr 1
  have hn : n = a * k := by
    simpa using Fintype.card_congr (rectangleCoordinates t)
  subst n
  unfold rectangleLogCovolume rectangleRank rectangleLattice spanLattice realSpan realLattice
  rw [orbitLattice_eq t (rectangleTableau a k)]

end BostConjecture.Specht
