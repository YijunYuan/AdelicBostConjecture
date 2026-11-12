/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Determinant.HermitianBasis
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
import ArakelovGeometry.Analysis.Determinant.ExactSequence

/-!
# Actual determinant norms and Gram determinants

The projective quotient norm on the top exterior power is computed from the
Gram determinant of the original completed Hermitian fibre. This is the local
bridge needed to compute the degree of a constant Specht bundle.
-/

@[expose] public section
noncomputable section

namespace ArakelovGeometry.NormFamily

open scoped TensorProduct

variable {K : Type*} [Field K] {S : AdelicStructure K}
  {E : Type*} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {ξ : NormFamily S E}
  [hS : S.IsArchimedeanNormalized]

/-- Relative to an orthonormal frame, the actual exterior determinant norm
is the absolute value of the coordinate determinant. -/
theorem IsHermitian.determinant_norm_eq_norm_det (hξ : ξ.IsHermitian)
    (ω : S.Ω) (hω : ω ∈ S.Ωinf) :
    letI := hS ω hω
    letI := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
    letI := ξ.fibreNormedAddCommGroup ω
    letI := ξ.fibreNormedSpace ω
    letI := ξ.fiberInnerProductSpace ω hω
    ∀ (b : OrthonormalBasis (Fin (Module.finrank K E)) (S.ϕ ω).Completion
        ((S.ϕ ω).Completion ⊗[K] E))
      (v : Fin (Module.finrank K E) → (S.ϕ ω).Completion ⊗[K] E),
      ξ.determinant.norm ω
        ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion E _).symm
          (_root_.exteriorPower.ιMulti (S.ϕ ω).Completion _ v)) = ‖b.toBasis.det v‖ := by
  let := hS ω hω
  let := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
  let := ξ.fibreNormedAddCommGroup ω
  let := ξ.fibreNormedSpace ω
  let := ξ.fiberInnerProductSpace ω hω
  intro b v
  have hv : _root_.exteriorPower.ιMulti (S.ϕ ω).Completion (Module.finrank K E) v =
      b.toBasis.det v • _root_.exteriorPower.ιMulti (S.ϕ ω).Completion _ b.toBasis := by
    apply (determinantCoordinateEquiv b.toBasis).injective
    simp only [map_smul, determinantCoordinateEquiv_ιMulti, Module.Basis.det_self,
      smul_eq_mul, mul_one]
  rw [hv, map_smul, ξ.determinant.norm_smul, OrthonormalBasis.coe_toBasis,
    hξ.determinant_norm_orthonormalBasis ξ ω hω b, mul_one]

/-- The Gram determinant computes the square of the actual exterior norm,
for every completed tuple, including dependent tuples and rank zero. -/
theorem IsHermitian.determinant_norm_sq_eq_norm_gram (hξ : ξ.IsHermitian)
    (ω : S.Ω) (hω : ω ∈ S.Ωinf) :
    letI := hS ω hω
    letI := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
    letI := ξ.fibreNormedAddCommGroup ω
    letI := ξ.fibreNormedSpace ω
    letI := ξ.fiberInnerProductSpace ω hω
    ∀ v : Fin (Module.finrank K E) → (S.ϕ ω).Completion ⊗[K] E,
      (ξ.determinant.norm ω
        ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion E _).symm
          (_root_.exteriorPower.ιMulti (S.ϕ ω).Completion _ v))) ^ 2 =
        ‖(Matrix.gram (S.ϕ ω).Completion v).det‖ := by
  classical
  let := hS ω hω
  let := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
  let := ξ.fibreNormedAddCommGroup ω
  let := ξ.fibreNormedSpace ω
  let := ξ.fiberInnerProductSpace ω hω
  intro v
  let b := (stdOrthonormalBasis (S.ϕ ω).Completion
    ((S.ϕ ω).Completion ⊗[K] E)).reindex (finCongr Module.finrank_baseChange)
  rw [hξ.determinant_norm_eq_norm_det ω hω b v, Matrix.gram_eq_conjTranspose_mul b v,
    Matrix.det_mul, Matrix.det_conjTranspose, norm_mul, norm_star, pow_two]
  rfl

end ArakelovGeometry.NormFamily
