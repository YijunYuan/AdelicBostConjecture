/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Degree.Normalization
public import BostConjecture.ExternalCode.TauCeti.Lattice.Covolume
public import BostConjecture.Arithmetic.RestrictionCovolume.TraceSpace
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs

/-!
# Euclidean Haar covolume of the actual trace lattice

The volume is the canonical Euclidean Haar volume of the trace inner
product. Its Gram determinant formula uses any integer basis of the
original projective integral module. The rank-zero discriminant/degree
formula follows from the empty Gram determinant and the intrinsic
rank-zero degree theorem.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct MeasureTheory

namespace BostConjecture.Arithmetic.HermitianMetric

variable {K : Type*} [Field K] [NumberField K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]
variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
variable (h : HermitianMetric K M)

instance : MeasurableSpace h.TraceSpace := borel h.TraceSpace

instance : BorelSpace h.TraceSpace := ⟨rfl⟩

/-- Euclidean Haar covolume of the actual restriction-of-scalars lattice. -/
def traceCovolume : ℝ := ZLattice.covolume h.traceLattice

theorem traceCovolume_pos : 0 < h.traceCovolume :=
  ZLattice.covolume_pos h.traceLattice volume

/-- The actual Haar covolume is computed by the trace Gram matrix of any
integer basis of the original integral module. -/
theorem traceCovolume_sq_eq_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ M) :
    h.traceCovolume ^ 2 = (Matrix.of fun i j =>
      ∑ σ : K →+* ℂ, ((h.fiber σ).inner
        (fiberSection M σ (b i)) (fiberSection M σ (b j))).re).det := by
  rw [traceCovolume, ZLattice.covolume_sq_eq_det_gram _ (b.map h.traceLatticeEquiv)]
  congr 1

/-- The zero-dimensional lattice has Euclidean Haar covolume one. -/
theorem traceCovolume_eq_one_of_rank_zero
    (hr : Module.finrank K (K ⊗[𝓞 K] M) = 0) : h.traceCovolume = 1 := by
  let := finite_int (K := K) (M := M)
  let := free_int (K := K) (M := M)
  have hz : Module.finrank ℤ M = 0 := by rw [finrank_int (K := K), hr, mul_zero]
  let b := (Module.finBasis ℤ M).reindex (finCongr hz)
  have hs := h.traceCovolume_sq_eq_det b
  rw [Matrix.det_isEmpty] at hs
  nlinarith [h.traceCovolume_pos]

/-- The exact restriction-covolume formula in rank zero, with the same
intrinsic degree and discriminant normalization as the general endpoint. -/
theorem traceCovolume_eq_discr_degree_of_rank_zero
    (hr : Module.finrank K (K ⊗[𝓞 K] M) = 0) :
    h.traceCovolume = |(NumberField.discr K : ℝ)| ^
        ((Module.finrank K (K ⊗[𝓞 K] M) : ℝ) / 2) *
      Real.exp (-(Module.finrank ℚ K : ℝ) * h.degree) := by
  rw [h.traceCovolume_eq_one_of_rank_zero hr, hr, h.degree_eq_zero_of_rank_zero hr]
  simp

end BostConjecture.Arithmetic.HermitianMetric
