/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Ring.Real

/-!
# Finiteness of integral actions in compact real frames

Integer matrices form a closed discrete subset of real matrices. Conjugating
a compact family of real operators by a compact family of invertible frames
therefore leaves only finitely many possible integer action matrices.

Reference: this paper, page 11, Lemma 7.1.
-/

@[expose] public section

noncomputable section

open Matrix Topology

namespace BostConjecture.Arithmetic.Compactness

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- Integer matrices lying in a compact set of real matrices form a finite set. -/
theorem finite_integral_matrices_in_compact [Finite ι] {S : Set (Matrix ι ι ℝ)} (hS : IsCompact S) :
    {N : Matrix ι ι ℤ | N.map (Int.castRingHom ℝ) ∈ S}.Finite := by
  let := Fintype.ofFinite ι
  have he : IsClosedEmbedding (fun N : Matrix ι ι ℤ => N.map (Int.castRingHom ℝ)) :=
    IsClosedEmbedding.piMap (fun _ => IsClosedEmbedding.piMap
      (fun _ => Int.isClosedEmbedding_coe_real))
  exact (he.isCompact_preimage hS).finite_of_discrete

/-- A compact family of frames and a compact family of real operators allow
only finitely many integral matrices for the operators in those frames. -/
theorem finite_integral_conjugates
    {S : Set (GeneralLinearGroup ι ℝ)} (hS : IsCompact S)
    {T : Set (Matrix ι ι ℝ)} (hT : IsCompact T) :
    {N : Matrix ι ι ℤ | ∃ B ∈ S,
      B.val * N.map (Int.castRingHom ℝ) * (B⁻¹).val ∈ T}.Finite := by
  let f : GeneralLinearGroup ι ℝ × Matrix ι ι ℝ → Matrix ι ι ℝ :=
    fun p => (p.1⁻¹).val * p.2 * p.1.val
  have hf : Continuous f :=
    ((Units.continuous_val.comp (continuous_fst.inv)).mul continuous_snd).mul
      (Units.continuous_val.comp continuous_fst)
  apply (finite_integral_matrices_in_compact ((hS.prod hT).image hf)).subset
  rintro N ⟨B, hB, hN⟩
  refine ⟨(B, B.val * N.map (Int.castRingHom ℝ) * (B⁻¹).val), ⟨hB, hN⟩, ?_⟩
  change (B⁻¹).val * (B.val * N.map (Int.castRingHom ℝ) * (B⁻¹).val) * B.val = _
  simp only [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  simp [mul_assoc]

/-- In compact frames, a uniform entry bound on the real operator implies
finiteness of its integral coordinate matrices. -/
theorem finite_bounded_integral_conjugates
    {S : Set (GeneralLinearGroup ι ℝ)} (hS : IsCompact S) (C : ℝ) :
    {N : Matrix ι ι ℤ | ∃ B ∈ S, ∀ i j,
      |(B.val * N.map (Int.castRingHom ℝ) * (B⁻¹).val) i j| ≤ C}.Finite := by
  have hT : IsCompact {A : Matrix ι ι ℝ | ∀ i j, A i j ∈ Set.Icc (-C) C} :=
    isCompact_pi_infinite (fun _ => isCompact_pi_infinite (fun _ => isCompact_Icc))
  convert finite_integral_conjugates hS hT using 1
  ext N
  simp only [Set.mem_ofPred_eq, Set.mem_Icc, abs_le]

end BostConjecture.Arithmetic.Compactness
