/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Gram determinants and covolumes of integral lattices

The square of the covolume of a full integral lattice is the Gram determinant
of an integral basis. Inclusion of full lattices reverses their covolumes.
The ambient space is any finite-dimensional real inner product space, equipped
with its inner-product volume; this also covers lattices in real Specht spaces.

Adapted from `TauCeti/Algebra/Module/ZLattice/Covolume.lean` and
`TauCeti/Analysis/InnerProductSpace/Gram/Hadamard.lean` at TauCeti revision
`b3b0334ab9203d9faee4b2f34cd75161463ecdd0`. Changes for Lean/mathlib 4.35.0
and exact source hashes are recorded in `vendor/tauceti/PROVENANCE.json`;
the upstream license is preserved in `vendor/tauceti/LICENSE`.
-/

public section

noncomputable section

open Module MeasureTheory Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Gram determinant is the square of the absolute coordinate determinant
in an orthonormal basis. -/
theorem OrthonormalBasis.det_gram_eq_norm_det_sq {ι : Type*} [Fintype ι]
    [DecidableEq ι] (o : OrthonormalBasis ι ℝ E) (v : ι → E) :
    (Matrix.gram ℝ v).det = ‖o.toBasis.det v‖ ^ 2 := by
  rw [Matrix.gram_eq_conjTranspose_mul o, Matrix.det_mul, Matrix.det_conjTranspose,
    RCLike.star_def, RCLike.conj_mul, Basis.det_apply]
  have hM : o.toBasis.toMatrix v = Matrix.of fun i j ↦ o.repr (v j) i := by
    ext
    simp [Basis.toMatrix_apply]
  simp [hM]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The half-open fundamental parallelepiped of an orthonormal basis has volume one. -/
@[simp]
theorem OrthonormalBasis.volume_fundamentalDomain {ι : Type*} [Fintype ι]
    (o : OrthonormalBasis ι ℝ E) : volume (ZSpan.fundamentalDomain o.toBasis) = 1 := by
  rw [measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped o.toBasis volume),
    OrthonormalBasis.coe_toBasis, o.volume_parallelepiped]

/-- The orthonormal fundamental parallelepiped has real-valued volume one. -/
@[simp]
theorem OrthonormalBasis.volume_real_fundamentalDomain {ι : Type*} [Fintype ι]
    (o : OrthonormalBasis ι ℝ E) : volume.real (ZSpan.fundamentalDomain o.toBasis) = 1 := by
  simp [measureReal_def]

/-- The square of a full lattice's covolume is the Gram determinant of an integral basis. -/
theorem ZLattice.covolume_sq_eq_det_gram (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ L) :
    ZLattice.covolume L ^ 2 = (Matrix.gram ℝ fun i ↦ (b i : E)).det := by
  have hcard : finrank ℝ E = Fintype.card ι := by
    rw [← ZLattice.rank ℝ L, finrank_eq_card_basis b]
  let o : OrthonormalBasis ι ℝ E :=
    (stdOrthonormalBasis ℝ E).reindex (Fintype.equivFinOfCardEq hcard.symm).symm
  rw [ZLattice.covolume_eq_det_mul_measureReal L volume b o.toBasis,
    o.volume_real_fundamentalDomain, mul_one, o.det_gram_eq_norm_det_sq]
  simp [Function.comp_def]

/-- The integral span of a real basis has squared covolume equal to its Gram determinant. -/
theorem ZLattice.covolume_span_sq_eq_det_gram {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℝ E) : ZLattice.covolume (span ℤ (Set.range b)) ^ 2 =
      (Matrix.gram ℝ b).det := by
  rw [ZLattice.covolume_sq_eq_det_gram _ (b.restrictScalars ℤ)]
  simp only [Basis.restrictScalars_apply]

/-- A discrete superlattice of a full lattice has no greater covolume. -/
theorem ZLattice.covolume_le_covolume_of_le {L₁ L₂ : Submodule ℤ E}
    [DiscreteTopology L₁] [IsZLattice ℝ L₁] [DiscreteTopology L₂] (h : L₁ ≤ L₂) :
    ZLattice.covolume L₂ ≤ ZLattice.covolume L₁ := by
  have : IsZLattice ℝ L₂ :=
    ⟨eq_top_iff.2 (IsZLattice.span_top (K := ℝ) (L := L₁) ▸ span_mono h)⟩
  have hindex_pos : (0 : ℝ) < L₁.toAddSubgroup.relIndex L₂.toAddSubgroup := by
    rw [← ZLattice.covolume_div_covolume_eq_relIndex' L₁ L₂ h]
    exact div_pos (ZLattice.covolume_pos L₁ volume) (ZLattice.covolume_pos L₂ volume)
  have hindex : 1 ≤ L₁.toAddSubgroup.relIndex L₂.toAddSubgroup :=
    Nat.succ_le_iff.mpr (by exact_mod_cast hindex_pos)
  have hquot : (1 : ℝ) ≤ ZLattice.covolume L₁ / ZLattice.covolume L₂ := by
    rw [ZLattice.covolume_div_covolume_eq_relIndex' L₁ L₂ h]
    exact_mod_cast hindex
  simpa only [one_mul] using (le_div_iff₀ (ZLattice.covolume_pos L₂ volume)).mp hquot
