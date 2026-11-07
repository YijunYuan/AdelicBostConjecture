/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.RestrictionCovolume.Quotient
public import BostConjecture.Arithmetic.RestrictionCovolume.Covolume
public import Mathlib.LinearAlgebra.Basis.Prod

/-!
# Trace covolume in a saturated exact sequence

An integral splitting combines integer bases. Its real basis differs from
the orthogonal splitting by a triangular matrix of determinant one.
The orthogonal Gram blocks are the actual induced and quotient trace
Gram matrices, so their Euclidean Haar covolumes multiply.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct Module


namespace BostConjecture.Arithmetic.HermitianMetric

variable {K : Type*} [Field K] [NumberField K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]
variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
variable (h : HermitianMetric K M)

lemma traceCovolume_sq_eq_gram {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℤ M) : h.traceCovolume ^ 2 = (Matrix.gram ℝ (h.traceBasis b)).det := by
  rw [h.traceCovolume_sq_eq_det b]
  congr 1
  ext i j
  simp only [Matrix.gram_apply, traceBasis_apply]
  rfl

/-- A determinant-one change of a real basis preserves its Gram determinant. -/
lemma det_gram_eq_of_basis_det_eq_one {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b c : Basis ι ℝ E)
    (hc : c.det b = 1) : (Matrix.gram ℝ b).det = (Matrix.gram ℝ c).det := by
  have hn : Module.finrank ℝ E = Fintype.card ι := Module.finrank_eq_card_basis b
  let o := (stdOrthonormalBasis ℝ E).reindex (Fintype.equivFinOfCardEq hn.symm).symm
  have he := o.toBasis.det_mul_det c b
  rw [hc, mul_one] at he
  rw [o.det_gram_eq_norm_det_sq, o.det_gram_eq_norm_det_sq, ← he]

/-- The real trace covolume multiplies for an actual saturated integral sequence. -/
theorem traceCovolume_exact (P : Submodule (𝓞 K) M)
    [Module.Projective (𝓞 K) (M ⧸ P)] :
    h.traceCovolume = (h.submodule P).traceCovolume * (h.quotient P).traceCovolume := by
  let := finite_int (K := K) (M := P)
  let := free_int (K := K) (M := P)
  let := finite_int (K := K) (M := M ⧸ P)
  let := free_int (K := K) (M := M ⧸ P)
  obtain ⟨s, hs⟩ := P.mkQ.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr P.mkQ_surjective)
  let eZ := ((LinearMap.exact_subtype_mkQ P).splitSurjectiveEquiv P.injective_subtype
    ⟨s, hs⟩).1.symm
  let pZ := Module.finBasis ℤ P
  let qZ := Module.finBasis ℤ (M ⧸ P)
  let bZ := (pZ.prod qZ).map (eZ.restrictScalars ℤ)
  let p := (h.submodule P).traceBasis pZ
  let q := (h.quotient P).traceBasis qZ
  let e := h.traceSplitEquiv P
  let c := (p.prod q).map e
  let b := h.traceBasis bZ
  have hb₁ (i) : b (Sum.inl i) = h.traceSection (pZ i : M) := by
    simp only [b, bZ, traceBasis_apply, Basis.map_apply]
    change h.traceSection (((pZ.prod qZ) (Sum.inl i)).1 + s (((pZ.prod qZ) (Sum.inl i)).2)) = _
    rw [Basis.prod_apply_inl_fst, Basis.prod_apply_inl_snd]
    simp
  have hb₂ (j) : b (Sum.inr j) = h.traceSection (s (qZ j)) := by
    simp only [b, bZ, traceBasis_apply, Basis.map_apply]
    change h.traceSection (((pZ.prod qZ) (Sum.inr j)).1 + s (((pZ.prod qZ) (Sum.inr j)).2)) = _
    rw [Basis.prod_apply_inr_fst, Basis.prod_apply_inr_snd]
    simp
  have hc₁ (i) : c (Sum.inl i) = (h.submodule P).traceMap h P.subtype (p i) := by
    simp only [c, e, Basis.map_apply, traceSplitEquiv_apply,
      Basis.prod_apply_inl_fst, Basis.prod_apply_inl_snd]
    rw [show h.traceLift P.mkQ P.mkQ_surjective (0 : (h.quotient P).TraceSpace) = 0 from
      (h.traceLift P.mkQ P.mkQ_surjective).map_zero, add_zero]
  have hc₂ (j) : c (Sum.inr j) = h.traceLift P.mkQ P.mkQ_surjective (q j) := by
    simp [c, e]
  have hleft (i) : b (Sum.inl i) = c (Sum.inl i) := by
    rw [hb₁, hc₁]
    simp only [p, traceBasis_apply, traceMap_section]
    rfl
  have hright (j) : (e.symm (b (Sum.inr j))).2 = q j := by
    rw [h.traceSplitEquiv_symm_snd, hb₂, h.traceMap_section]
    have hh := LinearMap.congr_fun hs (qZ j)
    change P.mkQ (s (qZ j)) = qZ j at hh
    rw [hh]
    exact ((h.quotient P).traceBasis_apply qZ j).symm
  let C := Matrix.of fun i j => p.repr (e.symm (b (Sum.inr j))).1 i
  have hmat : c.toMatrix b = Matrix.fromBlocks 1 C 0 1 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simp [Basis.toMatrix_apply, hleft, Matrix.one_apply, Finsupp.single_apply, eq_comm]
    · rfl
    · simp [Basis.toMatrix_apply, hleft]
    · change q.repr (e.symm (b (Sum.inr j))).2 i = _
      rw [hright]
      simp [Matrix.one_apply, Finsupp.single_apply, eq_comm]
  have hdet : c.det b = 1 := by
    rw [Basis.det_apply, hmat, Matrix.det_fromBlocks_zero₂₁]
    simp
  have hgram : Matrix.gram ℝ c = Matrix.fromBlocks (Matrix.gram ℝ p) 0 0 (Matrix.gram ℝ q) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · rw [Matrix.gram_apply, hc₁, hc₁]
      exact h.traceMap_pullback_inner P.subtype P.injective_subtype (p i) (p j)
    · rw [Matrix.gram_apply, hc₁, hc₂]
      exact h.traceLift_orthogonal P (p i) (q j)
    · rw [Matrix.gram_apply, hc₂, hc₁, real_inner_comm]
      exact h.traceLift_orthogonal P (p j) (q i)
    · rw [Matrix.gram_apply, hc₂, hc₂]
      exact h.traceLift_inner P.mkQ P.mkQ_surjective (q i) (q j)
  have heq : h.traceCovolume ^ 2 =
      (h.submodule P).traceCovolume ^ 2 * (h.quotient P).traceCovolume ^ 2 := by
    rw [h.traceCovolume_sq_eq_gram bZ, det_gram_eq_of_basis_det_eq_one b c hdet,
      hgram, Matrix.det_fromBlocks_zero₂₁,
      ← (h.submodule P).traceCovolume_sq_eq_gram pZ,
      ← (h.quotient P).traceCovolume_sq_eq_gram qZ]
  apply (sq_eq_sq₀ (le_of_lt h.traceCovolume_pos)
    (le_of_lt (mul_pos (h.submodule P).traceCovolume_pos (h.quotient P).traceCovolume_pos))).mp
  simpa only [mul_pow] using heq

end BostConjecture.Arithmetic.HermitianMetric
