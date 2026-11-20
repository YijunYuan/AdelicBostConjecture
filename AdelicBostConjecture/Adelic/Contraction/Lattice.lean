/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import AdelicBostConjecture.Geometry.Tensor.FreeEmbedding
public import ArakelovGeometry.Analysis.Tensor.Basic
public import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Ring.Ultra

/-!
# Integral Specht word estimates

The rectangular orbit lattice is supported on words with the same letter
content. At a finite place, its integral coefficients give the required
epsilon-tensor norm estimate in any integral lattice basis.
-/

@[expose] public section

noncomputable section

namespace AdelicBostConjecture.Adelic.Contraction

open Module Specht OAI.Saxl
open scoped TensorProduct

variable {n a k : ℕ}

/-- A diagonal change of letters multiplies each word coefficient by its
letter-weight product. -/
theorem wordTensorAction_diagonal_apply (r : Fin a → ℝ)
    (x : (Fin n → Fin a) → ℝ) (w : Fin n → Fin a) :
    wordTensorAction n (Matrix.diagonal r) x w = (∏ q, r (w q)) * x w := by
  classical
  change (∑ v, (∏ q, Matrix.diagonal r (w q) (v q)) * x v) = _
  rw [Finset.sum_eq_single w]
  · simp
  · intro v _ hv
    obtain ⟨q, hq⟩ : ∃ q, w q ≠ v q := by
      by_contra! h
      exact hv (funext fun q ↦ (h q).symm)
    have hp : (∏ q, Matrix.diagonal r (w q) (v q)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ q) (by simp [Matrix.diagonal, hq])
    rw [hp, zero_mul]
  · intro h
    exact (h (Finset.mem_univ w)).elim

/-- Every nonzero coefficient of the actual integral rectangular orbit
lattice has the determinant letter weight. No choice of standard basis or
integral straightening theorem is needed. -/
theorem prod_weights_eq_of_orbitLattice_ne_zero (hk : 0 < k)
    (t : Tableau n (rectangle a k)) (x : orbitLattice t)
    (w : Fin n → Fin a)
    (hx : x.val ((rectangleAlphabetEquiv hk).symm w) ≠ 0) (r : Fin a → ℝ) :
    (∏ q, r (w q)) = (∏ i, r i) ^ k := by
  let y : (Fin n → Fin a) → ℝ :=
    fun v ↦ (x.val ((rectangleAlphabetEquiv hk).symm v) : ℝ)
  have hy : y ∈ Submodule.span ℝ (Set.range fun z : orbitLattice t ↦
      fun v ↦ (z.val ((rectangleAlphabetEquiv hk).symm v) : ℝ)) :=
    Submodule.subset_span ⟨x, rfl⟩
  have h := congrFun (wordTensorAction_of_mem_span hk t (Matrix.diagonal r) hy) w
  rw [wordTensorAction_diagonal_apply, Matrix.det_diagonal] at h
  change (∏ q, r (w q)) * y w = (∏ i, r i) ^ k * y w at h
  exact mul_right_cancel₀ (by dsimp only [y]; exact_mod_cast hx : y w ≠ 0) h

private theorem seminorm_sum_le {L W κ : Type*} [NormedField L]
    [AddCommGroup W] [Module L W] (p : Seminorm L W)
    (hp : ∀ x y, p (x + y) ≤ max (p x) (p y))
    (s : Finset κ) (f : κ → W) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ i ∈ s, p (f i) ≤ C) : p (∑ i ∈ s, f i) ≤ C := by
  classical
  induction s using Finset.induction with
  | empty => simpa using hC
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hp _ _).trans (max_le (hf i (Finset.mem_insert_self _ _))
      (ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)))

section FinitePlace

open ArakelovGeometry Geometry

variable {L E : Type*} [NormedField L] [CompleteSpace L] [IsUltrametricDist L]
  [NormedAddCommGroup E] [NormedSpace L E] [FiniteDimensional L E]

/-- An integral rectangular lattice vector has injective tensor norm bounded
by the balanced product of the basis-vector norms. The bound uses the actual
`freeLatticeMap` and is valid for trivial valuations. -/
theorem injective_freeLatticeMap_one_tmul_le (hk : 0 < k)
    (t : Tableau n (rectangle a k)) (b : Basis (Fin a) L E) (x : orbitLattice t) :
    injectiveTensorSeminorm (freeLatticeMap hk t b (1 ⊗ₜ[ℤ] x)) ≤
      (∏ i, ‖b i‖) ^ k := by
  classical
  let B := Basis.piTensorProduct (fun _ : Fin n ↦ b)
  rw [freeLatticeMap_tmul, one_smul]
  change injectiveTensorSeminorm (B.equivFun.symm
    (fun w ↦ (x.val ((rectangleAlphabetEquiv hk).symm w) : L))) ≤ _
  rw [Basis.equivFun_symm_apply]
  refine seminorm_sum_le (L := L) (injectiveTensorSeminorm (E := fun _ : Fin n ↦ E))
    (injectiveTensorSeminorm_add_le_max IsUltrametricDist.norm_add_le_max)
    Finset.univ _ (pow_nonneg (Finset.prod_nonneg fun i _ ↦ norm_nonneg (b i)) k) ?_
  intro w _
  by_cases hx : x.val ((rectangleAlphabetEquiv hk).symm w) = 0
  · simp only [hx, Int.cast_zero, zero_smul, map_zero]
    exact pow_nonneg (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _) _
  rw [map_smul_eq_mul]
  have hB : injectiveTensorSeminorm (B w) ≤ ∏ q, ‖b (w q)‖ := by
    rw [show B w = ⨂ₜ[L] q, b (w q) from Basis.piTensorProduct_apply _ _]
    exact (injectiveTensorSeminorm_le_projective _).trans
      (PiTensorProduct.projectiveSeminorm_tprod_le (fun q ↦ b (w q)))
  calc
    ‖(x.val ((rectangleAlphabetEquiv hk).symm w) : L)‖ *
        injectiveTensorSeminorm (B w) ≤ 1 * ∏ q, ‖b (w q)‖ :=
      mul_le_mul (IsUltrametricDist.norm_intCast_le_one L _) hB
        (apply_nonneg _ _) zero_le_one
    _ = (∏ i, ‖b i‖) ^ k := by
      rw [one_mul]
      exact prod_weights_eq_of_orbitLattice_ne_zero hk t x w hx (fun i ↦ ‖b i‖)

/-- The actual lattice realization is bounded by its integral-basis maximum
norm times the balanced basis weight. -/
theorem injective_freeLatticeMap_le {κ : Type*} [Fintype κ]
    (hk : 0 < k) (t : Tableau n (rectangle a k)) (b : Basis (Fin a) L E)
    (c : Basis κ ℤ (orbitLattice t)) (z : L ⊗[ℤ] orbitLattice t) :
    injectiveTensorSeminorm (freeLatticeMap hk t b z) ≤
      (∏ i, ‖b i‖) ^ k * ‖(c.baseChange L).equivFun z‖ := by
  classical
  have hweight : 0 ≤ (∏ i, ‖b i‖) ^ k :=
    pow_nonneg (Finset.prod_nonneg fun i _ ↦ norm_nonneg (b i)) k
  conv_lhs => rw [← (c.baseChange L).sum_repr z, map_sum]
  refine seminorm_sum_le (L := L) (injectiveTensorSeminorm (E := fun _ : Fin n ↦ E))
    (injectiveTensorSeminorm_add_le_max IsUltrametricDist.norm_add_le_max)
    Finset.univ _ (mul_nonneg hweight (norm_nonneg _)) ?_
  intro j _
  rw [map_smul, map_smul_eq_mul, Basis.baseChange_apply]
  calc
    ‖(c.baseChange L).repr z j‖ *
        injectiveTensorSeminorm (freeLatticeMap hk t b (1 ⊗ₜ[ℤ] c j)) ≤
        ‖(c.baseChange L).equivFun z‖ * (∏ i, ‖b i‖) ^ k :=
      mul_le_mul (norm_le_pi_norm ((c.baseChange L).equivFun z) j)
        (injective_freeLatticeMap_one_tmul_le hk t b (c j))
        (apply_nonneg _ _) (norm_nonneg _)
    _ = _ := mul_comm _ _

end FinitePlace

end AdelicBostConjecture.Adelic.Contraction
