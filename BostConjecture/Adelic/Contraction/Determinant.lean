/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.Analysis.Determinant.Basic
public import ArakelovGeometry.Analysis.Determinant.Pairing
public import ArakelovGeometry.AdelicVectorBundle.Determinant.Universal
import ArakelovGeometry.Analysis.AbsoluteValue.Basic

/-!
# Non-Archimedean determinant estimates

The determinant estimate used in Lemma 6.1 of this paper, with no
nontriviality hypothesis on the absolute value.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Adelic.Contraction

open ArakelovGeometry Module

variable {L E ι : Type*} [NormedField L] [IsUltrametricDist L]
  [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace L E]

/-- Coordinate bounds in a nearly orthogonal basis give the determinant bound
without a factorial loss. The field may carry the trivial norm. -/
theorem norm_basis_det_le (b : Basis ι L E) (c : ι → ℝ)
    (hc : ∀ i x, ‖b.coord i x‖ ≤ c i * ‖x‖) (x : ι → E) :
    ‖b.det x‖ ≤ (∏ i, c i) * ∏ i, ‖x i‖ := by
  rw [Basis.det_apply]
  apply norm_det_le_prod_of_entry_le _ c (fun i ↦ ‖x i‖)
  intro i j
  exact hc i (x j)

/-- The dual coordinate operator norms give an intrinsic version of the
non-Archimedean determinant bound. -/
theorem norm_basis_det_le_dual_prod [CompleteSpace L] [FiniteDimensional L E]
    (b : Basis ι L E) (x : ι → E) :
    ‖b.det x‖ ≤ (∏ i, linearMapOperatorSeminorm (b.coord i)) * ∏ i, ‖x i‖ :=
  norm_basis_det_le b _ (fun i x ↦ norm_linearMap_apply_le (b.coord i) x) x

/-- A weighted coordinate lower bound passes to the determinant. This is the
local algebraic estimate behind the alpha-orthogonal-basis argument. -/
theorem prod_mul_norm_basis_det_le (b : Basis ι L E) (w : ι → ℝ)
    (hw : ∀ i, 0 < w i) (hb : ∀ i x, w i * ‖b.coord i x‖ ≤ ‖x‖)
    (x : ι → E) :
    (∏ i, w i) * ‖b.det x‖ ≤ ∏ i, ‖x i‖ := by
  have hcoord (i : ι) (y : E) : ‖b.coord i y‖ ≤ (w i)⁻¹ * ‖y‖ := by
    rw [← div_eq_inv_mul]
    exact (le_div_iff₀ (hw i)).2 (by simpa only [mul_comm] using hb i y)
  have hprod : (∏ i, w i) ≠ 0 :=
    ne_of_gt (Finset.prod_pos fun i _ ↦ hw i)
  calc
    (∏ i, w i) * ‖b.det x‖ ≤
        (∏ i, w i) * ((∏ i, (w i)⁻¹) * ∏ i, ‖x i‖) :=
      mul_le_mul_of_nonneg_left (norm_basis_det_le b _ hcoord x)
        (Finset.prod_nonneg fun i _ ↦ (hw i).le)
    _ = ∏ i, ‖x i‖ := by
      rw [Finset.prod_inv_distrib, ← mul_assoc, mul_inv_cancel₀ hprod, one_mul]

omit [IsUltrametricDist L] [Fintype ι] [DecidableEq ι] in
/-- Nearly optimal bases supply the coordinate half of alpha-orthogonality.
This includes trivially valued complete fields. -/
theorem exists_basis_coord_bound [CompleteSpace L] [FiniteDimensional L E] [Finite ι]
    (b : Basis ι L E) {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ e : Basis ι L E, ∀ i x, α * ‖e i‖ * ‖e.coord i x‖ ≤ ‖x‖ := by
  obtain ⟨e, he⟩ := exists_basis_mul_dual_norm_le b hα hα1
  refine ⟨e, fun i x ↦ ?_⟩
  have hi : α * (‖e i‖ * linearMapOperatorSeminorm (e.coord i)) ≤ 1 := by
    simpa only [mul_inv_cancel₀ hα.ne'] using
      mul_le_mul_of_nonneg_left (he i).2 hα.le
  calc
    α * ‖e i‖ * ‖e.coord i x‖ ≤
        α * ‖e i‖ * (linearMapOperatorSeminorm (e.coord i) * ‖x‖) :=
      mul_le_mul_of_nonneg_left (norm_linearMap_apply_le (e.coord i) x)
        (mul_nonneg hα.le (norm_nonneg _))
    _ = (α * (‖e i‖ * linearMapOperatorSeminorm (e.coord i))) * ‖x‖ := by ring
    _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hi (norm_nonneg _)
    _ = ‖x‖ := one_mul _

section Completed

open scoped TensorProduct

variable {K V : Type*} [Field K] {S : AdelicStructure K}
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Weighted coordinate bounds give the basis-wedge lower bound for the
actual completed determinant norm. -/
theorem determinant_norm_basis_ge_weight (ξ : NormFamily S V) (ω : S.Ω)
    (hω : ω ∈ S.Ωfin)
    (b : Basis (Fin (Module.finrank K V)) (S.ϕ ω).Completion
      ((S.ϕ ω).Completion ⊗[K] V))
    (w : Fin (Module.finrank K V) → ℝ) (hw : ∀ i, 0 < w i)
    (hb : ∀ i x, w i * ‖b.coord i x‖ ≤ ξ.norm ω x) :
    (∏ i, w i) ≤ ξ.determinant.norm ω
      ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion V (Module.finrank K V)).symm
        (exteriorPower.ιMulti (S.ϕ ω).Completion (Module.finrank K V) b)) := by
  let f : ((S.ϕ ω).Completion ⊗[K] (⋀[K]^(Module.finrank K V) V)) →ₗ[(S.ϕ ω).Completion]
      (S.ϕ ω).Completion :=
    LinearMap.comp (exteriorPower.alternatingMapLinearEquiv
      (R := (S.ϕ ω).Completion) (M := (S.ϕ ω).Completion ⊗[K] V)
      (N := (S.ϕ ω).Completion) (n := Module.finrank K V) b.det)
      (exteriorBaseChangeEquiv K (S.ϕ ω).Completion V (Module.finrank K V)).toLinearMap
  let p : Seminorm (S.ϕ ω).Completion
      ((S.ϕ ω).Completion ⊗[K] (⋀[K]^(Module.finrank K V) V)) :=
    NNReal.mk (∏ i, w i) (Finset.prod_nonneg fun i _ ↦ (hw i).le) •
      (normSeminorm (S.ϕ ω).Completion (S.ϕ ω).Completion).comp f
  have hp (x : Fin (Module.finrank K V) → (S.ϕ ω).Completion ⊗[K] V) :
      p ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion V (Module.finrank K V)).symm
        (exteriorPower.ιMulti (S.ϕ ω).Completion (Module.finrank K V) x)) ≤
          ∏ i, ξ.norm ω (x i) := by
    let := ξ.fibreNormedAddCommGroup ω
    let := ξ.fibreNormedSpace ω
    let : IsUltrametricDist (S.ϕ ω).Completion :=
      (S.ϕ ω).isUltrametricDist_completion hω
    change (∏ i, w i) * ‖f ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion V
      (Module.finrank K V)).symm (exteriorPower.ιMulti (S.ϕ ω).Completion
        (Module.finrank K V) x))‖ ≤ _
    simp only [f, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    exact prod_mul_norm_basis_det_le b w hw hb x
  have h := ξ.seminorm_le_determinant_of_ιMulti_le ω p hp
    ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion V (Module.finrank K V)).symm
      (exteriorPower.ιMulti (S.ϕ ω).Completion (Module.finrank K V) b))
  change (∏ i, w i) * ‖f ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion V
    (Module.finrank K V)).symm (exteriorPower.ιMulti (S.ϕ ω).Completion
      (Module.finrank K V) b))‖ ≤ _ at h
  simpa only [f, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    Basis.det_self, norm_one, mul_one] using h

/-- The alpha-orthogonal lower determinant bound of Lemma 6.1 on the actual
AG completed fibre. No discreteness or nontrivial valuation is assumed. -/
theorem determinant_norm_basis_ge (ξ : NormFamily S V) (ω : S.Ω)
    (hω : ω ∈ S.Ωfin)
    (b : Basis (Fin (Module.finrank K V)) (S.ϕ ω).Completion
      ((S.ϕ ω).Completion ⊗[K] V))
    {α : ℝ} (hα : 0 < α)
    (hb : ∀ i x, α * ξ.norm ω (b i) * ‖b.coord i x‖ ≤ ξ.norm ω x) :
    α ^ Module.finrank K V * (∏ i, ξ.norm ω (b i)) ≤
      ξ.determinant.norm ω
        ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion V (Module.finrank K V)).symm
          (exteriorPower.ιMulti (S.ϕ ω).Completion (Module.finrank K V) b)) := by
  have h := determinant_norm_basis_ge_weight ξ ω hω b
    (fun i ↦ α * ξ.norm ω (b i))
    (fun i ↦ mul_pos hα (ξ.norm_pos ω (b.ne_zero i))) hb
  simpa only [LinearEquiv.apply_symm_apply,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, Basis.det_self, norm_one,
    mul_one, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] using h

/-- Such determinant-controlled bases exist at every non-Archimedean place
for every alpha strictly between zero and one. -/
theorem exists_completed_basis_det_bound (ξ : NormFamily S V) (ω : S.Ω)
    (hω : ω ∈ S.Ωfin) {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ b : Basis (Fin (Module.finrank K V)) (S.ϕ ω).Completion
        ((S.ϕ ω).Completion ⊗[K] V),
      (∀ i x, α * ξ.norm ω (b i) * ‖b.coord i x‖ ≤ ξ.norm ω x) ∧
      α ^ Module.finrank K V * (∏ i, ξ.norm ω (b i)) ≤
        ξ.determinant.norm ω
          ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion V (Module.finrank K V)).symm
            (exteriorPower.ιMulti (S.ϕ ω).Completion (Module.finrank K V) b)) := by
  obtain ⟨b, hb⟩ := ξ.exists_completedBasis_norm_mul_dual_norm_le ω hα hα1
  have hcoord (i) (x : (S.ϕ ω).Completion ⊗[K] V) :
      α * ξ.norm ω (b i) * ‖b.coord i x‖ ≤ ξ.norm ω x := by
    let d := ξ.dual.norm ω
      ((dualBaseChangeEquiv K (S.ϕ ω).Completion V).symm (b.coord i))
    have hi : α * (ξ.norm ω (b i) * d) ≤ 1 := by
      simpa only [mul_inv_cancel₀ hα.ne'] using
        mul_le_mul_of_nonneg_left (hb i).2 hα.le
    have heval : ‖b.coord i x‖ ≤ d * ξ.norm ω x := by
      simpa only [LinearEquiv.apply_symm_apply] using ξ.norm_dual_apply_le ω
        ((dualBaseChangeEquiv K (S.ϕ ω).Completion V).symm (b.coord i)) x
    calc
      α * ξ.norm ω (b i) * ‖b.coord i x‖ ≤
          α * ξ.norm ω (b i) * (d * ξ.norm ω x) :=
        mul_le_mul_of_nonneg_left heval (mul_nonneg hα.le (ξ.norm_nonneg ω _))
      _ = (α * (ξ.norm ω (b i) * d)) * ξ.norm ω x := by ring
      _ ≤ 1 * ξ.norm ω x := mul_le_mul_of_nonneg_right hi (ξ.norm_nonneg ω _)
      _ = ξ.norm ω x := one_mul _
  exact ⟨b, hcoord, determinant_norm_basis_ge ξ ω hω b hα hcoord⟩

end Completed

end BostConjecture.Adelic.Contraction
