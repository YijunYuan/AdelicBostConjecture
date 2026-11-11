/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Adelic.Contraction.Lattice
public import BostConjecture.Adelic.Contraction.Determinant
public import BostConjecture.Geometry.Determinant.Frame
public import ArakelovGeometry.AdelicVectorBundle.Tensor.Basic

/-!
# Non-Archimedean determinant-twisted lattice maps

Nearly orthogonal determinant lower bounds remove the basis weight from the
integral lattice estimate. The map is the existing algebraic determinant map.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Adelic.Contraction

open Module ArakelovGeometry Geometry Specht OAI.Saxl Filter
open scoped TensorProduct Topology

variable {L E : Type*} [NormedField L] [CompleteSpace L] [IsUltrametricDist L]
  [NormedAddCommGroup E] [NormedSpace L E] [FiniteDimensional L E]
  {n a k : ℕ} {κ : Type*} [Fintype κ]

omit [CompleteSpace L] [IsUltrametricDist L] [FiniteDimensional L E] in
/-- A determinant-line seminorm is bounded below by its value on the basis
wedge times the absolute value of the determinant coordinate. -/
theorem determinant_seminorm_eq_coord (p : Seminorm L (⋀[L]^a E))
    (b : Basis (Fin a) L E) (η : ⋀[L]^a E) :
    p η = ‖determinantCoordinates b η‖ * p (exteriorPower.ιMulti L a b) := by
  obtain ⟨r, rfl⟩ := (determinantCoordinates b).symm.surjective η
  rw [LinearEquiv.apply_symm_apply, determinantCoordinates_symm_apply, map_smul_eq_mul]

/-- The alpha loss cancels against a nearly orthogonal basis and disappears
as alpha tends to one. This is a contraction estimate for the actual
determinant-twisted lattice map on products of determinant vectors. -/
theorem injective_freeDeterminantMap_tprod_le
    (hk : 0 < k) (t : Tableau n (rectangle a k)) (b₀ : Basis (Fin a) L E)
    (c : Basis κ ℤ (orbitLattice t)) (p : Seminorm L (⋀[L]^a E))
    (hp : ∀ α : ℝ, 0 < α → α < 1 → ∃ b : Basis (Fin a) L E,
      α ^ a * (∏ i, ‖b i‖) ≤ p (exteriorPower.ιMulti L a b))
    (η : Fin k → ⋀[L]^a E) (z : L ⊗[ℤ] orbitLattice t) :
    injectiveTensorSeminorm
      (freeDeterminantMap hk t b₀ ((⨂ₜ[L] q, η q) ⊗ₜ[L] z)) ≤
      (∏ q, p (η q)) * ‖(c.baseChange L).equivFun z‖ := by
  classical
  let A := injectiveTensorSeminorm
    (freeDeterminantMap hk t b₀ ((⨂ₜ[L] q, η q) ⊗ₜ[L] z))
  have hα (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
      α ^ (a * k) * A ≤ (∏ q, p (η q)) * ‖(c.baseChange L).equivFun z‖ := by
    obtain ⟨b, hb⟩ := hp α hα hα1
    have hcoord (q : Fin k) :
        (α ^ a * (∏ i, ‖b i‖)) * ‖determinantCoordinates b (η q)‖ ≤ p (η q) := by
      rw [determinant_seminorm_eq_coord p b (η q)]
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left hb (norm_nonneg (determinantCoordinates b (η q)))
    have hprod := Finset.prod_le_prod₀
      (fun q (_ : q ∈ (Finset.univ : Finset (Fin k))) ↦
        mul_nonneg (mul_nonneg (pow_nonneg hα.le _) (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _))
          (norm_nonneg (determinantCoordinates b (η q))))
      (fun q _ ↦ hcoord q)
    have hmap : A ≤ (∏ q, ‖determinantCoordinates b (η q)‖) *
        (∏ i, ‖b i‖) ^ k * ‖(c.baseChange L).equivFun z‖ := by
      dsimp [A]
      rw [freeDeterminantMap_eq hk t b₀ b, freeDeterminantMap_tmul,
        map_smul_eq_mul, determinantPowerCoordinates_tprod, norm_prod]
      calc
        _ ≤ (∏ q, ‖determinantCoordinates b (η q)‖) *
            ((∏ i, ‖b i‖) ^ k * ‖(c.baseChange L).equivFun z‖) :=
          mul_le_mul_of_nonneg_left (injective_freeLatticeMap_le hk t b c z)
            (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)
        _ = _ := by simp only [Basis.equivFun_apply]; ring
    calc
      α ^ (a * k) * A ≤ α ^ (a * k) *
          ((∏ q, ‖determinantCoordinates b (η q)‖) * (∏ i, ‖b i‖) ^ k *
            ‖(c.baseChange L).equivFun z‖) :=
        mul_le_mul_of_nonneg_left hmap (pow_nonneg hα.le _)
      _ = (∏ q, (α ^ a * (∏ i, ‖b i‖)) *
          ‖determinantCoordinates b (η q)‖) * ‖(c.baseChange L).equivFun z‖ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin, mul_pow, ← pow_mul]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
  have hlim : Tendsto (fun α : ℝ ↦ α ^ (a * k) * A) (𝓝[<] 1) (𝓝 A) := by
    have hcont : ContinuousAt (fun α : ℝ ↦ α ^ (a * k) * A) 1 := by fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with α hα'
  exact hα α hα'.1 hα'.2

section Completed

variable {K V : Type*} [Field K] {S : AdelicStructure K}
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

set_option maxHeartbeats 800000 in
-- Comparing the algebraic completion's ring projections in exterior powers is costly.
set_option backward.isDefEq.respectTransparency false in
/-- In any completed frame, the lattice realization is bounded by the actual
norm of its determinant wedge, with no alpha loss. This is the finite-place
normalization of the determinant embedding on the full Specht factor. -/
theorem injective_freeLatticeMap_completed_le
    (ξ : NormFamily S V) (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (hk : 0 < k) (t : Tableau n (rectangle (Module.finrank K V) k))
    (b₀ : Basis (Fin (Module.finrank K V)) (S.ϕ ω).Completion
      ((S.ϕ ω).Completion ⊗[K] V))
    (c : Basis κ ℤ (orbitLattice t))
    (z : (S.ϕ ω).Completion ⊗[ℤ] orbitLattice t) :
    (NormFamily.injectiveTensor (fun _ : Fin n ↦ ξ)).norm ω
      ((tensorBaseChangeEquiv K (S.ϕ ω).Completion (fun _ : Fin n ↦ V)).symm
        (freeLatticeMap hk t b₀ z)) ≤
      (ξ.determinant.norm ω
        ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion V (Module.finrank K V)).symm
          (exteriorPower.ιMulti (S.ϕ ω).Completion (Module.finrank K V) b₀))) ^ k *
        ‖(c.baseChange (S.ϕ ω).Completion).equivFun z‖ := by
  let := ξ.fibreNormedAddCommGroup ω
  let := ξ.fibreNormedSpace ω
  let : IsUltrametricDist (S.ϕ ω).Completion :=
    (S.ϕ ω).isUltrametricDist_completion hω
  let p := (ξ.determinant.norm ω).comp
    (exteriorBaseChangeEquiv K (S.ϕ ω).Completion V (Module.finrank K V)).symm.toLinearMap
  have hp (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
      ∃ b : Basis (Fin (Module.finrank K V)) (S.ϕ ω).Completion
        ((S.ϕ ω).Completion ⊗[K] V),
        α ^ Module.finrank K V * (∏ i, ‖b i‖) ≤
          p (exteriorPower.ιMulti (S.ϕ ω).Completion (Module.finrank K V) b) := by
    obtain ⟨b, _, hb⟩ := exists_completed_basis_det_bound ξ ω hω hα hα1
    exact ⟨b, hb⟩
  have h := injective_freeDeterminantMap_tprod_le hk t b₀ c p hp
    (fun _ : Fin k ↦ exteriorPower.ιMulti (S.ϕ ω).Completion (Module.finrank K V) b₀) z
  rw [freeDeterminantMap_basis] at h
  change injectiveTensorSeminorm
    ((tensorBaseChangeEquiv K (S.ϕ ω).Completion (fun _ : Fin n ↦ V))
      ((tensorBaseChangeEquiv K (S.ϕ ω).Completion (fun _ : Fin n ↦ V)).symm _)) ≤ _
  rw [LinearEquiv.apply_symm_apply]
  convert h using 1
  simp only [p, Seminorm.comp_apply, LinearEquiv.coe_coe,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rfl

end Completed

end BostConjecture.Adelic.Contraction
