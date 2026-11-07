/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Degree.Basic

/-!
# Normalization of intrinsic determinant degree

In generic rank one, the canonical first-exterior-power isomorphism is an
isometry and determinant degree agrees with intrinsic line degree. In generic
rank zero, the integral empty wedge generates the determinant line and has
norm one, so the determinant degree vanishes.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct exteriorPower

namespace exteriorPower

/-- Transport an exterior power along equality of its degree. -/
def degreeCongr {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    {m n : ℕ} (h : m = n) : (⋀[R]^m V) ≃ₗ[R] (⋀[R]^n V) := by
  subst n
  exact LinearEquiv.refl R _

lemma degreeCongr_symm_ιMulti {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    {m n : ℕ} (h : m = n) (x : Fin n → V) :
    (degreeCongr (R := R) (V := V) h).symm (ιMulti R n x) =
      ιMulti R m (x ∘ Fin.cast h) := by
  subst n
  rfl

end exteriorPower

namespace BostConjecture.Arithmetic

variable {K : Type*} [Field K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]

/-- The canonical identification of the determinant of a rank-one module. -/
def determinantOneEquiv (hr : Module.finrank K (K ⊗[𝓞 K] M) = 1) :
    DeterminantLine (K := K) M ≃ₗ[𝓞 K] M :=
  (degreeCongr hr) ≪≫ₗ oneEquiv (𝓞 K) M

lemma determinantOneEquiv_symm (hr : Module.finrank K (K ⊗[𝓞 K] M) = 1) (x : M) :
    (determinantOneEquiv hr).symm x = ιMulti (𝓞 K) _ (fun _ => x) := by
  simp only [determinantOneEquiv, LinearEquiv.symm_trans_apply,
    oneEquiv_symm_apply, degreeCongr_symm_ιMulti]
  rfl

/-- The canonical identification of the determinant in generic rank zero. -/
def determinantZeroEquiv (hr : Module.finrank K (K ⊗[𝓞 K] M) = 0) :
    DeterminantLine (K := K) M ≃ₗ[𝓞 K] 𝓞 K :=
  (degreeCongr hr) ≪≫ₗ zeroEquiv (𝓞 K) M

lemma determinantZeroEquiv_symm_one (hr : Module.finrank K (K ⊗[𝓞 K] M) = 0) :
    (determinantZeroEquiv hr).symm 1 = ιMulti (𝓞 K) _ (fun _ => (0 : M)) := by
  simp only [determinantZeroEquiv, LinearEquiv.symm_trans_apply,
    zeroEquiv_symm_apply, one_smul, degreeCongr_symm_ιMulti]
  congr 1
  funext i
  exact (Fin.elim0 (Fin.cast hr i))

namespace HermitianMetric

variable [NumberField K] [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]

omit [NumberField K] [Module.Projective (𝓞 K) M] in
/-- The first-exterior-power isomorphism preserves every section norm. -/
lemma determinant_sectionNorm_rank_one (h : HermitianMetric K M)
    (hr : Module.finrank K (K ⊗[𝓞 K] M) = 1) (σ : K →+* ℂ) (x : M) :
    h.determinant.sectionNorm σ ((determinantOneEquiv hr).symm x) = h.sectionNorm σ x := by
  rw [determinantOneEquiv_symm]
  change Real.sqrt ((h.determinantFiber σ).inner _ _).re = _
  rw [h.determinantFiber_inner_wedge]
  have hd (a : ℂ) :
      (Matrix.of (fun (_ _ : Fin (Module.finrank K (K ⊗[𝓞 K] M))) => a)).det = a := by
    rw [hr]
    exact Matrix.det_unique _
  rw [hd]
  rfl

/-- Intrinsic determinant degree agrees with intrinsic line degree in rank one. -/
theorem degree_eq_lineDegree [Nontrivial M] (h : HermitianMetric K M)
    (hr : Module.finrank K (K ⊗[𝓞 K] M) = 1) : h.degree = h.lineDegree hr := by
  symm
  exact h.lineDegree_eq_of_equiv h.determinant (determinantOneEquiv hr).symm
    hr (determinant_generic_finrank M)
    (fun σ x => (h.determinant_sectionNorm_rank_one hr σ x).symm)

omit [NumberField K] [Module.Projective (𝓞 K) M] in
/-- The empty integral determinant wedge has norm one at every embedding. -/
lemma determinant_sectionNorm_rank_zero (h : HermitianMetric K M)
    (hr : Module.finrank K (K ⊗[𝓞 K] M) = 0) (σ : K →+* ℂ) :
    h.determinant.sectionNorm σ ((determinantZeroEquiv hr).symm 1) = 1 := by
  rw [determinantZeroEquiv_symm_one]
  change Real.sqrt ((h.determinantFiber σ).inner _ _).re = _
  rw [h.determinantFiber_inner_wedge]
  have hd (a : ℂ) :
      (Matrix.of (fun (_ _ : Fin (Module.finrank K (K ⊗[𝓞 K] M))) => a)).det = 1 := by
    rw [hr]
    exact Matrix.det_isEmpty
  rw [hd]
  simp

/-- The intrinsic determinant degree of a generic rank-zero module vanishes. -/
theorem degree_eq_zero_of_rank_zero (h : HermitianMetric K M)
    (hr : Module.finrank K (K ⊗[𝓞 K] M) = 0) : h.degree = 0 := by
  let e := determinantZeroEquiv (M := M) hr
  let ξ := e.symm 1
  have hξ : ξ ≠ 0 := e.symm.map_ne_zero_iff.mpr one_ne_zero
  have hs : (𝓞 K ∙ ξ) = ⊤ := by
    apply top_unique
    intro y _
    obtain ⟨a, rfl⟩ := e.symm.surjective y
    apply Submodule.mem_span_singleton.mpr
    exact ⟨a, by simp [ξ, ← map_smul]⟩
  have hq : Nat.card (DeterminantLine (K := K) M ⧸ (𝓞 K ∙ ξ)) = 1 := by
    rw [hs]
    exact Nat.card_unique
  rw [h.degree_eq hξ, hq]
  have hn (σ : K →+* ℂ) : h.determinant.sectionNorm σ ξ = 1 :=
    h.determinant_sectionNorm_rank_zero hr σ
  simp only [Nat.cast_one, Real.log_one, hn, Finset.sum_const_zero, sub_self, zero_div]

end HermitianMetric
end BostConjecture.Arithmetic
