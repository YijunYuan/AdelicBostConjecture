/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Exterior.PluckerBaseChange
public import BostConjecture.Arithmetic.Line.Minkowski
public import BostConjecture.Arithmetic.Degree.ArchimedeanFiniteness
public import BostConjecture.Arithmetic.Submodule.SubspaceDegree

/-!
# Finiteness of saturated submodules of bounded degree below

Minkowski supplies a uniformly bounded nonzero determinant section. Its image
in the fixed ambient exterior module determines the generic subspace by
Plücker recovery; saturation then determines the integral submodule.
-/

@[expose] public section

noncomputable section

open NumberField exteriorPower Module
open scoped TensorProduct

namespace BostConjecture.Arithmetic.HermitianMetric

variable {K : Type*} [Field K] [NumberField K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]
variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]

/-- A generic subspace has a nonzero bounded integral Plücker section in the
fixed ambient exterior module, with bound controlled by its intrinsic degree. -/
theorem exists_small_exterior_section (h : HermitianMetric (K := K) M)
    (X : Submodule K (K ⊗[𝓞 K] M)) {r : ℕ} (hr : finrank K X = r) :
    ∃ ξ : ⋀[𝓞 K]^r M, ξ ≠ 0 ∧
      (∀ σ : K →+* ℂ, (h.exterior r).sectionNorm σ ξ <
        lineMinkowskiConstant K * Real.exp (-h.subspaceDegree X)) ∧
      exteriorPower.baseChangeEquiv (𝓞 K) M K r (1 ⊗ₜ[𝓞 K] ξ) ∈
        (map (M := X) r X.subtype).range := by
  have hR : finrank K (K ⊗[𝓞 K] integralPart X) = r :=
    (integralPart_generic_finrank X).trans hr
  rw [← hR]
  obtain ⟨η, hη, hbound⟩ := (h.submodule (integralPart X)).determinant.exists_small_section
    (determinant_generic_finrank (integralPart X))
  refine ⟨map _ (integralPart X).subtype η, ?_, ?_, ?_⟩
  · simpa only [map_zero] using
      (exteriorMap_injective (integralPart X).subtype (integralPart X).injective_subtype _).ne hη
  · intro σ
    rw [h.determinant_submodule_sectionNorm]
    exact hbound σ
  · exact ⟨map (N := X) _ (integralPartGenericEquiv X).toLinearMap
      (exteriorPower.baseChangeEquiv (𝓞 K) (integralPart X) K _ (1 ⊗ₜ[𝓞 K] η)),
      integralPart_exterior_section X _ η⟩

/-- The actual intrinsic subspace degree has finite superlevel sets in every
fixed rank. No degree finiteness assumption enters the statement. -/
theorem finite_subspaces_degree_ge (h : HermitianMetric (K := K) M) (r : ℕ) (c : ℝ) :
    {X : Submodule K (K ⊗[𝓞 K] M) | finrank K X = r ∧ c ≤ h.subspaceDegree X}.Finite := by
  classical
  let S := {X : Submodule K (K ⊗[𝓞 K] M) | finrank K X = r ∧ c ≤ h.subspaceDegree X}
  let T := {ξ : ⋀[𝓞 K]^r M | ∀ σ : K →+* ℂ,
    (h.exterior r).sectionNorm σ ξ ≤ lineMinkowskiConstant K * Real.exp (-c)}
  have hT : T.Finite := (h.exterior r).finite_bounded_sections _
  choose ξ hξ0 hξb hξrange using fun X : S => h.exists_small_exterior_section X.val X.property.1
  have hb (X : S) : ξ X ∈ T := by
    intro σ
    exact (hξb X σ).le.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (neg_le_neg X.property.2)) lineMinkowskiConstant_pos.le)
  let F : S → T := fun X => ⟨ξ X, hb X⟩
  have hF : Function.Injective F := by
    intro X Y he
    have hxy : ξ X = ξ Y := congrArg Subtype.val he
    apply Subtype.ext
    have hnonzero : exteriorPower.baseChangeEquiv (𝓞 K) M K r
        (1 ⊗ₜ[𝓞 K] ξ X) ≠ 0 := by
      apply (exteriorPower.baseChangeEquiv (𝓞 K) M K r).map_ne_zero_iff.mpr
      intro hz
      apply hξ0 X
      apply Module.Flat.tensorProduct_mk_injective (𝓞 K) (⋀[𝓞 K]^r M) K
      change (1 : K) ⊗ₜ[𝓞 K] ξ X = (1 : K) ⊗ₜ[𝓞 K] 0
      simpa only [TensorProduct.tmul_zero] using hz
    apply eq_of_mem_exterior_ranges X.val Y.val X.property.1 Y.property.1
      hnonzero (hξrange X)
    rw [hxy]
    exact hξrange Y
  let : Fintype T := hT.fintype
  let : Finite S := Finite.of_injective F hF
  exact Set.toFinite S

/-- Finiteness holds across all ranks, since the ambient generic dimension is finite. -/
theorem finite_subspaces_degree_ge_all (h : HermitianMetric (K := K) M) (c : ℝ) :
    {X : Submodule K (K ⊗[𝓞 K] M) | c ≤ h.subspaceDegree X}.Finite := by
  have hf := Set.finite_iUnion (fun r : Fin (finrank K (K ⊗[𝓞 K] M) + 1) =>
    h.finite_subspaces_degree_ge r.val c)
  apply hf.subset
  intro X hX
  exact Set.mem_iUnion.mpr ⟨⟨finrank K X, Nat.lt_succ_of_le X.finrank_le⟩, rfl, hX⟩

/-- Saturated integral submodules of a fixed Hermitian bundle with degree
bounded below form a finite set, with no integral freeness assumption. -/
theorem finite_saturated_submodules_degree_ge (h : HermitianMetric (K := K) M) (c : ℝ) :
    {P : Submodule (𝓞 K) M | Module.IsTorsionFree (𝓞 K) (M ⧸ P) ∧
      c ≤ (h.submodule P).degree}.Finite := by
  apply Set.Finite.of_injOn (f := fun P : Submodule (𝓞 K) M => P.baseChange K)
    (t := {X : Submodule K (K ⊗[𝓞 K] M) | c ≤ h.subspaceDegree X})
    ?_ ?_ (h.finite_subspaces_degree_ge_all c)
  · intro P hP
    let : Module.IsTorsionFree (𝓞 K) (M ⧸ P) := hP.1
    change c ≤ h.subspaceDegree (P.baseChange K)
    have he := congrArg (fun Q : Submodule (𝓞 K) M => (h.submodule Q).degree)
      (integralPart_baseChange P)
    exact hP.2.trans_eq he.symm
  · intro P hP Q hQ hPQ
    let : Module.IsTorsionFree (𝓞 K) (M ⧸ P) := hP.1
    let : Module.IsTorsionFree (𝓞 K) (M ⧸ Q) := hQ.1
    simpa only [integralPart_baseChange] using congrArg integralPart hPQ

end BostConjecture.Arithmetic.HermitianMetric
