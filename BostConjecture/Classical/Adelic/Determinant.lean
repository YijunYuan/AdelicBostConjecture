/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Classical.Adelic.Finite
public import BostConjecture.Classical.Degree
public import ArakelovGeometry.AdelicVectorBundle.Determinant.Universal
public import ArakelovGeometry.AdelicVectorBundle.NormFamily.Line

/-!
# Comparing determinant norms at finite places

Multilinear bounds on the completed unit lattice identify the adelic
determinant norm with the gauge of the original determinant lattice.
-/

@[expose] public section
noncomputable section

section MultilinearBounds

open NumberField TensorProduct IsDedekindDomain
open ArakelovGeometry ArakelovGeometry.AdelicStructure
  ArakelovGeometry.ActualPrimeIndexing ArakelovGeometry.NumberFieldFullLattice

namespace BostConjecture.Classical

/-- Multilinearity extends an integral-generator bound to the generated submodules. -/
theorem multilinear_mem_of_mem_span {R ι W : Type*} [CommRing R] [Finite ι]
    {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    [AddCommGroup W] [Module R W]
    (f : MultilinearMap R V W) (P : Submodule R W) (s : ∀ i, Set (V i))
    (hf : ∀ v : ∀ i, V i, (∀ i, v i ∈ s i) → f v ∈ P)
    (v : ∀ i, V i) (hv : ∀ i, v i ∈ Submodule.span R (s i)) : f v ∈ P := by
  classical
  let := Fintype.ofFinite ι
  have H (t : Finset ι) : ∀ v : ∀ i, V i,
      (∀ i ∈ t, v i ∈ Submodule.span R (s i)) →
      (∀ i ∉ t, v i ∈ s i) → f v ∈ P := by
    induction t using Finset.induction_on with
    | empty =>
      intro v _ hv
      exact hf v (fun i => hv i (Finset.notMem_empty i))
    | @insert i t hi ih =>
      intro v hv hs
      have hvi := hv i (Finset.mem_insert_self i t)
      have hu : ∀ x ∈ Submodule.span R (s i), f (Function.update v i x) ∈ P := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem x hx =>
          apply ih
          · intro j hj
            have hji : j ≠ i := by rintro rfl; exact hi hj
            rw [Function.update_of_ne hji]
            exact hv j (Finset.mem_insert_of_mem hj)
          · intro j hj
            by_cases hji : j = i
            · subst j
              simpa using hx
            · rw [Function.update_of_ne hji]
              exact hs j (by simp [hji, hj])
        | zero =>
          rw [f.map_coord_zero i (by simp)]
          exact P.zero_mem
        | add x y _ _ hx hy =>
          rw [f.map_update_add]
          exact P.add_mem hx hy
        | smul a x _ hx =>
          rw [f.map_update_smul]
          exact P.smul_mem a hx
      simpa only [Function.update_eq_self] using hu (v i) hvi
  exact H Finset.univ v (fun i _ => hv i) (by simp)

/-- If the input seminorms admit exact scalar normalization, the unit-ball
bound of a multilinear map gives its product bound. -/
theorem seminorm_multilinear_le_prod {F ι W : Type*} [NormedField F] [Fintype ι]
    {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module F (V i)]
    [AddCommGroup W] [Module F W]
    (q : Seminorm F W) (p : ∀ i, Seminorm F (V i)) (f : MultilinearMap F V W)
    (hscale : ∀ i (x : V i), x ≠ 0 →
      ∃ a : F, a ≠ 0 ∧ p i (a⁻¹ • x) ≤ 1 ∧ ‖a‖ = p i x)
    (hunit : ∀ v : ∀ i, V i, (∀ i, p i (v i) ≤ 1) → q (f v) ≤ 1)
    (v : ∀ i, V i) : q (f v) ≤ ∏ i, p i (v i) := by
  classical
  by_cases hz : ∃ i, v i = 0
  · obtain ⟨i, hi⟩ := hz
    rw [f.map_coord_zero i hi, map_zero]
    exact Finset.prod_nonneg (fun i _ => apply_nonneg (p i) _)
  · have hn (i : ι) : v i ≠ 0 := fun he => hz ⟨i, he⟩
    choose a ha hb hc using fun i => hscale i (v i) (hn i)
    have he : v = fun i => a i • ((a i)⁻¹ • v i) := by
      funext i
      rw [smul_smul, mul_inv_cancel₀ (ha i), one_smul]
    calc
      q (f v) = ‖∏ i, a i‖ * q (f (fun i => (a i)⁻¹ • v i)) := by
        conv_lhs => rw [he]
        rw [f.map_smul_univ, map_smul_eq_mul]
      _ ≤ ‖∏ i, a i‖ :=
        (mul_le_mul_of_nonneg_left (hunit _ hb) (norm_nonneg _)).trans_eq (mul_one _)
      _ = ∏ i, p i (v i) := by simp only [norm_prod, hc]

end BostConjecture.Classical

end MultilinearBounds

section DeterminantComparison

set_option backward.isDefEq.respectTransparency false

open NumberField TensorProduct IsDedekindDomain exteriorPower
open ArakelovGeometry ArakelovGeometry.AdelicStructure
  ArakelovGeometry.ActualPrimeIndexing ArakelovGeometry.NumberFieldFullLattice

namespace BostConjecture.Arithmetic
attribute [local instance 2000] Algebra.toModule Algebra.toSMul

variable {K M : Type*} [Field K] [NumberField K]
  [AddCommGroup M] [Module (𝓞 K) M] [Module.Finite (𝓞 K) M]

/-- Integral exterior powers commute with both scalar extensions. -/
def completedDeterminantEquiv (F : Type*) [Field F] [Algebra K F] :
    F ⊗[K] (K ⊗[𝓞 K] DeterminantLine (K := K) M) ≃ₗ[F]
      ⋀[F]^(Module.finrank K (K ⊗[𝓞 K] M)) (F ⊗[K] (K ⊗[𝓞 K] M)) :=
  LinearEquiv.baseChange K F _ _ (determinantGenericEquiv (K := K) M) ≪≫ₗ
    exteriorBaseChangeEquiv K F (K ⊗[𝓞 K] M) _

def completedIntegralWedge (F : Type*) [Field F] [Algebra K F] :
    (F ⊗[K] (K ⊗[𝓞 K] M)) [⋀^Fin (Module.finrank K (K ⊗[𝓞 K] M))]→ₗ[F]
      F ⊗[K] (K ⊗[𝓞 K] DeterminantLine (K := K) M) :=
  (completedDeterminantEquiv (K := K) (M := M) F).symm.toLinearMap.compAlternatingMap
    (ιMulti F _)

omit [NumberField K] [Module.Finite (𝓞 K) M] in
theorem completedIntegralWedge_section (F : Type*) [Field F] [Algebra K F]
    (x : Fin (Module.finrank K (K ⊗[𝓞 K] M)) → M) :
    completedIntegralWedge (K := K) (M := M) F
      (fun i => (1 : F) ⊗ₜ[K] ((1 : K) ⊗ₜ[𝓞 K] x i)) =
      (1 : F) ⊗ₜ[K] ((1 : K) ⊗ₜ[𝓞 K] (ιMulti (𝓞 K) _ x)) := by
  apply (completedDeterminantEquiv (K := K) (M := M) F).injective
  change (completedDeterminantEquiv (K := K) (M := M) F)
    ((completedDeterminantEquiv (K := K) (M := M) F).symm (ιMulti F _ _)) = _
  rw [LinearEquiv.apply_symm_apply]
  simp only [completedDeterminantEquiv, LinearEquiv.trans_apply,
    LinearEquiv.baseChange_tmul, determinantGenericEquiv,
    exteriorPower.baseChangeEquiv_apply_tmul, exteriorBaseChangeEquiv_tmul_ιMulti, one_smul]
  rfl

namespace HermitianMetric

/-- Wedges of finite unit vectors belong to the completed integral determinant. -/
theorem completedIntegralWedge_mem (h : HermitianMetric K M)
    (p : HeightOneSpectrum (𝓞 K))
    (x : Fin (Module.finrank K (K ⊗[𝓞 K] M)) → FiniteCompletion p ⊗[K] (K ⊗[𝓞 K] M))
    (hx : ∀ i, h.toAdelicBundle.norm (normalizedPrimeParameter p) (x i) ≤ 1) :
    completedIntegralWedge (K := K) (M := M) (FiniteCompletion p) x ∈
      NumberFieldModel.completedLatticeSpan
        (genericLattice (K := K) (DeterminantLine (K := K) M)) p := by
  let f := (completedIntegralWedge (K := K) (M := M) (FiniteCompletion p)).toMultilinearMap
  apply Classical.multilinear_mem_of_mem_span (R := FiniteIntegers p)
    (ι := Fin (Module.finrank K (K ⊗[𝓞 K] M)))
    (V := fun _ => FiniteCompletion p ⊗[K] (K ⊗[𝓞 K] M))
    (f.restrictScalars (FiniteIntegers p))
    (NumberFieldModel.completedLatticeSpan
      (genericLattice (K := K) (DeterminantLine (K := K) M)) p)
    (fun _ => Set.range fun v : genericLattice (K := K) M =>
      (1 : FiniteCompletion p) ⊗ₜ[K] (v : K ⊗[𝓞 K] M))
  · intro v hv
    choose y hy using hv
    choose m hm using fun i => (y i).property
    have he : v = fun i => (1 : FiniteCompletion p) ⊗ₜ[K] ((1 : K) ⊗ₜ[𝓞 K] m i) := by
      funext i
      rw [← hy i]
      change (1 : FiniteCompletion p) ⊗ₜ[K] (y i : K ⊗[𝓞 K] M) = _
      rw [← hm i]
      rfl
    change completedIntegralWedge (K := K) (M := M) (FiniteCompletion p) v ∈ _
    rw [he, completedIntegralWedge_section]
    exact Submodule.subset_span ⟨⟨_, ιMulti (𝓞 K) _ m, rfl⟩, rfl⟩
  · intro i
    exact (h.finite_norm_le_one_iff p (x i)).mp (hx i)

/-- The original determinant gauge satisfies Hadamard's bound at finite places. -/
theorem finite_norm_completedIntegralWedge_le (h : HermitianMetric K M)
    (p : HeightOneSpectrum (𝓞 K))
    (x : Fin (Module.finrank K (K ⊗[𝓞 K] M)) → FiniteCompletion p ⊗[K] (K ⊗[𝓞 K] M)) :
    h.determinant.adelicNormFamily.norm (normalizedPrimeParameter p)
      (completedIntegralWedge (K := K) (M := M) (FiniteCompletion p) x) ≤
      ∏ i, h.toAdelicBundle.norm (normalizedPrimeParameter p) (x i) := by
  apply Classical.seminorm_multilinear_le_prod (F := FiniteCompletion p)
    (ι := Fin (Module.finrank K (K ⊗[𝓞 K] M)))
    (V := fun _ => FiniteCompletion p ⊗[K] (K ⊗[𝓞 K] M))
    (h.determinant.adelicNormFamily.norm (normalizedPrimeParameter p))
    (fun _ => h.toAdelicBundle.norm (normalizedPrimeParameter p))
    (completedIntegralWedge (K := K) (M := M) (FiniteCompletion p)).toMultilinearMap
  · intro i z hz
    exact h.finite_norm_exists_scalar p z hz
  · intro v hv
    exact (h.determinant.finite_norm_le_one_iff p _).mpr (h.completedIntegralWedge_mem p v hv)

set_option maxHeartbeats 800000 in
-- Elaborating the two exterior-power scalar extensions is expensive.
/-- The adelic determinant seminorm is bounded on all integral determinant sections. -/
theorem finite_determinant_section_le_one (h : HermitianMetric K M)
    (p : HeightOneSpectrum (𝓞 K)) (ξ : DeterminantLine (K := K) M) :
    h.adelicNormFamily.determinant.norm (normalizedPrimeParameter p)
      (LinearEquiv.baseChange K (FiniteCompletion p) _ _ (determinantGenericEquiv (K := K) M)
        (1 ⊗ₜ[K] ((1 : K) ⊗ₜ[𝓞 K] ξ))) ≤ 1 := by
  classical
  let ω := normalizedPrimeParameter p
  let e := LinearEquiv.baseChange K (FiniteCompletion p) _ _
    (determinantGenericEquiv (K := K) M)
  let q := (h.adelicNormFamily.determinant.norm ω).comp e.toLinearMap
  have hq : ∀ x y, q (x + y) ≤ max (q x) (q y) := by
    intro x y
    change h.adelicNormFamily.determinant.norm ω (e (x + y)) ≤ _
    rw [map_add]
    exact h.adelicNormFamily.determinant.isUltrametricAtFinitePlaces_of_finrank_le_one
      NormFamily.determinant_finrank.le ω (normalizedPrimeParameter_mem_fin p) _ _
  change q (1 ⊗ₜ[K] ((1 : K) ⊗ₜ[𝓞 K] ξ)) ≤ 1
  have hξ : ξ ∈ Submodule.span (𝓞 K) (Set.range (ιMulti (𝓞 K)
      (Module.finrank K (K ⊗[𝓞 K] M)) (M := M))) := by
    rw [ιMulti_span]; trivial
  induction hξ using Submodule.span_induction with
  | mem ξ hξ =>
    obtain ⟨v, rfl⟩ := hξ
    have hb := h.adelicNormFamily.determinant_norm_ιMulti_le ω
      (fun i => (1 : FiniteCompletion p) ⊗ₜ[K] ((1 : K) ⊗ₜ[𝓞 K] v i))
    have he : (exteriorBaseChangeEquiv K (FiniteCompletion p) (K ⊗[𝓞 K] M) _).symm
        (ιMulti (FiniteCompletion p) _
          (fun i => (1 : FiniteCompletion p) ⊗ₜ[K] ((1 : K) ⊗ₜ[𝓞 K] v i))) =
        e (1 ⊗ₜ[K] ((1 : K) ⊗ₜ[𝓞 K] ιMulti (𝓞 K) _ v)) := by
      simp only [e, LinearEquiv.baseChange_tmul, determinantGenericEquiv,
        exteriorPower.baseChangeEquiv_apply_tmul, exteriorBaseChangeEquiv_symm_ιMulti_tmul,
        Finset.prod_const_one]
      rfl
    rw [he] at hb
    exact hb.trans ((Finset.prod_le_prod₀
      (fun i _ => h.adelicNormFamily.norm_nonneg ω _)
      (fun i _ => h.finite_norm_section_le_one p (v i))).trans_eq (by simp))
  | zero =>
    rw [tmul_zero, tmul_zero]
    exact (map_zero q).le.trans zero_le_one
  | add x y _ _ hx hy =>
    simpa only [tmul_add] using (hq (1 ⊗ₜ[K] ((1 : K) ⊗ₜ[𝓞 K] x))
      (1 ⊗ₜ[K] ((1 : K) ⊗ₜ[𝓞 K] y))).trans (max_le hx hy)
  | smul a x _ hx =>
    let c := (normalizedNumberFieldAdelicStructure K).integralCompletedLocalCoefficientMap
      ω (normalizedPrimeParameter_mem_fin p) a
    have hc : ‖(c : FiniteCompletion p)‖ ≤ 1 :=
      ((normalizedNumberFieldAdelicStructure K).mem_completedLocalRing _ _ _).mp c.property
    have he : (1 : FiniteCompletion p) ⊗ₜ[K] ((1 : K) ⊗ₜ[𝓞 K] (a • x)) =
        (c : FiniteCompletion p) • (1 ⊗ₜ[K] ((1 : K) ⊗ₜ[𝓞 K] x)) := by
      change _ = (algebraMap K (FiniteCompletion p) (algebraMap (𝓞 K) K a)) • _
      rw [IsScalarTower.algebraMap_smul, ← tmul_smul]
      congr 1
      rw [tmul_smul, smul_tmul']
      simp only [Algebra.smul_def, smul_tmul', mul_one, Algebra.algebraMap_self, RingHom.id_apply]
    rw [he, map_smul_eq_mul]
    exact (mul_le_mul hc hx (apply_nonneg q _) zero_le_one).trans_eq (mul_one _)

set_option maxHeartbeats 800000 in
-- Elaborating the two exterior-power scalar extensions is expensive.
/-- Both constructions give the same completed determinant norm at finite places. -/
theorem finite_norm_determinant (h : HermitianMetric K M)
    (p : HeightOneSpectrum (𝓞 K))
    (z : FiniteCompletion p ⊗[K] (K ⊗[𝓞 K] DeterminantLine (K := K) M)) :
    h.adelicNormFamily.determinant.norm (normalizedPrimeParameter p)
      (LinearEquiv.baseChange K (FiniteCompletion p) _ _ (determinantGenericEquiv (K := K) M) z) =
      h.determinant.adelicNormFamily.norm (normalizedPrimeParameter p) z := by
  classical
  let ω := normalizedPrimeParameter p
  let e := LinearEquiv.baseChange K (FiniteCompletion p) _ _
    (determinantGenericEquiv (K := K) M)
  let q := (h.adelicNormFamily.determinant.norm ω).comp e.toLinearMap
  have hq : ∀ x y, q (x + y) ≤ max (q x) (q y) := by
    intro x y
    change h.adelicNormFamily.determinant.norm ω (e (x + y)) ≤ _
    rw [map_add]
    exact h.adelicNormFamily.determinant.isUltrametricAtFinitePlaces_of_finrank_le_one
      NormFamily.determinant_finrank.le ω (normalizedPrimeParameter_mem_fin p) _ _
  apply le_antisymm
  · have hb := seminorm_le_completedGauge
      (genericLattice (K := K) (DeterminantLine (K := K) M))
      (genericLattice_fg (K := K) _) (genericLattice_span (K := K) _) p q hq
      (by rintro ⟨_, ξ, rfl⟩; exact h.finite_determinant_section_le_one p ξ) z
    change q z ≤ h.determinant.adelicNormFamily.norm _ _
    rw [adelicNormFamily, fullLatticeGaugeFamily_norm_prime]
    exact hb
  · let q' := (h.determinant.adelicNormFamily.norm ω).comp e.symm.toLinearMap
    have hb := h.adelicNormFamily.seminorm_le_determinant_of_ιMulti_le ω q'
      (fun x => h.finite_norm_completedIntegralWedge_le p x) (e z)
    change h.determinant.adelicNormFamily.norm ω (e.symm (e z)) ≤
      h.adelicNormFamily.determinant.norm ω (e z) at hb
    rw [LinearEquiv.symm_apply_apply] at hb
    simpa only [e, ω] using hb

end HermitianMetric
end BostConjecture.Arithmetic

end DeterminantComparison
