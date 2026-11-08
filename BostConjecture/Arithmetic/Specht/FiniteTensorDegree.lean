/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Degree.Tensor
public import BostConjecture.Arithmetic.Representation.IndependentPiSemistable

/-!
# Average slopes of finite Hilbert tensor products

Binary degree additivity extends to finite Hilbert tensor products.
These are average-slope identities and do not assume tensor semistability.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct PiTensorProduct

namespace BostConjecture.Arithmetic.Specht

open scoped HermitianMetric

universe u

variable {K : Type u} [Field K] [NumberField K]

omit [NumberField K] in
/-- The generic rank of the actual finite tensor module is the product of the ranks. -/
lemma piTensor_generic_finrank {ι : Type} [Fintype ι] (M : ι → Type u)
    [∀ i, AddCommGroup (M i)] [∀ i, Module (𝓞 K) (M i)]
    [∀ i, Module.Finite (𝓞 K) (M i)] :
    Module.finrank K (K ⊗[𝓞 K] (⨂[𝓞 K] i, M i)) =
      ∏ i, Module.finrank K (K ⊗[𝓞 K] M i) := by
  classical
  rw [(Tensor.baseChangeEquiv (𝓞 K) K M).finrank_eq]
  rw [Module.finrank_eq_card_basis
    (Basis.piTensorProduct (fun i => Module.finBasis K (K ⊗[𝓞 K] M i)))]
  simp only [Fintype.card_pi, Fintype.card_fin]

/-- Separating the final factor preserves the entire arithmetic fiber form. -/
lemma piTensor_option_inner {ι : Type} [Fintype ι] (M : Option ι → Type u)
    [∀ i, AddCommGroup (M i)] [∀ i, Module (𝓞 K) (M i)]
    (h : ∀ i, HermitianMetric K (M i)) (σ : K →+* ℂ)
    (x y : ComplexFiber (⨂[𝓞 K] i, M i) σ) :
    (((HermitianMetric.piTensor (fun i => h (some i))) ⊗[𝓞 K] (h none)).fiber σ).inner
      (fiberMap (Tensor.optionEquiv (𝓞 K) M).toLinearMap σ x)
      (fiberMap (Tensor.optionEquiv (𝓞 K) M).toLinearMap σ y) =
        ((HermitianMetric.piTensor h).fiber σ).inner x y := by
  apply Tensor.inner_ext_of_span (fun z : ∀ i, M i => fiberSection _ σ (tprod (𝓞 K) z))
    (span_fiberSection_piTensor σ) _ _
    (fiberMap (Tensor.optionEquiv (𝓞 K) M).toLinearMap σ) LinearMap.id _ x y
  intro z w
  simp only [fiberMap_section, LinearEquiv.coe_coe, Tensor.optionEquiv_tprod,
    LinearMap.id_apply, HermitianMetric.tensor_inner_section]
  change (HermitianMetric.tensorFiber (fun i => h (some i)) σ).inner _ _ * _ =
    (HermitianMetric.tensorFiber h σ).inner _ _
  simp only [HermitianMetric.tensorFiber_inner_tprod, Fintype.prod_option, mul_comm]

omit [NumberField K] in
/-- Reindexing preserves the entire arithmetic tensor form. -/
lemma piTensor_reindex_inner {ι κ : Type} [Fintype ι] [Fintype κ]
    (M : κ → Type u) [∀ i, AddCommGroup (M i)] [∀ i, Module (𝓞 K) (M i)]
    (h : ∀ i, HermitianMetric K (M i)) (e : ι ≃ κ) (σ : K →+* ℂ)
    (x y : ComplexFiber (⨂[𝓞 K] i, M i) σ) :
    ((HermitianMetric.piTensor (fun i => h (e i))).fiber σ).inner
      (fiberMap (reindex (𝓞 K) M e.symm).toLinearMap σ x)
      (fiberMap (reindex (𝓞 K) M e.symm).toLinearMap σ y) =
        ((HermitianMetric.piTensor h).fiber σ).inner x y := by
  apply Tensor.inner_ext_of_span (fun z : ∀ i, M i => fiberSection _ σ (tprod (𝓞 K) z))
    (span_fiberSection_piTensor σ) _ _
    (fiberMap (reindex (𝓞 K) M e.symm).toLinearMap σ) LinearMap.id _ x y
  intro z w
  simp only [fiberMap_section, LinearEquiv.coe_coe, reindex_tprod, LinearMap.id_apply]
  change (HermitianMetric.tensorFiber (fun i => h (e i)) σ).inner _ _ =
    (HermitianMetric.tensorFiber h σ).inner _ _
  simp only [HermitianMetric.tensorFiber_inner_tprod]
  exact Equiv.prod_comp e (fun i => ((h i).fiber σ).inner
    (fiberSection (M i) σ (z i)) (fiberSection (M i) σ (w i)))

/-- The empty tensor is the degree-zero unit Hermitian line. -/
lemma degree_piTensor_empty {ι : Type} [Fintype ι] [IsEmpty ι]
    (M : ι → Type u) [∀ i, AddCommGroup (M i)] [∀ i, Module (𝓞 K) (M i)]
    [∀ i, Module.Finite (𝓞 K) (M i)] [∀ i, Module.Projective (𝓞 K) (M i)]
    (h : ∀ i, HermitianMetric K (M i)) :
    (HermitianMetric.piTensor h).degree = 0 := by
  classical
  let e := isEmptyEquiv ι (R := 𝓞 K) (s := M)
  let ξ := tprod (𝓞 K) (fun i => (0 : M i))
  have he : e ξ = 1 := isEmptyEquiv_apply_tprod ι _
  have hn : ξ ≠ 0 := by
    intro hh
    simp [hh] at he
  let : Nontrivial (⨂[𝓞 K] i, M i) := e.symm.injective.nontrivial
  have hr : Module.finrank K (K ⊗[𝓞 K] (⨂[𝓞 K] i, M i)) = 1 := by
    simp [piTensor_generic_finrank]
  have hs : (𝓞 K ∙ ξ) = ⊤ := by
    apply top_unique
    intro y _
    refine Submodule.mem_span_singleton.mpr ⟨e y, ?_⟩
    apply e.injective
    simp only [map_smul, he, smul_eq_mul, mul_one]
  rw [(HermitianMetric.piTensor h).degree_eq_lineDegree hr,
    (HermitianMetric.piTensor h).lineDegree_eq_sum_embeddings hr hn, hs]
  simp [ξ, HermitianMetric.sectionNorm_piTensor_tprod]

/-- Average slope is additive for the actual finite Hilbert tensor product. -/
theorem slope_piTensor {ι : Type} [Fintype ι] (M : ι → Type u)
    [∀ i, AddCommGroup (M i)] [∀ i, Module (𝓞 K) (M i)]
    [∀ i, Module.Finite (𝓞 K) (M i)] [∀ i, Module.Projective (𝓞 K) (M i)]
    (h : ∀ i, HermitianMetric K (M i))
    (hr : ∀ i, 0 < Module.finrank K (K ⊗[𝓞 K] M i)) :
    (HermitianMetric.piTensor h).slope = ∑ i, (h i).slope := by
  classical
  revert M
  refine Fintype.induction_empty_option (P := fun ι _ =>
    ∀ (M : ι → Type u) [∀ i, AddCommGroup (M i)] [∀ i, Module (𝓞 K) (M i)]
      [∀ i, Module.Finite (𝓞 K) (M i)] [∀ i, Module.Projective (𝓞 K) (M i)]
      (h : ∀ i, HermitianMetric K (M i)),
      (∀ i, 0 < Module.finrank K (K ⊗[𝓞 K] M i)) →
      (HermitianMetric.piTensor h).slope = ∑ i, (h i).slope) ?_ ?_ ?_ ι
  · intro α β _ e ih M _ _ _ _ h hr
    let : Fintype α := Fintype.ofEquiv β e.symm
    let f := reindex (𝓞 K) M e.symm
    have hd := HermitianMetric.degree_eq_of_equiv (HermitianMetric.piTensor h)
      (HermitianMetric.piTensor (fun i => h (e i))) f (piTensor_reindex_inner M h e)
    calc
      (HermitianMetric.piTensor h).slope =
          (HermitianMetric.piTensor (fun i => h (e i))).slope := by
        unfold HermitianMetric.slope
        rw [hd, (f.baseChange (𝓞 K) K).finrank_eq]
        rfl
      _ = ∑ i, (h (e i)).slope := ih (fun i => M (e i)) (fun i => h (e i)) (fun i => hr (e i))
      _ = ∑ i, (h i).slope := Equiv.sum_comp e (fun i => (h i).slope)
  · intro M _ _ _ _ h hr
    simp [HermitianMetric.slope, degree_piTensor_empty]
  · intro α _ ih M _ _ _ _ h hr
    let f := Tensor.optionEquiv (𝓞 K) M
    have hd := HermitianMetric.degree_eq_of_equiv (HermitianMetric.piTensor h)
      ((HermitianMetric.piTensor (fun i => h (some i))) ⊗[𝓞 K] (h none)) f
      (piTensor_option_inner M h)
    have hp : 0 < Module.finrank K (K ⊗[𝓞 K] (⨂[𝓞 K] i : α, M (some i))) := by
      rw [piTensor_generic_finrank]
      exact Finset.prod_pos (fun i _ => hr (some i))
    calc
      (HermitianMetric.piTensor h).slope =
          ((HermitianMetric.piTensor (fun i => h (some i))) ⊗[𝓞 K] (h none)).slope := by
        unfold HermitianMetric.slope
        rw [hd, (f.baseChange (𝓞 K) K).finrank_eq]
      _ = (HermitianMetric.piTensor (fun i => h (some i))).slope + (h none).slope :=
        HermitianMetric.slope_tensor _ _ hp (hr none)
      _ = ∑ i, (h i).slope := by
        rw [ih (fun i => M (some i)) (fun i => h (some i)) (fun i => hr (some i))]
        simp only [Fintype.sum_option, add_comm]

variable {M : Type u} [AddCommGroup M] [Module (𝓞 K) M]
  [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]

/-- Taking the intrinsic determinant line preserves the defining determinant degree. -/
lemma determinant_degree (h : HermitianMetric K M) :
    h.determinant.degree = h.degree :=
  h.determinant.degree_eq_lineDegree (determinant_generic_finrank M)

/-- The actual finite tensor power of the determinant line has the expected slope. -/
lemma determinant_piTensor_slope (h : HermitianMetric K M) (k : ℕ) :
    (HermitianMetric.piTensor (fun _ : Fin k => h.determinant)).slope =
      (k : ℝ) * h.degree := by
  rw [slope_piTensor _ _ (fun _ => by rw [determinant_generic_finrank]; exact Nat.zero_lt_one)]
  simp [HermitianMetric.slope, determinant_generic_finrank, determinant_degree]

/-- The same formula gives the degree since a determinant tensor power has rank one. -/
lemma determinant_piTensor_degree (h : HermitianMetric K M) (k : ℕ) :
    (HermitianMetric.piTensor (fun _ : Fin k => h.determinant)).degree =
      (k : ℝ) * h.degree := by
  have hr : Module.finrank K
      (K ⊗[𝓞 K] (⨂[𝓞 K] (_ : Fin k), DeterminantLine (K := K) M)) = 1 := by
    simp [piTensor_generic_finrank, determinant_generic_finrank]
  simpa only [HermitianMetric.slope, hr, Nat.cast_one, div_one] using
    determinant_piTensor_slope h k

end BostConjecture.Arithmetic.Specht
