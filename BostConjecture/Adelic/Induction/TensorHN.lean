/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Adelic.Induction.GradeEquality
public import ArakelovGeometry.AdelicVectorBundle.Tensor.Graded.Degree
public import ArakelovGeometry.AdelicVectorBundle.Examples.Trivial.Filtration.HN.Lift
public import BostConjecture.Adelic.Induction.HNContraction
public import ArakelovGeometry.AdelicVectorBundle.Slope.Tensor
public import ArakelovGeometry.AdelicVectorBundle.Slope.Quotient
public import ArakelovGeometry.AdelicVectorBundle.Degree.TensorHermitian

/-!
# Identification of the tensor Harder--Narasimhan filtration

This paper, Lemma 7.1. The canonical component maps into each tensor grade
are completed contractions. HN functoriality and spanning force the target
HN threshold to be the whole grade. Equality of total degrees makes each bound sharp, so
HN uniqueness identifies the weighted tensor filtration. No norm on a direct
sum of the components is needed. Zero factors and zero grades are included.
-/

@[expose] public section

open Module Submodule
open scoped TensorProduct BigOperators

namespace Submodule

variable {K E F : Type*} [Field K]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]

/-- The finite family of canonical pair maps spans a tensor grade, retaining
all pairs with coincident total weight. -/
theorem iSup_range_tensorFiltrationGradedPair
    {ι κ : Type*} [Finite ι] [Finite κ]
    (b : Basis ι K E) (c : Basis κ K F) (w : ι → ℝ) (z : κ → ℝ)
    {P : ℝ → Submodule K E} {R : ℝ → Submodule K F}
    (hP : Antitone P) (hR : Antitone R)
    (hPw : ∀ t, P t = span K (b '' {i | t ≤ w i}))
    (hRz : ∀ u, R u = span K (c '' {j | u ≤ z j})) (γ : ℝ) :
    (⨆ p : {ij : ι × κ // w ij.1 + z ij.2 = γ},
      (tensorFiltrationGradedPair hP hR p.property).range) = ⊤ := by
  have h := iSup_range_tensorFiltrationGradedQuotientPair b c w z
    (LinearMap.id : E ⊗[K] F →ₗ[K] E ⊗[K] F) hP hR hPw hRz γ
  have transport (G : ℝ → Submodule K (E ⊗[K] F))
      (hG : G = tensorFiltration P R)
      (hg : ∀ s, tensorFiltration P R s ≤ (G s).comap LinearMap.id)
      (hs : (⨆ p : {ij : ι × κ // w ij.1 + z ij.2 = γ},
        ((filtrationGradedMap LinearMap.id hg γ).comp
          (tensorFiltrationGradedPair hP hR p.property)).range) = ⊤) :
      (⨆ p : {ij : ι × κ // w ij.1 + z ij.2 = γ},
        (tensorFiltrationGradedPair hP hR p.property).range) = ⊤ := by
    subst G
    simpa only [filtrationGradedMap_id, LinearMap.id_comp] using hs
  exact transport _ (funext fun s ↦ map_id _) _ h

end Submodule

namespace ArakelovGeometry.AdelicVectorBundle

universe u v w

variable {K : Type u} {E : Type w} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E] {S : AdelicStructure.{u, v} K} [S.IsProper]

/-- An actual Hermitian HN filtration admits a weighted basis, also in rank zero. -/
theorem exists_weighted_basis_hermitianHNFiltration
    (V : AdelicVectorBundle S E)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.toNormFamily.IsHermitian hN) :
    ∃ (b : Basis (Fin (finrank K E)) K E) (w : Fin (finrank K E) → ℝ),
      ∀ t, V.hermitianHNFiltration hS hN hV t = span K (b '' {i | t ≤ w i}) := by
  have ha := V.hermitianHNFiltration_antitone hS hN hV
  obtain ⟨a, ha'⟩ := V.hermitianHNFiltration_separated hS hN hV
  obtain ⟨b, hb'⟩ := V.hermitianHNFiltration_exhaustive hS hN hV
  have hbot : ∃ t, V.hermitianHNFiltration hS hN hV t = ⊥ :=
    ⟨a + 1, ha' _ (by linarith)⟩
  have htop : ∃ t, V.hermitianHNFiltration hS hN hV t = ⊤ := ⟨b, hb' _ le_rfl⟩
  have hleft (t : ℝ) : ∃ ε > 0, ∀ s, t - ε < s → s ≤ t →
      V.hermitianHNFiltration hS hN hV s = V.hermitianHNFiltration hS hN hV t := by
    obtain ⟨δ, hδ, hd⟩ := V.hermitianHNFiltration_locallyConstantLeft hS hN hV t
    refine ⟨δ, hδ, fun s hs hst ↦ ?_⟩
    simpa using hd (t - s) (by linarith) (by linarith)
  obtain ⟨b, w, _, hw, _⟩ := exists_common_weighted_basis
    ha hbot htop hleft ha hbot htop hleft
  exact ⟨b, w, hw⟩

variable {F : Type w} [AddCommGroup F] [Module K F] [FiniteDimensional K F]
  (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F)
  (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
  (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
  (hV : V.toNormFamily.IsHermitian hN) (hW : W.toNormFamily.IsHermitian hN)

/-- The weighted degree of the tensor of the two HN filtrations equals the
degree of the actual orthogonal tensor bundle, including zero ranks. -/
theorem finsum_tensor_hermitianHNFiltration_eq_degree :
    (∑ᶠ t : ℝ, t * (finrank K (FiltrationGraded
      (tensorFiltration (V.hermitianHNFiltration hS hN hV)
        (W.hermitianHNFiltration hS hN hW)) t) : ℝ)) =
      (V.orthogonalTensorPair W hS hN hV hW).degree hS hN := by
  obtain ⟨b, w, hb⟩ := V.exists_weighted_basis_hermitianHNFiltration hS hN hV
  obtain ⟨c, z, hc⟩ := W.exists_weighted_basis_hermitianHNFiltration hS hN hW
  have hVdeg : (∑ i, w i) = V.degree hS hN :=
    (finsum_weight_mul_finrank_filtrationGraded b w hb).symm.trans
      (V.finsum_hermitianHNFiltration_eq_degree hS hN hV)
  have hWdeg : (∑ j, z j) = W.degree hS hN :=
    (finsum_weight_mul_finrank_filtrationGraded c z hc).symm.trans
      (W.finsum_hermitianHNFiltration_eq_degree hS hN hW)
  rw [finsum_weight_mul_finrank_filtrationGraded (b.tensorProduct c)
    (fun p ↦ w p.1 + z p.2) (tensorFiltration_eq_span_tensorProduct b c w z hb hc),
    V.degree_orthogonalTensorPair W hS hN hV hW]
  simp only [Fintype.sum_prod_type, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum,
    hVdeg, hWdeg]

/-- This paper, Lemma 7.1: semistability of nonzero products of HN grades
identifies the tensor filtration with the actual HN filtration. -/
theorem hermitianHNFiltration_orthogonalTensorPair_of_semistable_grades
    (hsemi : ∀ t u,
      0 < finrank K (FiltrationGraded (V.hermitianHNFiltration hS hN hV) t) →
      0 < finrank K (FiltrationGraded (W.hermitianHNFiltration hS hN hW) u) →
      (tensorFiltrationGradedSource V W hS hN hV hW
        (V.hermitianHNFiltration hS hN hV)
        (W.hermitianHNFiltration hS hN hW) t u).IsMeanSlopeSemistable hS hN) :
    (V.orthogonalTensorPair W hS hN hV hW).hermitianHNFiltration hS hN
      (orthogonalTensorPair_isHermitian V W hS hN hV hW) =
        tensorFiltration (V.hermitianHNFiltration hS hN hV)
          (W.hermitianHNFiltration hS hN hW) := by
  let P := V.hermitianHNFiltration hS hN hV
  let R := W.hermitianHNFiltration hS hN hW
  let T := V.orthogonalTensorPair W hS hN hV hW
  have hT := orthogonalTensorPair_isHermitian V W hS hN hV hW
  have hP : Antitone P := V.hermitianHNFiltration_antitone hS hN hV
  have hR : Antitone R := W.hermitianHNFiltration_antitone hS hN hW
  obtain ⟨b, w, hb⟩ := V.exists_weighted_basis_hermitianHNFiltration hS hN hV
  obtain ⟨c, z, hc⟩ := W.exists_weighted_basis_hermitianHNFiltration hS hN hW
  have hs (t u : ℝ) : finrank K (FiltrationGraded P t ⊗[K] FiltrationGraded R u) = 0 ∨
      (tensorFiltrationGradedSource V W hS hN hV hW P R t u).IsMeanSlopeSemistable hS hN ∧
      (tensorFiltrationGradedSource V W hS hN hV hW P R t u).slope hS hN = t + u := by
    by_cases ht : finrank K (FiltrationGraded P t) = 0
    · exact Or.inl (by rw [finrank_tensorProduct, ht, zero_mul])
    by_cases hu : finrank K (FiltrationGraded R u) = 0
    · exact Or.inl (by rw [finrank_tensorProduct, hu, mul_zero])
    have htp := Nat.pos_of_ne_zero ht
    have hup := Nat.pos_of_ne_zero hu
    refine Or.inr ⟨hsemi t u htp hup, ?_⟩
    have hts :=
      (filtrationGraded_hermitianHN_zero_or_semistable V hS hN hV t).resolve_left ht
    have hus :=
      (filtrationGraded_hermitianHN_zero_or_semistable W hS hN hW u).resolve_left hu
    exact ((V.filtrationGraded P t hS).slope_orthogonalTensorPair
      (W.filtrationGraded R u hS) hS hN (hV.filtrationGraded P t)
      (hW.filtrationGraded R u) htp hup).trans (congrArg₂ (· + ·) hts.2 hus.2)
  let C (γ : ℝ) (p : {ij : Fin (finrank K E) × Fin (finrank K F) //
      w ij.1 + z ij.2 = γ}) :=
    tensorFiltrationGradedSource V W hS hN hV hW P R (w p.val.1) (z p.val.2)
  let f (γ : ℝ) (p : {ij : Fin (finrank K E) × Fin (finrank K F) //
      w ij.1 + z ij.2 = γ}) := tensorFiltrationGradedPair hP hR p.property
  have hC (γ : ℝ) (p) : (C γ p).toNormFamily.IsHermitian hN :=
    tensorFiltrationGradedSource_isHermitian V W hS hN hV hW P R _ _
  have hCs (γ : ℝ) (p : {ij : Fin (finrank K E) × Fin (finrank K F) //
      w ij.1 + z ij.2 = γ}) : finrank K
      (FiltrationGraded P (w p.val.1) ⊗[K] FiltrationGraded R (z p.val.2)) = 0 ∨
      (C γ p).IsMeanSlopeSemistable hS hN ∧ (C γ p).slope hS hN = γ := by
    simpa only [C, p.property] using hs (w p.val.1) (z p.val.2)
  have hspan (γ : ℝ) : (⨆ p, (f γ p).range) = ⊤ :=
    iSup_range_tensorFiltrationGradedPair b c w z hP hR hb hc γ
  have hf (γ : ℝ) (p) (ω : S.Ω) (x) :
      (T.filtrationGraded (tensorFiltration P R) γ hS).toNormFamily.norm ω
        ((f γ p).baseChange (S.ϕ ω).Completion x) ≤ (C γ p).toNormFamily.norm ω x :=
    NormFamily.tensorFiltrationGradedPair_norm_le V.toNormFamily W.toNormFamily
      hN hV hW hP hR p.property ω x
  have hmin (γ : ℝ) : (γ : EReal) ≤
      (T.filtrationGraded (tensorFiltration P R) γ hS).minimalSlope hS hN := by
    let G := T.filtrationGraded (tensorFiltration P R) γ hS
    have hG := hT.filtrationGraded (tensorFiltration P R) γ
    apply G.le_minimalSlope_of_hermitianHNFiltration_eq_top hS hN hG γ
    apply top_unique
    rw [← hspan γ]
    apply iSup_le
    intro p
    have hsource : (C γ p).hermitianHNFiltration hS hN (hC γ p) γ = ⊤ := by
      apply (C γ p).hermitianHNFiltration_eq_top_of_minimalSlope_ge hS hN (hC γ p)
      rcases hCs γ p with hz | ⟨hsemi, hslope⟩
      · rw [(C γ p).minimalSlope_eq_top_of_finrank_eq_zero hS hN hz]
        exact le_top
      · rw [((C γ p).isMeanSlopeSemistable_iff_minimalSlope_eq_slope_of_isHermitian
          hS hN (hC γ p) hsemi.1).mp hsemi, hslope]
    have hmap := (C γ p).map_hermitianHNFiltration_le_of_completed_contraction
      G hS hN (hC γ p) hG (f γ p) (hf γ p) γ
    simpa only [hsource, Submodule.map_top] using hmap
  obtain ⟨hbot, htop⟩ := tensorFiltration_attains_bot_top b c w z hb hc
  apply T.hermitianHNFiltration_eq_of_graded_quotient_bounds hS hN hT
    (tensorFiltration P R) (antitone_tensorFiltration P R) hbot htop
    (tensorFiltration_locallyConstant_left b c w z hb hc)
  · intro γ
    let G := T.filtrationGraded (tensorFiltration P R) γ hS
    by_cases hz : finrank K (FiltrationGraded (tensorFiltration P R) γ) = 0
    · rw [hz, Nat.cast_zero, mul_zero, G.degree_eq_zero_of_finrank_eq_zero hS hN hz]
    · have hslope : γ ≤ G.slope hS hN := EReal.coe_le_coe_iff.mp
        ((hmin γ).trans (G.minimalSlope_le_slope hS hN (Nat.pos_of_ne_zero hz)))
      rw [G.degree_eq_rank_mul_slope hS hN, mul_comm γ]
      exact mul_le_mul_of_nonneg_left hslope (Nat.cast_nonneg _)
  · exact finsum_tensor_hermitianHNFiltration_eq_degree V W hS hN hV hW
  · intro γ U hr
    exact EReal.coe_le_coe_iff.mp ((hmin γ).trans
      ((T.filtrationGraded (tensorFiltration P R) γ hS).minimalSlope_le_slope_quotient
        U hr hS hN))

end ArakelovGeometry.AdelicVectorBundle
