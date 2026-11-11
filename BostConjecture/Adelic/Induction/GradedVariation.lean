/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Adelic.Induction.OptimalVariation
public import ArakelovGeometry.AdelicVectorBundle.Tensor.Graded.Degree
public import BostConjecture.Adelic.Induction.HNContraction

/-!
# The upper bound for Bost's HN variation

This paper, Lemma 7.2. Canonical component contractions preserve the actual
HN thresholds. Lifting the HN filtrations of the target grades bounds the
quotient's perturbed expectation directly by its mean slope. The construction
uses the original restriction and quotient norms and tensor-HN compatibility
on the source grades. Rank drop is supplied by the induction caller.
-/

@[expose] public section

open ArakelovGeometry ArakelovGeometry.AdelicVectorBundle Submodule

open scoped TensorProduct BigOperators
open Module

namespace BostConjecture.Adelic

variable {K E V Q : Type*} [Field K]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup Q] [Module K Q]
  {P : ℝ → Submodule K E} {R : ℝ → Submodule K V}

omit [FiniteDimensional K E] in
/-- A class lying in an induced secondary cut has lexicographically bounded
coordinates in any basis adapted to the primary and lifted filtrations. -/
theorem primary_lt_or_secondary_le_of_graded_mem
    {ι : Type*} (b : Basis ι K E) (w s : ι → ℝ)
    {L : ℝ → Submodule K E}
    (hP : ∀ t, P t = span K (b '' {i | t ≤ w i}))
    (hL : ∀ a, L a = span K (b '' {i | a ≤ s i}))
    {t a : ℝ} (x : P t)
    (hx : filtrationGradedMk P t x ∈ filtrationOnGraded P L t a)
    (i : ι) (hi : b.repr (x : E) i ≠ 0) : t < w i ∨ a ≤ s i := by
  obtain ⟨y, hy, he⟩ := hx
  have hz : (y : E) - (x : E) ∈ filtrationRightLimit P t := by
    exact (show y - x ∈ (filtrationRightLimit P t).comap (P t).subtype from
      (Submodule.Quotient.eq _).mp he)
  by_cases ht : t < w i
  · exact Or.inl ht
  · right
    have hzi : b.repr ((y : E) - (x : E)) i = 0 := by
      rw [filtrationRightLimit_eq_span_weights b w hP] at hz
      exact Finsupp.notMem_support_iff.mp (fun hn ↦ ht (b.mem_span_image.mp hz hn))
    have hni : b.repr (y : E) i ≠ 0 := by
      simp only [map_sub, Finsupp.sub_apply, sub_eq_zero] at hzi
      rw [hzi]
      exact hi
    have hy' : (y : E) ∈ span K (b '' {j | a ≤ s j}) := by
      change (y : E) ∈ L a at hy
      rwa [hL] at hy
    exact b.mem_span_image.mp hy' (Finsupp.mem_support_iff.mpr hni)

omit [FiniteDimensional K E] in
/-- Actual secondary cut membership gives the one-sided variation estimate
in the same source basis. Finite primary gaps control every nonzero matrix
coefficient; the determinant maximum is that of the actual quotient. -/
theorem eventual_image_expectation_le_of_graded_mem
    [FiniteDimensional K Q] {ι : Type*} [Finite ι]
    (b : Basis ι K E) (w s : ι → ℝ)
    (q : E →ₗ[K] Q) (hq : Function.Surjective q)
    {T L : ℝ → Submodule K Q}
    (d : Basis (Fin (finrank K Q)) K Q) (a r : Fin (finrank K Q) → ℝ)
    (hT : ∀ t, T t = span K (d '' {j | t ≤ a j}))
    (hL : ∀ t, L t = span K (d '' {j | t ≤ r j}))
    (hm : ∀ i, q (b i) ∈ T (w i))
    (hc : ∀ i, filtrationGradedMk T (w i) ⟨q (b i), hm i⟩ ∈
      filtrationOnGraded T L (w i) (s i)) :
    ∃ η > 0, ∀ ε, 0 < ε → ε < η →
      filtrationExpectation (fun t ↦ (weightedBasisVariation b w s ε t).map q) ≤
        filtrationExpectation T + ε * filtrationExpectation L := by
  classical
  have he : ∀ᶠ ε : ℝ in nhds 0, ∀ i j, w i < a j →
      w i + ε * s i ≤ a j + ε * r j := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    by_cases hij : w i < a j
    · have hf : ContinuousAt (fun ε : ℝ ↦ w i + ε * s i) 0 := by fun_prop
      have hg : ContinuousAt (fun ε : ℝ ↦ a j + ε * r j) 0 := by fun_prop
      filter_upwards [hf.eventually_lt hg (by simpa using hij)] with ε hε _
      exact hε.le
    · exact Filter.Eventually.of_forall fun _ h ↦ (hij h).elim
  obtain ⟨η, hη, he⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨η, hη, fun ε hε hεη ↦ ?_⟩
  have hcoord (i : ι) : q (b i) ∈ span K (d ''
      {j | w i + ε * s i ≤ a j + ε * r j}) := by
    apply d.mem_span_image.mpr
    intro j hj
    have hn := Finsupp.mem_support_iff.mp hj
    rcases primary_lt_or_secondary_le_of_graded_mem d a r hT hL
      ⟨q (b i), hm i⟩ (hc i) j hn with hlt | hle
    · exact he (by simpa only [Real.dist_eq, sub_zero, abs_of_pos hε] using hεη) i j hlt
    · have hp : w i ≤ a j := d.mem_span_image.mp (hT (w i) ▸ hm i) hj
      exact add_le_add hp (mul_le_mul_of_nonneg_left hle hε.le)
  obtain ⟨σ, hσ, hmax, _⟩ := exists_quotient_expectation_maximum
    b (fun i ↦ w i + ε * s i) d q hq
  change filtrationExpectation (fun t ↦
    (span K (b '' {i | t ≤ w i + ε * s i})).map q) ≤ _
  rw [hmax, filtrationExpectation_eq_sum_weights d a hT,
    filtrationExpectation_eq_sum_weights d r hL]
  have hsum := sum_le_sum_weights_of_det_ne_zero d (fun j ↦ a j + ε * r j)
    (fun j ↦ w (σ j) + ε * s (σ j)) (fun j ↦ q (b (σ j)))
    (fun j ↦ hcoord (σ j)) ((mem_quotientDeterminantSupport b d q σ).mp hσ)
  have hh := div_le_div_of_nonneg_right hsum (Nat.cast_nonneg (finrank K Q))
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, add_div, mul_div_assoc] using hh

end BostConjecture.Adelic

namespace BostConjecture.Adelic

universe u v w w'

variable {K : Type u} [Field K] {S : AdelicStructure.{u, v} K}
  {E F : Type w} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K F]
  {Q : Type w'} [AddCommGroup Q] [Module K Q] [FiniteDimensional K Q]

/-- The chosen HN variation lift has the actual grade-HN cuts at every
real level. Its finite flag data also settle levels outside the jump set. -/
theorem HNVariationLift.filtrationOnGraded_eq
    [S.IsProper]
    {V : AdelicVectorBundle S E}
    {hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield}
    {hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion}
    {hV : V.toNormFamily.IsHermitian hN} {P : ℝ → Submodule K E}
    (L : BostConjecture.Adelic.HNVariationLift V hS hN hV P) (t : ℝ) :
    Submodule.filtrationOnGraded P L.direction t =
      (V.filtrationGraded P t hS).hermitianHNFiltration hS hN (hV.filtrationGraded P t) := by
  classical
  by_cases hm : t ∈ Set.range L.weight
  · obtain ⟨i, rfl⟩ := hm
    let C (A : Submodule K E × Submodule K E) :=
      ∀ s, ((L.direction s).comap A.1.subtype).map (A.2.comap A.1.subtype).mkQ =
        ((V.restrictOfMeasurableBase A.1 hS).quotientOfMeasurableBase
          (A.2.comap A.1.subtype) hS).hermitianHNFiltration
          hS hN ((hV.restrict A.1).quotient (A.2.comap A.1.subtype)) s
    have hp : (P (L.weight i), Submodule.filtrationRightLimit P (L.weight i)) =
        (L.flag i.succ, L.flag i.castSucc) := Prod.ext (L.level i) (L.right i)
    have hc : C (L.flag i.succ, L.flag i.castSucc) := L.cuts i
    exact funext ((congrArg C hp).mpr hc)
  · have := (Module.finrank_eq_zero_iff_of_free K (Submodule.FiltrationGraded P t)).mp
      (Submodule.finrank_filtrationGraded_eq_zero_of_flag
        L.flag L.weight L.level L.reconstruct hm)
    exact Subsingleton.elim _ _

variable [S.IsProper]

/-- HN functoriality on the canonical component contractions gives the
small-positive-parameter upper bound directly by the actual quotient slope.
Tensor-HN compatibility is needed on the source grades; rank drop belongs
only to the induction caller. No secondary image filtration is constructed. -/
theorem tensorFiltrationQuotient_eventual_hn_upper
    (V : AdelicVectorBundle S E) (W : AdelicVectorBundle S F)
    (hS : DiscreteMeasurableSpace S.Ω ∨ S.HasCommonCountableDenseSubfield)
    (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
    (hV : V.toNormFamily.IsHermitian hN) (hW : W.toNormFamily.IsHermitian hN)
    (q : E ⊗[K] F →ₗ[K] Q) (hq : Function.Surjective q)
    {P : ℝ → Submodule K E} {R : ℝ → Submodule K F}
    (hP : Antitone P) (hR : Antitone R)
    {ι κ : Type*} [Finite ι] [Finite κ]
    (b : Basis ι K E) (c : Basis κ K F) (w : ι → ℝ) (z : κ → ℝ)
    (hPw : ∀ t, P t = Submodule.span K (b '' {i | t ≤ w i}))
    (hRz : ∀ u, R u = Submodule.span K (c '' {j | u ≤ z j}))
    (L : BostConjecture.Adelic.HNVariationLift V hS hN hV P)
    (M : BostConjecture.Adelic.HNVariationLift W hS hN hW R)
    (s : ι → ℝ) (v : κ → ℝ)
    (hLs : ∀ t, L.direction t = Submodule.span K (b '' {i | t ≤ s i}))
    (hMv : ∀ t, M.direction t = Submodule.span K (c '' {j | t ≤ v j}))
    (hInd : ∀ t u,
      (tensorFiltrationGradedSource V W hS hN hV hW P R t u).hermitianHNFiltration hS hN
        (tensorFiltrationGradedSource_isHermitian V W hS hN hV hW P R t u) =
      Submodule.tensorFiltration
        ((V.filtrationGraded P t hS).hermitianHNFiltration hS hN (hV.filtrationGraded P t))
        ((W.filtrationGraded R u hS).hermitianHNFiltration hS hN (hW.filtrationGraded R u))) :
    let T := V.orthogonalTensorPair W hS hN hV hW
    let B := T.pushforward q hq (T.isMeasurable.pushforward_of_discrete_or_countable hS q hq)
    ∃ η > 0, ∀ ε, 0 < ε → ε < η →
      Submodule.filtrationExpectation (fun t ↦
        (Submodule.tensorFiltration (Submodule.weightedBasisVariation b w s ε)
          (Submodule.weightedBasisVariation c z v ε) t).map q) ≤
      Submodule.filtrationExpectation (fun t ↦ (Submodule.tensorFiltration P R t).map q) +
        ε * B.slope hS hN := by
  classical
  dsimp only
  let T := V.orthogonalTensorPair W hS hN hV hW
  let B := T.pushforward q hq (T.isMeasurable.pushforward_of_discrete_or_countable hS q hq)
  have hB : B.toNormFamily.IsHermitian hN :=
    (NormFamily.orthogonalTensorPair_isHermitian
      V.toNormFamily W.toNormFamily hN hV hW).pushforward q hq
  let PQ : ℝ → Submodule K Q := fun t ↦ (Submodule.tensorFiltration P R t).map q
  obtain ⟨d₀, a₀, hd₀⟩ := Submodule.exists_weighted_basis_image
    (b.tensorProduct c) (fun p ↦ w p.1 + z p.2) q hq
  have hPQ (t : ℝ) : PQ t = Submodule.span K (d₀ '' {i | t ≤ a₀ i}) := by
    dsimp only [PQ]
    rw [Submodule.tensorFiltration_eq_span_tensorProduct b c w z hPw hRz]
    exact hd₀ t
  have hPQa : Antitone PQ := by
    rw [funext hPQ]
    exact Submodule.antitone_span_weights d₀ a₀
  obtain ⟨hPQb, hPQt⟩ := Submodule.span_weights_attains_bot_top d₀ a₀
  have hPQl := Submodule.span_weights_locallyConstant_left d₀ a₀
  simp_rw [← hPQ] at hPQb hPQt hPQl
  obtain ⟨N⟩ := BostConjecture.Adelic.exists_hnVariationLift B hS hN hB PQ hPQa hPQb hPQt hPQl
  obtain ⟨d, a, r, hd, hNr, _, _⟩ := Submodule.exists_common_weighted_basis
    hPQa hPQb hPQt hPQl N.antitone_direction N.direction_bot N.direction_top N.direction_left
  have hb (i : ι) : b i ∈ P (w i) := by
    rw [hPw]
    exact Submodule.subset_span ⟨i, (show w i ≤ w i from le_rfl), rfl⟩
  have hc (j : κ) : c j ∈ R (z j) := by
    rw [hRz]
    exact Submodule.subset_span ⟨j, (show z j ≤ z j from le_rfl), rfl⟩
  have hm (p : ι × κ) : q ((b.tensorProduct c) p) ∈ PQ (w p.1 + z p.2) := by
    dsimp only [PQ]
    rw [Submodule.tensorFiltration_eq_span_tensorProduct b c w z hPw hRz]
    exact ⟨(b.tensorProduct c) p, Submodule.subset_span
      ⟨p, (show w p.1 + z p.2 ≤ w p.1 + z p.2 from le_rfl), rfl⟩, rfl⟩
  have hclass (p : ι × κ) : Submodule.filtrationGradedMk PQ (w p.1 + z p.2)
      ⟨q ((b.tensorProduct c) p), hm p⟩ ∈
        Submodule.filtrationOnGraded PQ N.direction (w p.1 + z p.2) (s p.1 + v p.2) := by
    let C := tensorFiltrationGradedSource V W hS hN hV hW P R (w p.1) (z p.2)
    let hC := tensorFiltrationGradedSource_isHermitian V W hS hN hV hW P R (w p.1) (z p.2)
    let f := Submodule.tensorFiltrationGradedQuotientPair q hP hR (t := w p.1) (u := z p.2) rfl
    have hf := C.map_hermitianHNFiltration_le_of_completed_contraction
      (B.filtrationGraded PQ (w p.1 + z p.2) hS) hS hN hC (hB.filtrationGraded _ _) f
      (fun ω x ↦ NormFamily.tensorFiltrationGradedPair_pushforward_norm_le
        V.toNormFamily W.toNormFamily hN hV hW q hq hP hR rfl ω x) (s p.1 + v p.2)
    let x := Submodule.filtrationGradedMk P (w p.1) ⟨b p.1, hb p.1⟩
    let y := Submodule.filtrationGradedMk R (z p.2) ⟨c p.2, hc p.2⟩
    have hx : x ∈ (V.filtrationGraded P (w p.1) hS).hermitianHNFiltration
        hS hN (hV.filtrationGraded P (w p.1)) (s p.1) := by
      rw [← L.filtrationOnGraded_eq]
      refine ⟨⟨b p.1, hb p.1⟩, ?_, rfl⟩
      change b p.1 ∈ L.direction (s p.1)
      rw [hLs]
      exact Submodule.subset_span ⟨p.1, (show s p.1 ≤ s p.1 from le_rfl), rfl⟩
    have hy : y ∈ (W.filtrationGraded R (z p.2) hS).hermitianHNFiltration
        hS hN (hW.filtrationGraded R (z p.2)) (v p.2) := by
      rw [← M.filtrationOnGraded_eq]
      refine ⟨⟨c p.2, hc p.2⟩, ?_, rfl⟩
      change c p.2 ∈ M.direction (v p.2)
      rw [hMv]
      exact Submodule.subset_span ⟨p.2, (show v p.2 ≤ v p.2 from le_rfl), rfl⟩
    have hxy : x ⊗ₜ[K] y ∈ C.hermitianHNFiltration hS hN hC (s p.1 + v p.2) := by
      rw [show C.hermitianHNFiltration hS hN hC = _ from hInd (w p.1) (z p.2)]
      exact Submodule.tmul_mem_tensorFiltration le_rfl hx hy
    rw [N.filtrationOnGraded_eq]
    have hmem := hf (Submodule.mem_map.mpr ⟨x ⊗ₜ[K] y, hxy, rfl⟩)
    convert hmem using 1
    dsimp only [f, x, y, Submodule.tensorFiltrationGradedQuotientPair, LinearMap.comp_apply]
    rw [Submodule.tensorFiltrationGradedPair_mk, Submodule.filtrationGradedMap_mk]
    congr 1
    apply Subtype.ext
    exact congrArg q (Basis.tensorProduct_apply b c p.1 p.2)
  obtain ⟨η, hη, hu⟩ := BostConjecture.Adelic.eventual_image_expectation_le_of_graded_mem
    (b.tensorProduct c) (fun p ↦ w p.1 + z p.2) (fun p ↦ s p.1 + v p.2)
    q hq d a r hd hNr hm hclass
  refine ⟨η, hη, fun ε hε he ↦ ?_⟩
  have hvar : Submodule.tensorFiltration (Submodule.weightedBasisVariation b w s ε)
      (Submodule.weightedBasisVariation c z v ε) =
      Submodule.weightedBasisVariation (b.tensorProduct c)
        (fun p ↦ w p.1 + z p.2) (fun p ↦ s p.1 + v p.2) ε := by
    funext t
    unfold Submodule.weightedBasisVariation
    rw [Submodule.tensorFiltration_eq_span_tensorProduct b c
      (fun i ↦ w i + ε * s i) (fun j ↦ z j + ε * v j) (fun _ ↦ rfl) (fun _ ↦ rfl)]
    congr 2
    ext p
    change (t ≤ (w p.1 + ε * s p.1) + (z p.2 + ε * v p.2)) ↔
      t ≤ (w p.1 + z p.2) + ε * (s p.1 + v p.2)
    ring_nf
  rw [hvar]
  simpa only [N.mean] using hu ε hε he

end BostConjecture.Adelic
