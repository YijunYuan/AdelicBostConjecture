/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Main.StrictReduction.StrictFactors
public import BostConjecture.Main.LineTwist.Semistability

/-!
# Actual strictly stable maximizing counterexamples

Starting from an actual normalized counterexample, well-ordering chooses the
least rank sum, arithmetic compactness produces a global maximizing pair,
and normalized extension closure proves strict stability of its two factors.
Line twists exclude rank one in both orders.

Reference: this paper, Proposition 7.3, pages 12–13.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace BostConjecture.Arithmetic.Compactness

open scoped HermitianMetric

universe u
variable {K : Type*} [Field K] [NumberField K]

/-- An actual normalized tensor counterexample produces actual degree-zero
strictly stable maximizing factors of ranks at least two and a saturated
positive-degree tensor maximizer. Minimality is constructed internally. -/
theorem exists_strict_maximizing_counterexample
    {M N : Type u} [AddCommGroup M] [Module (𝓞 K) M]
    [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
    [AddCommGroup N] [Module (𝓞 K) N]
    [Module.Finite (𝓞 K) N] [Module.Projective (𝓞 K) N]
    (h : HermitianMetric K M) (g : HermitianMetric K N)
    (hrM : 0 < Module.finrank K (K ⊗[𝓞 K] M))
    (hrN : 0 < Module.finrank K (K ⊗[𝓞 K] N))
    (h0 : h.degree = 0) (g0 : g.degree = 0)
    (hs : h.IsSemistable) (gs : g.IsSemistable)
    (hbad : ¬ (h ⊗[𝓞 K] g).IsSemistable) :
    ∃ E F : Type u, ∃ ae : AddCommGroup E, ∃ af : AddCommGroup F,
    letI := ae; letI := af;
    ∃ me : Module (𝓞 K) E, ∃ mf : Module (𝓞 K) F,
    letI := me; letI := mf;
    ∃ fe : Module.Finite (𝓞 K) E, ∃ pe : Module.Projective (𝓞 K) E,
    ∃ ff : Module.Finite (𝓞 K) F, ∃ pf : Module.Projective (𝓞 K) F,
    letI := fe; letI := pe; letI := ff; letI := pf;
    ∃ H : HermitianMetric K E, ∃ G : HermitianMetric K F,
      2 ≤ Module.finrank K (K ⊗[𝓞 K] E) ∧
      2 ≤ Module.finrank K (K ⊗[𝓞 K] F) ∧
      H.degree = 0 ∧ G.degree = 0 ∧ H.IsStable ∧ G.IsStable ∧
      ∃ P : Submodule (𝓞 K) (E ⊗[𝓞 K] F),
        Module.IsTorsionFree (𝓞 K) ((E ⊗[𝓞 K] F) ⧸ P) ∧
        0 < ((H ⊗[𝓞 K] G).submodule P).degree ∧
        ((H ⊗[𝓞 K] G).submodule P).degree = (H ⊗[𝓞 K] G).maxDegree ∧
        IsGreatest (tensorMaxDegreeValues.{u} K
          (Module.finrank K (K ⊗[𝓞 K] E)) (Module.finrank K (K ⊗[𝓞 K] F)))
          (H ⊗[𝓞 K] G).maxDegree := by
  have hpos := h.maxDegree_tensor_pos_of_not_isSemistable g h0 g0 hbad
  obtain ⟨a, b, ha, hb, ⟨d, hd, hdpos⟩, hmin⟩ :=
    exists_minimal_positive_tensorMaxDegree (K := K)
      ⟨_, _, hrM, hrN, _, tensor_maxDegree_mem h g rfl rfl h0 g0 hs gs, hpos⟩
  obtain ⟨E, F, ae, af, me, mf, fe, pe, ff, pf, H, G,
      hrE, hrF, H0, G0, Hs, Gs, P, hP, hdeg, hmax⟩ :=
    exists_maximizing_pair a b ⟨d, hd⟩
  let : AddCommGroup E := ae
  let : AddCommGroup F := af
  let : Module (𝓞 K) E := me
  let : Module (𝓞 K) F := mf
  let : Module.Finite (𝓞 K) E := fe
  let : Module.Projective (𝓞 K) E := pe
  let : Module.Finite (𝓞 K) F := ff
  let : Module.Projective (𝓞 K) F := pf
  have hEpos : 0 < Module.finrank K (K ⊗[𝓞 K] E) := hrE ▸ ha
  have hFpos : 0 < Module.finrank K (K ⊗[𝓞 K] F) := hrF ▸ hb
  have hmaxpos : 0 < (H ⊗[𝓞 K] G).maxDegree := hdpos.trans_le (hmax.2 hd)
  have hT0 : (H ⊗[𝓞 K] G).degree = 0 := by
    simp [HermitianMetric.degree_tensor, H0, G0]
  have hTbad : ¬ (H ⊗[𝓞 K] G).IsSemistable := by
    intro hT
    exact (not_le_of_gt hmaxpos)
      (((H ⊗[𝓞 K] G).isSemistable_iff_maxDegree_nonpos hT0).mp hT)
  have hE1 : Module.finrank K (K ⊗[𝓞 K] E) ≠ 1 := by
    intro hr
    exact hTbad (Gs.tensor_rankOne_left H hFpos hr)
  have hF1 : Module.finrank K (K ⊗[𝓞 K] F) ≠ 1 := by
    intro hr
    exact hTbad (Hs.tensor_rankOne_right G hEpos hr)
  obtain ⟨Hst, Gst⟩ := H.isStable_factors_of_minimal_rank_sum G H0 G0 Hs Gs
    hEpos hFpos hTbad (by simpa only [hrE, hrF] using hmin)
  refine ⟨E, F, ae, af, me, mf, fe, pe, ff, pf, H, G, by omega, by omega,
    H0, G0, Hst, Gst, P, hP, ?_, hdeg, ?_⟩
  · rwa [hdeg]
  · simpa only [hrE, hrF] using hmax

end BostConjecture.Arithmetic.Compactness
