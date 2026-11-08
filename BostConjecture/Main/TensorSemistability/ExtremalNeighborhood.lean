/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Main.TensorSemistability.VariationTopology
public import BostConjecture.Main.TensorSemistability.Extensions
public import BostConjecture.Arithmetic.Compactness.Maximum.MaximizingPair
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Actual local degree maxima at strictly stable maximizing pairs

Global maximality in the realized value set bounds each fixed saturated
submodule along admissible metric variations. Reference:
this paper, Proposition 7.3, pages 12–13.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct Filter
open scoped Topology

namespace BostConjecture.Arithmetic.HermitianMetric

universe u
variable {K : Type*} [Field K] [NumberField K]
variable {M N : Type u} [AddCommGroup M] [Module (𝓞 K) M]
    [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
    [AddCommGroup N] [Module (𝓞 K) N]
    [Module.Finite (𝓞 K) N] [Module.Projective (𝓞 K) N]

/-- Normalized strict stability implies genuine integral semistability,
including nonsaturated test modules by saturation. -/
theorem IsStable.isSemistable_of_degree_zero {h : HermitianMetric K M}
    (hst : h.IsStable) (h0 : h.degree = 0) : h.IsSemistable := by
  apply (h.isSemistable_iff_degree_nonpos h0).mpr
  intro P
  apply (h.degree_le_saturation P).trans
  by_cases hb : integralPart (P.baseChange K) = ⊥
  · exact ((congrArg (fun Q : Submodule (𝓞 K) M => (h.submodule Q).degree) hb).trans
      h.degree_submodule_bot).le
  by_cases ht : integralPart (P.baseChange K) = ⊤
  · exact ((congrArg (fun Q : Submodule (𝓞 K) M => (h.submodule Q).degree) ht).trans
      (h.degree_submodule_top.trans h0)).le
  exact ((h.isStable_iff_degree_neg h0).mp hst _ inferInstance hb ht).le

/-- Global attainment in the actual realized-value set yields a local degree
maximum along every continuous normalized curve through a strictly stable pair.
This consumes the global maximizing-pair output; local maximality is a conclusion. -/
theorem isLocalMax_degree_of_maximizing_pair
    (h : HermitianMetric K M) (g : HermitianMetric K N)
    (P : Submodule (𝓞 K) (M ⊗[𝓞 K] N))
    [Module.IsTorsionFree (𝓞 K) ((M ⊗[𝓞 K] N) ⧸ P)]
    (hst : h.IsStable) (gst : g.IsStable) (h0 : h.degree = 0) (g0 : g.degree = 0)
    (hP : ((h ⊗[𝓞 K] g).submodule P).degree = (h ⊗[𝓞 K] g).maxDegree)
    (hmax : IsGreatest (Compactness.tensorMaxDegreeValues.{u} K
      (Module.finrank K (K ⊗[𝓞 K] M)) (Module.finrank K (K ⊗[𝓞 K] N)))
      (h ⊗[𝓞 K] g).maxDegree)
    (H : ℝ → HermitianMetric K M) (G : ℝ → HermitianMetric K N)
    (hH : ContinuousAt H 0) (hG : ContinuousAt G 0) (H0 : H 0 = h) (G0 : G 0 = g)
    (Hd : ∀ t, (H t).degree = 0) (Gd : ∀ t, (G t).degree = 0) :
    IsLocalMax (fun t => (((H t) ⊗[𝓞 K] (G t)).submodule P).degree) 0 := by
  have he := hH.eventually (by simpa only [H0] using hst.eventually_isStable_normalized h0)
  have ge := hG.eventually (by simpa only [G0] using gst.eventually_isStable_normalized g0)
  filter_upwards [he, ge] with t ht gt
  have hmem := Compactness.tensor_maxDegree_mem (H t) (G t) rfl rfl
    (Hd t) (Gd t) ((ht (Hd t)).isSemistable_of_degree_zero (Hd t))
    ((gt (Gd t)).isSemistable_of_degree_zero (Gd t))
  simpa only [H0, G0, hP] using
    (((H t) ⊗[𝓞 K] (G t)).degree_le_maxDegree P).trans (hmax.2 hmem)

end BostConjecture.Arithmetic.HermitianMetric
