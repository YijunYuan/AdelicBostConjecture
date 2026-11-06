/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Main.TensorSemistability.BalancedSlope
public import BostConjecture.Main.TensorSemistability.TensorRescale
public import BostConjecture.Main.StrictReduction.MaximizingCounterexample

/-!
# Tensor semistability over arbitrary number fields

The actual compact maximizing pair, strict reduction, metric variations,
intrinsic Plücker semistability and geometric slope inequality rule out every
normalized counterexample. Uniform rescaling gives arbitrary slopes.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace BostConjecture.Arithmetic.HermitianMetric

universe u
variable {K M N : Type u} [Field K] [NumberField K]
    [AddCommGroup M] [Module (𝓞 K) M]
    [AddCommGroup N] [Module (𝓞 K) N]
    [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
    [Module.Finite (𝓞 K) N] [Module.Projective (𝓞 K) N]

/-- There are no actual normalized tensor counterexamples. -/
theorem isSemistable_tensor_of_degree_zero
    (h : HermitianMetric (K := K) M) (k : HermitianMetric (K := K) N)
    (hrM : 0 < Module.finrank K (K ⊗[𝓞 K] M))
    (hrN : 0 < Module.finrank K (K ⊗[𝓞 K] N))
    (h0 : h.degree = 0) (k0 : k.degree = 0)
    (hs : h.IsSemistable) (ks : k.IsSemistable) : (h.tensor k).IsSemistable := by
  by_contra hbad
  obtain ⟨E, F, ae, af, me, mf, fe, pe, ff, pf, H, G,
      hrE, hrF, H0, G0, Hst, Gst, P, hsat, hpos, hP, hmax⟩ :=
    Compactness.exists_strict_maximizing_counterexample h k hrM hrN h0 k0 hs ks hbad
  let : AddCommGroup E := ae
  let : AddCommGroup F := af
  let : Module (𝓞 K) E := me
  let : Module (𝓞 K) F := mf
  let : Module.Finite (𝓞 K) E := fe
  let : Module.Projective (𝓞 K) E := pe
  let : Module.Finite (𝓞 K) F := ff
  let : Module.Projective (𝓞 K) F := pf
  let : Module.IsTorsionFree (𝓞 K) ((E ⊗[𝓞 K] F) ⧸ P) := hsat
  have he : 0 < Module.finrank K (K ⊗[𝓞 K] E) := by omega
  have hf : 0 < Module.finrank K (K ⊗[𝓞 K] F) := by omega
  have hp : 0 < Module.finrank K (K ⊗[𝓞 K] P) := by
    by_contra hn
    have hz := ((H.tensor G).submodule P).degree_eq_zero_of_rank_zero (by omega)
    linarith
  let σ : K →+* ℂ := Classical.choice inferInstance
  have hbal := H.isBalanced_of_maximizing_pair G P he hf Hst Gst H0 G0 hP hmax σ
  have hb := H.slope_submodule_tensor_le_of_isBalanced G P he hf hp σ hbal
  have hsp : 0 < ((H.tensor G).submodule P).slope :=
    div_pos hpos (by exact_mod_cast hp)
  simp only [slope, H0, G0, zero_div, zero_add] at hb
  exact (not_le_of_gt hsp) hb

/-- The actual Hilbert tensor product of positive-rank semistable Hermitian
finite projective modules over any number field is semistable. -/
theorem IsSemistable.tensor
    {h : HermitianMetric (K := K) M} {k : HermitianMetric (K := K) N}
    (hs : h.IsSemistable) (ks : k.IsSemistable)
    (hrM : 0 < Module.finrank K (K ⊗[𝓞 K] M))
    (hrN : 0 < Module.finrank K (K ⊗[𝓞 K] N)) : (h.tensor k).IsSemistable := by
  have hh := (h.isSemistable_rescale_iff hrM.ne' h.slope).mpr hs
  have hk := (k.isSemistable_rescale_iff hrN.ne' k.slope).mpr ks
  have ht := isSemistable_tensor_of_degree_zero (h.rescale h.slope) (k.rescale k.slope)
    hrM hrN h.degree_rescale_self k.degree_rescale_self hh hk
  rw [tensor_rescale] at ht
  have hr : Module.finrank K (K ⊗[𝓞 K] (M ⊗[𝓞 K] N)) ≠ 0 := by
    rw [tensor_generic_finrank]
    exact mul_ne_zero hrM.ne' hrN.ne'
  exact ((h.tensor k).isSemistable_rescale_iff hr _).mp ht

end BostConjecture.Arithmetic.HermitianMetric
