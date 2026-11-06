/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Main.LineTwist.Submodule
public import BostConjecture.Arithmetic.HN.Semistable

/-!
# Semistability of actual Hermitian line twists

Every integral tensor submodule is recovered by integral dual contraction.
The existing tensor-pullback and tensor-degree theorems then give the exact
induced slope shift and semistability, in both factor orders.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace BostConjecture.Arithmetic

universe u
variable {K : Type*} [Field K] [NumberField K]
variable {M L : Type u} [AddCommGroup M] [Module (𝓞 K) M]
    [AddCommGroup L] [Module (𝓞 K) L]
    [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
    [Module.Finite (𝓞 K) L] [Module.Projective (𝓞 K) L]

omit [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M] in
/-- The actual tensor image has the original generic rank under a line twist. -/
lemma tensorRight_generic_finrank_of_rank_one
    (hL : Module.finrank K (K ⊗[𝓞 K] L) = 1) (P : Submodule (𝓞 K) M) :
    Module.finrank K (K ⊗[𝓞 K] tensorRight L P) =
      Module.finrank K (K ⊗[𝓞 K] P) := by
  rw [← ((tensorRightEquiv L P).baseChange (𝓞 K) K _ _).finrank_eq,
    tensor_generic_finrank, hL, mul_one]

namespace HermitianMetric

/-- The ambient slope shifts by the degree of an arbitrary projective line. -/
theorem slope_tensor_rankOne_right (h : HermitianMetric (K := K) M)
    (g : HermitianMetric (K := K) L)
    (hM : 0 < Module.finrank K (K ⊗[𝓞 K] M))
    (hL : Module.finrank K (K ⊗[𝓞 K] L) = 1) :
    (h.tensor g).slope = h.slope + g.degree := by
  rw [slope_tensor h g hM (by omega)]
  simp only [slope, hL, Nat.cast_one, div_one]

/-- The same exact ambient slope shift in the other tensor order. -/
theorem slope_tensor_rankOne_left (h : HermitianMetric (K := K) M)
    (g : HermitianMetric (K := K) L)
    (hM : 0 < Module.finrank K (K ⊗[𝓞 K] M))
    (hL : Module.finrank K (K ⊗[𝓞 K] L) = 1) :
    (g.tensor h).slope = g.degree + h.slope := by
  rw [slope_tensor g h (by omega) hM]
  simp only [slope, hL, Nat.cast_one, div_one]

/-- The induced slope on the actual integral tensor image has the exact line shift. -/
theorem slope_tensorRight_of_rank_one (h : HermitianMetric (K := K) M)
    (g : HermitianMetric (K := K) L)
    (hL : Module.finrank K (K ⊗[𝓞 K] L) = 1)
    (P : Submodule (𝓞 K) M) (hP : 0 < Module.finrank K (K ⊗[𝓞 K] P)) :
    ((h.tensor g).submodule (tensorRight L P)).slope =
      (h.submodule P).slope + g.degree := by
  have hd := degree_eq_of_equiv ((h.submodule P).tensor g)
    ((h.tensor g).submodule (tensorRight L P)) (tensorRightEquiv L P)
    (tensorRightEquiv_inner h g P)
  have hs : ((h.tensor g).submodule (tensorRight L P)).slope =
      ((h.submodule P).tensor g).slope := by
    rw [slope, slope, ← hd,
      ((tensorRightEquiv L P).baseChange (𝓞 K) K _ _).finrank_eq]
  rw [hs, slope_tensor_rankOne_right _ _ hP hL]

/-- Every positive-rank integral submodule, without saturation assumptions,
has precisely the slope of its recovered submodule plus the line degree. -/
theorem slope_submodule_tensor_of_rank_one (h : HermitianMetric (K := K) M)
    (g : HermitianMetric (K := K) L)
    (hL : Module.finrank K (K ⊗[𝓞 K] L) = 1)
    (C : Submodule (𝓞 K) (M ⊗[𝓞 K] L))
    (hC : 0 < Module.finrank K (K ⊗[𝓞 K] C)) :
    ((h.tensor g).submodule C).slope = (h.submodule (lineUntwist C)).slope + g.degree := by
  have hB : 0 < Module.finrank K (K ⊗[𝓞 K] lineUntwist C) := by
    rw [← tensorRight_generic_finrank_of_rank_one hL, tensorRight_lineUntwist hL]
    exact hC
  have he := slope_tensorRight_of_rank_one h g hL (lineUntwist C) hB
  rw [tensorRight_lineUntwist hL] at he
  exact he

/-- Tensoring a semistable bundle on the right with any projective Hermitian line
preserves actual integral semistability. -/
theorem IsSemistable.tensor_rankOne_right {h : HermitianMetric (K := K) M}
    (hs : h.IsSemistable) (g : HermitianMetric (K := K) L)
    (hM : 0 < Module.finrank K (K ⊗[𝓞 K] M))
    (hL : Module.finrank K (K ⊗[𝓞 K] L) = 1) : (h.tensor g).IsSemistable := by
  intro C hC
  have hB : 0 < Module.finrank K (K ⊗[𝓞 K] lineUntwist C) := by
    rw [← tensorRight_generic_finrank_of_rank_one hL, tensorRight_lineUntwist hL]
    exact hC
  rw [slope_submodule_tensor_of_rank_one h g hL C hC,
    slope_tensor_rankOne_right h g hM hL]
  linarith [hs (lineUntwist C) hB]

/-- Tensoring a semistable bundle on the left with any projective Hermitian line
preserves actual integral semistability. -/
theorem IsSemistable.tensor_rankOne_left {h : HermitianMetric (K := K) M}
    (hs : h.IsSemistable) (g : HermitianMetric (K := K) L)
    (hM : 0 < Module.finrank K (K ⊗[𝓞 K] M))
    (hL : Module.finrank K (K ⊗[𝓞 K] L) = 1) : (g.tensor h).IsSemistable := by
  intro C hC
  let e := TensorProduct.comm (𝓞 K) L M
  let eC := Submodule.equivMapOfInjective e.toLinearMap e.injective C
  have hr := (eC.baseChange (𝓞 K) K C (C.map e.toLinearMap)).finrank_eq
  have hd : ((g.tensor h).submodule C).degree =
      ((h.tensor g).submodule (C.map e.toLinearMap)).degree := by
    apply degree_eq_of_equiv _ _ eC
    intro σ x y
    have he : (C.map e.toLinearMap).subtype.comp eC.toLinearMap =
        e.toLinearMap.comp C.subtype := by ext; rfl
    change ((h.tensor g).fiber σ).inner
        (fiberMap (C.map e.toLinearMap).subtype σ (fiberMap eC.toLinearMap σ x))
        (fiberMap (C.map e.toLinearMap).subtype σ (fiberMap eC.toLinearMap σ y)) = _
    have he' := congrArg (fun f => fiberMap f σ) he
    simp only [fiberMap_comp] at he'
    exact (congrArg₂ ((h.tensor g).fiber σ).inner
      (LinearMap.congr_fun he' x) (LinearMap.congr_fun he' y)).trans
        (tensor_comm_inner g h σ _ _)
  have hsc : ((g.tensor h).submodule C).slope =
      ((h.tensor g).submodule (C.map e.toLinearMap)).slope := by
    rw [slope, slope, hd, hr]
  rw [hsc, slope_tensor_rankOne_left h g hM hL]
  have hb := hs.tensor_rankOne_right g hM hL (C.map e.toLinearMap) (hr ▸ hC)
  rw [slope_tensor_rankOne_right h g hM hL] at hb
  linarith

end HermitianMetric

end BostConjecture.Arithmetic
