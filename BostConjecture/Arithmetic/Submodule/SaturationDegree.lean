/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Determinant.Contraction
public import BostConjecture.Arithmetic.Submodule.IntegralSubspace
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Saturation increases intrinsic degree

The inclusion of integral submodules of the same generic rank is isometric
on fibers with their induced metrics. The determinant contraction theorem
therefore proves degree monotonicity, including for the actual saturation.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace BostConjecture.Arithmetic.HermitianMetric

variable {K : Type*} [Field K] [NumberField K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]

/-- The induced metric is unchanged along nested integral inclusions. -/
lemma submodule_inner_inclusion (h : HermitianMetric K M)
    {P T : Submodule (𝓞 K) M} (hPT : P ≤ T) (σ : K →+* ℂ)
    (x y : ComplexFiber P σ) :
    ((h.submodule T).fiber σ).inner (fiberMap (Submodule.inclusion hPT) σ x)
        (fiberMap (Submodule.inclusion hPT) σ y) =
      ((h.submodule P).fiber σ).inner x y := by
  let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  have he : (fiberMap T.subtype σ).comp (fiberMap (Submodule.inclusion hPT) σ) =
      fiberMap P.subtype σ :=
    (LinearMap.baseChange_comp (A := ℂ) (Submodule.inclusion hPT) T.subtype).symm
  change (h.fiber σ).inner
    ((fiberMap T.subtype σ).comp (fiberMap (Submodule.inclusion hPT) σ) x)
    ((fiberMap T.subtype σ).comp (fiberMap (Submodule.inclusion hPT) σ) y) = _
  rw [he]
  rfl

variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]

/-- Equal-rank integral inclusions increase the degree for induced metrics. -/
theorem degree_submodule_le_of_le (h : HermitianMetric K M)
    {P T : Submodule (𝓞 K) M} (hPT : P ≤ T)
    (hr : Module.finrank K (K ⊗[𝓞 K] P) = Module.finrank K (K ⊗[𝓞 K] T)) :
    (h.submodule P).degree ≤ (h.submodule T).degree := by
  apply (h.submodule P).degree_le_of_injective (h.submodule T)
    (Submodule.inclusion hPT) (Submodule.inclusion_injective hPT) hr
  exact fun σ x =>
    le_of_eq (congrArg Real.sqrt (congrArg Complex.re (h.submodule_inner_inclusion hPT σ x x)))

/-- The actual saturation of an integral submodule has at least its degree. -/
theorem degree_le_saturation (h : HermitianMetric K M)
    (P : Submodule (𝓞 K) M) :
    (h.submodule P).degree ≤ (h.submodule (integralPart (P.baseChange K))).degree := by
  apply h.degree_submodule_le_of_le
    (fun x hx => Submodule.tmul_mem_baseChange_of_mem 1 hx)
  exact (Submodule.toBaseChange.toLinearEquiv K P).finrank_eq.trans
    (integralPart_generic_finrank (P.baseChange K)).symm

end BostConjecture.Arithmetic.HermitianMetric
