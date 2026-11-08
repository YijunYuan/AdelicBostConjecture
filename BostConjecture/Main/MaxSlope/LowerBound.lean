/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.HN.Filtration
public import BostConjecture.Arithmetic.Degree.Tensor

/-!
# The unconditional maximal-slope tensor lower bound

Tensor the actual first HN submodules and compare their induced metric with
that of their integral image. All modules are finite projective over the ring
of integers; no integral basis is chosen.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace BostConjecture.Arithmetic.HermitianMetric

universe u
variable {K : Type*} [Field K] [NumberField K]
variable {M N P Q : Type u}
variable [AddCommGroup M] [Module (𝓞 K) M]
    [AddCommGroup N] [Module (𝓞 K) N]
    [AddCommGroup P] [Module (𝓞 K) P]
    [AddCommGroup Q] [Module (𝓞 K) Q]

/-- The induced metric along an actual tensor injection is the tensor of the
two induced metrics. This equality holds on the entire complex fibers. -/
lemma tensor_map_pullback [Module.Flat (𝓞 K) M] [Module.Flat (𝓞 K) Q]
    (h : HermitianMetric K M) (g : HermitianMetric K N)
    (f : P →ₗ[𝓞 K] M) (j : Q →ₗ[𝓞 K] N)
    (hf : Function.Injective f) (hj : Function.Injective j) :
    (h ⊗[𝓞 K] g).pullback (TensorProduct.map f j)
      (TensorProduct.map_injective_of_flat_flat f j hf hj) =
        (h.pullback f hf) ⊗[𝓞 K] (g.pullback j hj) := by
  apply ext_inner
  intro σ x y
  apply Tensor.inner_ext_of_span
    (fun pq : P × Q => fiberSection _ σ (pq.1 ⊗ₜ[𝓞 K] pq.2))
    (span_fiberSection_tmul σ) _ _ LinearMap.id LinearMap.id _ x y
  intro a b
  simp only [LinearMap.id_apply, pullback_inner, fiberMap_section,
    TensorProduct.map_tmul, tensor_inner_section]

variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
    [Module.Finite (𝓞 K) N] [Module.Projective (𝓞 K) N]

/-- Pullback along an injection has the slope of its actual integral image. -/
lemma slope_pullback_eq_range (h : HermitianMetric K M)
    (f : N →ₗ[𝓞 K] M) (hf : Function.Injective f) :
    (h.pullback f hf).slope = (h.submodule (LinearMap.range f)).slope := by
  let e := LinearEquiv.ofInjective f hf
  have hd : (h.pullback f hf).degree = (h.submodule (LinearMap.range f)).degree := by
    apply degree_eq_of_equiv _ _ e
    intro σ x y
    change (h.fiber σ).inner
      (fiberMap (LinearMap.range f).subtype σ (fiberMap e.toLinearMap σ x))
      (fiberMap (LinearMap.range f).subtype σ (fiberMap e.toLinearMap σ y)) = _
    simp only [← LinearMap.comp_apply, ← fiberMap_comp]
    rfl
  rw [slope, slope, hd, (e.baseChange (𝓞 K) K N (LinearMap.range f)).finrank_eq]

/-- Every positive-rank isometrically induced subbundle has slope at most the
ambient maximum, without a saturation assumption. -/
lemma slope_pullback_le_maxSlope [Nontrivial (K ⊗[𝓞 K] M)]
    (h : HermitianMetric K M) (f : N →ₗ[𝓞 K] M)
    (hf : Function.Injective f) (hN : 0 < Module.finrank K (K ⊗[𝓞 K] N)) :
    (h.pullback f hf).slope ≤ h.maxSlope := by
  rw [slope_pullback_eq_range]
  apply h.slope_submodule_le_maxSlope
  rwa [← ((LinearEquiv.ofInjective f hf).baseChange
    (𝓞 K) K N (LinearMap.range f)).finrank_eq]

/-- The tensor product of two positive-rank generic fibers has positive rank. -/
instance tensorGenericNontrivial
    [Nontrivial (K ⊗[𝓞 K] M)] [Nontrivial (K ⊗[𝓞 K] N)] :
    Nontrivial (K ⊗[𝓞 K] (M ⊗[𝓞 K] N)) := by
  apply Module.nontrivial_of_finrank_pos (R := K)
  rw [tensor_generic_finrank]
  exact Nat.mul_pos Module.finrank_pos Module.finrank_pos

/-- The unconditional lower bound for maximal slopes under Hilbert tensor
products, obtained from the actual first HN terms. -/
theorem maxSlope_add_le_tensor
    [Nontrivial (K ⊗[𝓞 K] M)] [Nontrivial (K ⊗[𝓞 K] N)]
    (h : HermitianMetric K M) (g : HermitianMetric K N) :
    h.maxSlope + g.maxSlope ≤ (h ⊗[𝓞 K] g).maxSlope := by
  let P := h.hnSubmodule 1
  let Q := g.hnSubmodule 1
  let f := TensorProduct.map P.subtype Q.subtype
  have hf : Function.Injective f :=
    TensorProduct.map_injective_of_flat_flat _ _ P.injective_subtype Q.injective_subtype
  have hr : 0 < Module.finrank K (K ⊗[𝓞 K] (P ⊗[𝓞 K] Q)) := by
    rw [tensor_generic_finrank]
    exact Nat.mul_pos h.hnSubmodule_one_rank_pos g.hnSubmodule_one_rank_pos
  have hs := (h ⊗[𝓞 K] g).slope_pullback_le_maxSlope f hf hr
  rw [tensor_map_pullback h g P.subtype Q.subtype P.injective_subtype Q.injective_subtype,
    slope_tensor _ _
    h.hnSubmodule_one_rank_pos g.hnSubmodule_one_rank_pos] at hs
  rw [← h.slope_hnSubmodule_one, ← g.slope_hnSubmodule_one]
  exact hs

end BostConjecture.Arithmetic.HermitianMetric
