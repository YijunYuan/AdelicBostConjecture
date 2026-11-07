/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Tensor.ExactMetric
public import BostConjecture.Arithmetic.Line.RankOneReduction
public import BostConjecture.Arithmetic.Degree.Exact
public import BostConjecture.Arithmetic.Degree.Isometry

/-!
# Intrinsic tensor degree in arbitrary rank

Saturated rank-one reduction, exact determinant degree, and tensor quotient
metrics reduce the formula to the proved nonfree rank-one tensor formula.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace BostConjecture.Arithmetic.HermitianMetric

universe u
variable {K : Type*} [Field K] [NumberField K]
variable {M N P Q : Type u} [AddCommGroup M] [Module (𝓞 K) M]
    [AddCommGroup N] [Module (𝓞 K) N] [AddCommGroup P] [Module (𝓞 K) P]
    [AddCommGroup Q] [Module (𝓞 K) Q]

/-- Interchanging the two factors preserves the entire intrinsic tensor form. -/
lemma tensor_comm_inner (h : HermitianMetric K M)
    (g : HermitianMetric K N) (σ : K →+* ℂ)
    (x y : ComplexFiber (M ⊗[𝓞 K] N) σ) :
    ((g.tensor h).fiber σ).inner
      (fiberMap (TensorProduct.comm (𝓞 K) M N).toLinearMap σ x)
      (fiberMap (TensorProduct.comm (𝓞 K) M N).toLinearMap σ y) =
        ((h.tensor g).fiber σ).inner x y := by
  apply Tensor.inner_ext_of_span (fun xy : M × N => fiberSection _ σ (xy.1 ⊗ₜ[𝓞 K] xy.2))
    (span_fiberSection_tmul σ) ((g.tensor h).fiber σ) ((h.tensor g).fiber σ)
    (fiberMap (TensorProduct.comm (𝓞 K) M N).toLinearMap σ) LinearMap.id _ x y
  intro a b
  simp only [LinearMap.id_apply, fiberMap_section, LinearEquiv.coe_coe,
    TensorProduct.comm_tmul, tensor_inner_section, mul_comm]

variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
    [Module.Finite (𝓞 K) N] [Module.Projective (𝓞 K) N]

lemma degree_tensor_comm (h : HermitianMetric K M)
    (g : HermitianMetric K N) : (h.tensor g).degree = (g.tensor h).degree :=
  degree_eq_of_equiv _ _ (TensorProduct.comm (𝓞 K) M N) (tensor_comm_inner h g)

variable [Module.Finite (𝓞 K) P] [Module.Projective (𝓞 K) P]
    [Module.Finite (𝓞 K) Q] [Module.Projective (𝓞 K) Q]

/-- Exact determinant degree applied to the actual tensor exact sequence. -/
lemma degree_tensor_exact (h : HermitianMetric K P)
    (g : HermitianMetric K Q) (i : M →ₗ[𝓞 K] P) (q : P →ₗ[𝓞 K] N)
    (he : Function.Exact i q) (hi : Function.Injective i) (hq : Function.Surjective q) :
    (h.tensor g).degree = ((h.pullback i hi).tensor g).degree +
      ((h.pushforward q hq).tensor g).degree := by
  have hd := (h.tensor g).degree_exact (i.rTensor Q) (q.rTensor Q)
    (rTensor_exact Q he hq) (Module.Flat.rTensor_preserves_injective_linearMap i hi)
    (LinearMap.rTensor_surjective Q hq)
  rw [tensor_pullback, tensor_pushforward] at hd
  exact hd

/-- Normalized arithmetic tensor degree, for all finite projective modules
over every number field, including rank zero. -/
theorem degree_tensor (h : HermitianMetric K M)
    (g : HermitianMetric K N) :
    (h.tensor g).degree = (Module.finrank K (K ⊗[𝓞 K] N) : ℝ) * h.degree +
      (Module.finrank K (K ⊗[𝓞 K] M) : ℝ) * g.degree := by
  generalize hn : Module.finrank K (K ⊗[𝓞 K] M) + Module.finrank K (K ⊗[𝓞 K] N) = n
  induction n using Nat.strong_induction_on generalizing M N with
  | h n ih =>
    by_cases hM0 : Module.finrank K (K ⊗[𝓞 K] M) = 0
    · have ht : Module.finrank K (K ⊗[𝓞 K] (M ⊗[𝓞 K] N)) = 0 := by
        rw [tensor_generic_finrank, hM0, zero_mul]
      rw [(h.tensor g).degree_eq_zero_of_rank_zero ht, h.degree_eq_zero_of_rank_zero hM0, hM0]
      simp
    by_cases hN0 : Module.finrank K (K ⊗[𝓞 K] N) = 0
    · have ht : Module.finrank K (K ⊗[𝓞 K] (M ⊗[𝓞 K] N)) = 0 := by
        rw [tensor_generic_finrank, hN0, mul_zero]
      rw [(h.tensor g).degree_eq_zero_of_rank_zero ht, g.degree_eq_zero_of_rank_zero hN0, hN0]
      simp
    have hMpos : 0 < Module.finrank K (K ⊗[𝓞 K] M) := Nat.pos_of_ne_zero hM0
    have hNpos : 0 < Module.finrank K (K ⊗[𝓞 K] N) := Nat.pos_of_ne_zero hN0
    by_cases hM1 : Module.finrank K (K ⊗[𝓞 K] M) = 1
    · by_cases hN1 : Module.finrank K (K ⊗[𝓞 K] N) = 1
      · let : Nontrivial M := Module.nontrivial_of_finrank_pos
          (show 0 < Module.finrank (𝓞 K) M from
            (TensorProduct.isBaseChange (𝓞 K) M K).finrank_eq ▸ hMpos)
        let : Nontrivial N := Module.nontrivial_of_finrank_pos
          (show 0 < Module.finrank (𝓞 K) N from
            (TensorProduct.isBaseChange (𝓞 K) N K).finrank_eq ▸ hNpos)
        simpa only [hM1, hN1, Nat.cast_one, one_mul] using h.degree_tensor_of_rank_one g hM1 hN1
      · obtain ⟨L, hLproj, hL, hC⟩ := exists_rank_one_submodule (M := N) hNpos
        let := hLproj
        have hd := g.degree_tensor_exact h L.subtype L.mkQ
          (LinearMap.exact_subtype_mkQ L) L.injective_subtype L.mkQ_surjective
        have ha := ih _ (show Module.finrank K (K ⊗[𝓞 K] L) +
            Module.finrank K (K ⊗[𝓞 K] M) < n by omega)
            (g.pullback L.subtype L.injective_subtype) h rfl
        have hb := ih _ (show Module.finrank K (K ⊗[𝓞 K] (N ⧸ L)) +
            Module.finrank K (K ⊗[𝓞 K] M) < n by omega) (g.pushforward L.mkQ L.mkQ_surjective) h rfl
        have hc := g.degree_exact L.subtype L.mkQ
          (LinearMap.exact_subtype_mkQ L) L.injective_subtype L.mkQ_surjective
        rw [degree_tensor_comm, hd, ha, hb]
        have hCr : (Module.finrank K (K ⊗[𝓞 K] N) : ℝ) =
            1 + (Module.finrank K (K ⊗[𝓞 K] (N ⧸ L)) : ℝ) := by exact_mod_cast hC
        rw [hL, Nat.cast_one, one_mul]
        change _ = (Module.finrank K (K ⊗[𝓞 K] N) : ℝ) * h.degree +
          (Module.finrank K (K ⊗[𝓞 K] M) : ℝ) * g.degree
        rw [hc, hCr]
        ring
    · obtain ⟨L, hLproj, hL, hC⟩ := exists_rank_one_submodule (M := M) hMpos
      let := hLproj
      have hd := h.degree_tensor_exact g L.subtype L.mkQ
        (LinearMap.exact_subtype_mkQ L) L.injective_subtype L.mkQ_surjective
      have ha := ih _ (show Module.finrank K (K ⊗[𝓞 K] L) +
          Module.finrank K (K ⊗[𝓞 K] N) < n by omega)
          (h.pullback L.subtype L.injective_subtype) g rfl
      have hb := ih _ (show Module.finrank K (K ⊗[𝓞 K] (M ⧸ L)) +
          Module.finrank K (K ⊗[𝓞 K] N) < n by omega) (h.pushforward L.mkQ L.mkQ_surjective) g rfl
      have hc := h.degree_exact L.subtype L.mkQ
        (LinearMap.exact_subtype_mkQ L) L.injective_subtype L.mkQ_surjective
      rw [hd, ha, hb]
      have hCr : (Module.finrank K (K ⊗[𝓞 K] M) : ℝ) =
          1 + (Module.finrank K (K ⊗[𝓞 K] (M ⧸ L)) : ℝ) := by exact_mod_cast hC
      rw [hL, Nat.cast_one, one_mul, hc, hCr]
      ring

/-- Average slopes add under the actual Hilbert tensor product. -/
theorem slope_tensor (h : HermitianMetric K M)
    (g : HermitianMetric K N)
    (hM : 0 < Module.finrank K (K ⊗[𝓞 K] M))
    (hN : 0 < Module.finrank K (K ⊗[𝓞 K] N)) :
    (h.tensor g).slope = h.slope + g.slope := by
  have hm : (Module.finrank K (K ⊗[𝓞 K] M) : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hM
  have hn : (Module.finrank K (K ⊗[𝓞 K] N) : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  simp only [slope, degree_tensor, tensor_generic_finrank, Nat.cast_mul]
  field_simp

end BostConjecture.Arithmetic.HermitianMetric
