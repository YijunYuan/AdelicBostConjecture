module

public import BostConjecture.Arithmetic.Compactness.MetricTransport
public import BostConjecture.Arithmetic.Compactness.MaximumDegree
public import BostConjecture.Arithmetic.SaturationDegree
public import BostConjecture.Arithmetic.TensorCompatibility

/-!
# Integral isometry invariance of maximum degree

Actual integral submodules correspond under integral isomorphisms. Saturation
also bounds every nonsaturated degree by the same attained maximum.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace BostConjecture.Arithmetic.HermitianMetric

universe u
variable {K : Type*} [Field K] [NumberField K]
variable {M N : Type*} [AddCommGroup M] [Module (𝓞 K) M]
    [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
    [AddCommGroup N] [Module (𝓞 K) N]
    [Module.Finite (𝓞 K) N] [Module.Projective (𝓞 K) N]

/-- Saturation bounds every integral induced degree by the saturated maximum. -/
theorem degree_submodule_le_maxDegree (h : HermitianMetric (K := K) M)
    (P : Submodule (𝓞 K) M) : (h.submodule P).degree ≤ h.maxDegree :=
  (h.degree_le_saturation P).trans (h.degree_le_maxDegree (integralPart (P.baseChange K)))

/-- Actual integral isomorphisms preserve maximum saturated degree. -/
theorem maxDegree_pullback_equiv (h : HermitianMetric (K := K) N)
    (e : M ≃ₗ[𝓞 K] N) : (h.pullback e.toLinearMap e.injective).maxDegree = h.maxDegree := by
  apply le_antisymm
  · obtain ⟨P, _, hP⟩ := (h.pullback e.toLinearMap e.injective).exists_degree_eq_maxDegree
    rw [← hP, degree_submodule_pullback_equiv]
    exact h.degree_submodule_le_maxDegree _
  · obtain ⟨Q, _, hQ⟩ := h.exists_degree_eq_maxDegree
    have hp := (h.pullback e.toLinearMap e.injective).degree_submodule_le_maxDegree
      (Q.comap e.toLinearMap)
    rw [degree_submodule_pullback_equiv] at hp
    have heq : (h.submodule ((Q.comap e.toLinearMap).map e.toLinearMap)).degree =
        (h.submodule Q).degree :=
      congrArg (fun P : Submodule (𝓞 K) N => (h.submodule P).degree)
        (Submodule.map_comap_eq_of_surjective e.surjective Q)
    rwa [heq, hQ] at hp

variable {A B C D : Type u}
    [AddCommGroup A] [Module (𝓞 K) A] [Module.Finite (𝓞 K) A] [Module.Projective (𝓞 K) A]
    [AddCommGroup B] [Module (𝓞 K) B] [Module.Finite (𝓞 K) B] [Module.Projective (𝓞 K) B]
    [AddCommGroup C] [Module (𝓞 K) C] [Module.Finite (𝓞 K) C] [Module.Projective (𝓞 K) C]
    [AddCommGroup D] [Module (𝓞 K) D] [Module.Finite (𝓞 K) D] [Module.Projective (𝓞 K) D]

/-- The tensor objective is unchanged by actual integral identifications of both factors. -/
theorem maxDegree_tensor_pullback_equiv (h : HermitianMetric (K := K) C)
    (g : HermitianMetric (K := K) D) (e : A ≃ₗ[𝓞 K] C) (f : B ≃ₗ[𝓞 K] D) :
    ((h.pullback e.toLinearMap e.injective).tensor
      (g.pullback f.toLinearMap f.injective)).maxDegree = (h.tensor g).maxDegree := by
  let t := TensorProduct.congr e f
  have ht : (h.tensor g).pullback t.toLinearMap t.injective =
      (h.pullback e.toLinearMap e.injective).tensor
        (g.pullback f.toLinearMap f.injective) := by
    apply ext_inner
    intro σ x y
    apply Tensor.inner_ext_of_span
      (fun ab : A × B => fiberSection _ σ (ab.1 ⊗ₜ[𝓞 K] ab.2))
      (span_fiberSection_tmul σ) _ _ LinearMap.id LinearMap.id _ x y
    intro a b
    simp only [LinearMap.id_apply, pullback_inner, fiberMap_section,
      t, LinearEquiv.coe_coe, TensorProduct.congr_tmul, tensor_inner_section]
  rw [← ht, maxDegree_pullback_equiv]

end BostConjecture.Arithmetic.HermitianMetric
