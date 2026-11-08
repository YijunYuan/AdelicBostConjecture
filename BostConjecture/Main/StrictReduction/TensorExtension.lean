/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Tensor.Submodule
public import BostConjecture.Arithmetic.Compactness.Topology.MetricTransport
public import BostConjecture.Main.TensorSemistability.Extensions

/-!
# Normalized extensions after tensoring

The shared integral tensor image and quotient isometries identify both pieces
of the tensor exact sequence with their actual Hilbert tensor metrics.

Reference: this paper, Proposition 7.3, pages 12–13.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace BostConjecture.Arithmetic.HermitianMetric

universe u
variable {K : Type*} [Field K] [NumberField K]
variable {M N : Type u} [AddCommGroup M] [Module (𝓞 K) M]
    [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
    [AddCommGroup N] [Module (𝓞 K) N]
    [Module.Finite (𝓞 K) N] [Module.Projective (𝓞 K) N]

/-- Semistability is invariant under an actual integral fiberwise isometry. -/
theorem isSemistable_iff_of_equiv
    (h : HermitianMetric K M) (g : HermitianMetric K N)
    (e : M ≃ₗ[𝓞 K] N)
    (he : ∀ (σ : K →+* ℂ) (x y : ComplexFiber M σ),
      (g.fiber σ).inner (fiberMap e.toLinearMap σ x) (fiberMap e.toLinearMap σ y) =
        (h.fiber σ).inner x y) : h.IsSemistable ↔ g.IsSemistable := by
  have hp : g.pullback e.toLinearMap e.injective = h := ext_inner he
  constructor
  · intro hs
    have hi : h.pullback e.symm.toLinearMap e.symm.injective = g := by
      apply ext_inner
      intro σ x y
      let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
      have hx : fiberMap e.toLinearMap σ (fiberMap e.symm.toLinearMap σ x) = x :=
        (e.baseChange (𝓞 K) ℂ M N).apply_symm_apply x
      have hy : fiberMap e.toLinearMap σ (fiberMap e.symm.toLinearMap σ y) = y :=
        (e.baseChange (𝓞 K) ℂ M N).apply_symm_apply y
      exact (he σ _ _).symm.trans (by rw [hx, hy])
    rw [← hi]
    exact hs.pullback_equiv e.symm
  · intro hs
    rw [← hp]
    exact hs.pullback_equiv e

/-- If the two Hilbert tensor pieces are normalized semistable, the whole
tensor product is normalized semistable, for any saturated first-factor cut. -/
theorem isSemistable_tensor_of_submodule_quotient
    (h : HermitianMetric K M) (g : HermitianMetric K N)
    (P : Submodule (𝓞 K) M) [Module.Projective (𝓞 K) (M ⧸ P)]
    (hP : ((h.submodule P) ⊗[𝓞 K] g).IsSemistable)
    (hP0 : ((h.submodule P) ⊗[𝓞 K] g).degree = 0)
    (hQ : ((h.quotient P) ⊗[𝓞 K] g).IsSemistable)
    (hQ0 : ((h.quotient P) ⊗[𝓞 K] g).degree = 0) :
    (h ⊗[𝓞 K] g).degree = 0 ∧ (h ⊗[𝓞 K] g).IsSemistable := by
  let T := tensorRight N P
  have hPi := tensorRightEquiv_inner h g P
  have hQi := tensorRightQuotientEquiv_inner h g P
  apply (h ⊗[𝓞 K] g).isSemistable_of_submodule_quotient T
  · exact (isSemistable_iff_of_equiv _ _ (tensorRightEquiv N P) hPi).mp hP
  · exact (degree_eq_of_equiv _ _ (tensorRightEquiv N P) hPi).symm.trans hP0
  · exact (isSemistable_iff_of_equiv _ _ (tensorRightQuotientEquiv N P) hQi).mpr hQ
  · exact (degree_eq_of_equiv _ _ (tensorRightQuotientEquiv N P) hQi).trans hQ0

end BostConjecture.Arithmetic.HermitianMetric
