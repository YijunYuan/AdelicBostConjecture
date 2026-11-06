/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.HN.Unique
public import BostConjecture.Arithmetic.Submodule.Isometry
public import BostConjecture.Slope.Equivariance

/-!
# Isometric invariance of the intrinsic HN filtration

The generic payoff is unchanged by an actual integral fiberwise isometry.
Uniqueness then fixes the generic flag and its saturated integral terms.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct HarderNarasimhan

namespace BostConjecture.Arithmetic.HermitianMetric

variable {K : Type*} [Field K] [NumberField K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]
variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
variable [Nontrivial (K ⊗[𝓞 K] M)]

/-- Every actual integral isometric automorphism preserves the entire generic HN flag. -/
theorem hnFlag_map_equiv (h : HermitianMetric (K := K) M) (e : M ≃ₗ[𝓞 K] M)
    (he : ∀ (σ : K →+* ℂ) (x y : ComplexFiber M σ),
      (h.fiber σ).inner (fiberMap e.toLinearMap σ x) (fiberMap e.toLinearMap σ y) =
        (h.fiber σ).inner x y) (n : ℕ) :
    (h.hnFlag n).map (e.baseChange (𝓞 K) K M M).toLinearMap = h.hnFlag n := by
  let E := e.baseChange (𝓞 K) K M M
  let t := Submodule.orderIsoMapComap E
  apply BostConjecture.Slope.hnFiltration_eq_of_orderIso
    (BostConjecture.Subspace.slope h.subspaceDegree) t _ n
  intro I
  rw [BostConjecture.Subspace.slope_apply, BostConjecture.Subspace.slope_apply]
  have hd (X : Submodule K (K ⊗[𝓞 K] M)) : h.subspaceDegree (t X) = h.subspaceDegree X :=
    h.subspaceDegree_map_equiv e he X
  have hr (X : Submodule K (K ⊗[𝓞 K] M)) : Module.finrank K (t X) = Module.finrank K X :=
    (Submodule.equivMapOfInjective E.toLinearMap E.injective X).finrank_eq.symm
  simp only [hd, BostConjecture.Subspace.intervalRank, hr]

/-- Every actual integral isometric automorphism preserves the saturated integral HN terms. -/
theorem hnSubmodule_map_equiv (h : HermitianMetric (K := K) M) (e : M ≃ₗ[𝓞 K] M)
    (he : ∀ (σ : K →+* ℂ) (x y : ComplexFiber M σ),
      (h.fiber σ).inner (fiberMap e.toLinearMap σ x) (fiberMap e.toLinearMap σ y) =
        (h.fiber σ).inner x y) (n : ℕ) :
    (h.hnSubmodule n).map e.toLinearMap = h.hnSubmodule n := by
  rw [hnSubmodule, ← integralPart_map_equiv, h.hnFlag_map_equiv e he]

end BostConjecture.Arithmetic.HermitianMetric
