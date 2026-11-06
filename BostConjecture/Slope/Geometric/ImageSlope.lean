/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Slope.Geometric.PairingInjective
public import BostConjecture.Slope.Geometric.PairingMetric

/-!
# Comparing slopes through the actual canonical image

An injective contraction compares the source slope with the induced
metric on its image. Semistability of the auxiliary target bounds that image slope.
-/

@[expose] public section

noncomputable section

open Module NumberField TensorProduct

namespace BostConjecture.Slope.Geometric

open Arithmetic Arithmetic.Specht BostConjecture.Specht

/-- An injective contraction compares source slope with the slope of its
actual integral image, endowed with the induced metric. -/
theorem slope_le_image_of_injective
    {K M N : Type*} [Field K] [NumberField K]
    [AddCommGroup M] [Module (𝓞 K) M] [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
    [AddCommGroup N] [Module (𝓞 K) N] [Module.Finite (𝓞 K) N] [Module.Projective (𝓞 K) N]
    (h : HermitianMetric (K := K) M) (g : HermitianMetric (K := K) N)
    (f : M →ₗ[𝓞 K] N) (hf : Function.Injective f)
    (hc : ∀ (σ : K →+* ℂ) (x : ComplexFiber M σ),
      Real.sqrt (((g.fiber σ).inner (fiberMap f σ x) (fiberMap f σ x)).re) ≤
        Real.sqrt (((h.fiber σ).inner x x).re)) :
    h.slope ≤ (g.submodule (LinearMap.range f)).slope := by
  let e := LinearEquiv.ofInjective f hf
  have hr := (e.baseChange (𝓞 K) K).finrank_eq
  have hd : h.degree ≤ (g.submodule (LinearMap.range f)).degree := by
    apply h.degree_le_of_injective _ e.toLinearMap e.injective hr
    intro σ x
    have he : (LinearMap.range f).subtype.comp e.toLinearMap = f := rfl
    have hx := LinearMap.congr_fun (fiberMap_comp e.toLinearMap (LinearMap.range f).subtype σ) x
    rw [he] at hx
    simp only [LinearMap.comp_apply] at hx
    change Real.sqrt (((g.fiber σ).inner
      (fiberMap (LinearMap.range f).subtype σ (fiberMap e.toLinearMap σ x))
      (fiberMap (LinearMap.range f).subtype σ (fiberMap e.toLinearMap σ x))).re) ≤ _
    rw [← hx]
    exact hc σ x
  unfold HermitianMetric.slope
  rw [hr]
  exact div_le_div_of_nonneg_right hd (Nat.cast_nonneg _)

section Pairing

universe u
variable {K V : Type u} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  (E : ι → Type u) [∀ j, AddCommGroup (E j)] [∀ j, Module (𝓞 K) (E j)]
  [∀ j, Module.Finite (𝓞 K) (E j)] [∀ j, Module.Projective (𝓞 K) (E j)]
  (hE : ∀ j, HermitianMetric (K := K) (E j))
  [AddCommGroup V] [Module (𝓞 K) V]
  [Module.Finite (𝓞 K) V] [Module.Projective (𝓞 K) V]
  (i : V →ₗ[𝓞 K] (⨂[𝓞 K] j, E j)) (hi : Function.Injective i)
  {n s l : ℕ} {a k : ι → ℕ}

local instance imageDualDeterminantAddGroup
    (t : ∀ j, OAI.Saxl.Tableau n (rectangle (a j) (k j))) :
    ∀ j, AddCommGroup ((⨂[𝓞 K] (_ : Fin (k j)), ⋀[𝓞 K]^(a j) (Dual (𝓞 K) (E j))) ⊗[𝓞 K]
      (𝓞 K ⊗[ℤ] orbitLattice (t j))) := fun _ => Module.addCommMonoidToAddCommGroup (𝓞 K)

local instance imageSourceDeterminantAddGroup (v : OAI.Saxl.Tableau n (rectangle s l)) :
    AddCommGroup ((⨂[𝓞 K] (_ : Fin l), ⋀[𝓞 K]^s V) ⊗[𝓞 K]
      (𝓞 K ⊗[ℤ] orbitLattice v)) := Module.addCommMonoidToAddCommGroup (𝓞 K)

/-- The actual nonzero canonical pairing gives both slope inequalities through
its actual image; the target's semistability is proved on its concrete factors. -/
theorem canonicalPairing_image_slope (hk : ∀ j, 0 < k j)
    (t : ∀ j, OAI.Saxl.Tableau n (rectangle (a j) (k j)))
    (ha : ∀ j (p : PrimeSpectrum (𝓞 K)), Module.rankAtStalk (Dual (𝓞 K) (E j)) p = a j)
    (hl : 0 < l) (v : OAI.Saxl.Tableau n (rectangle s l))
    (hs : ∀ p : PrimeSpectrum (𝓞 K), Module.rankAtStalk V p = s)
    (hne : Geometry.canonicalPairing E hk t ha hl v hs i ≠ 0) :
    let hB := determinantMetric ((HermitianMetric.piTensor hE).pullback i hi) hl v hs
    let hD := (HermitianMetric.piTensor (fun j =>
      determinantMetric (hE j).dual (hk j) (t j) (ha j))).dual
    let J := LinearMap.range (Geometry.canonicalPairing E hk t ha hl v hs i)
    hB.slope ≤ (hD.submodule J).slope ∧ (hD.submodule J).slope ≤ hD.slope := by
  dsimp only
  have hf := canonicalPairing_injective E hk t ha hl v hs i hne
  constructor
  · exact slope_le_image_of_injective _ _ _ hf
      (canonicalPairing_intrinsic_norm_le E hE i hi hk t ha hl v hs)
  · apply (determinantMetric_piTensor_and_dual_isSemistable
      (fun j => Dual (𝓞 K) (E j)) (fun j => (hE j).dual) hk t ha).2
    let e := LinearEquiv.ofInjective (Geometry.canonicalPairing E hk t ha hl v hs i) hf
    rw [← (e.baseChange (𝓞 K) K).finrank_eq]
    let := determinant_generic_nontrivial v hs
    exact Module.finrank_pos

end Pairing

end BostConjecture.Slope.Geometric
