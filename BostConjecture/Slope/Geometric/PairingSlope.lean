/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Slope.Geometric.ImageSlope
public import BostConjecture.Arithmetic.Specht.DeterminantDegree
public import BostConjecture.Arithmetic.Determinant.Dual

/-!
# The finite-degree inequality from the actual canonical pairing

The integral determinant pairing is injective and contracting. Comparing
its source and target degrees yields the finite-degree slope estimate
whose Specht error tends to zero.
-/

@[expose] public section

noncomputable section

open Module NumberField TensorProduct
open scoped BigOperators

namespace BostConjecture.Slope.Geometric

open Arithmetic Arithmetic.Specht BostConjecture.Specht

universe u
variable {K V : Type u} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  (E : ι → Type u) [∀ j, AddCommGroup (E j)] [∀ j, Module (𝓞 K) (E j)]
  [∀ j, Module.Finite (𝓞 K) (E j)] [∀ j, Module.Projective (𝓞 K) (E j)]
  (hE : ∀ j, HermitianMetric K (E j))
  [AddCommGroup V] [Module (𝓞 K) V]
  [Module.Finite (𝓞 K) V] [Module.Projective (𝓞 K) V]
  (i : V →ₗ[𝓞 K] (⨂[𝓞 K] j, E j)) (hi : Function.Injective i)
  {n s l : ℕ} {a k : ι → ℕ}

local instance slopeDualDeterminantAddGroup
    (t : ∀ j, OAI.Saxl.Tableau n (rectangle (a j) (k j))) :
    ∀ j, AddCommGroup ((⨂[𝓞 K] (_ : Fin (k j)), ⋀[𝓞 K]^(a j) (Dual (𝓞 K) (E j))) ⊗[𝓞 K]
      (𝓞 K ⊗[ℤ] orbitLattice (t j))) := fun _ => Module.addCommMonoidToAddCommGroup (𝓞 K)

local instance slopeSourceDeterminantAddGroup (v : OAI.Saxl.Tableau n (rectangle s l)) :
    AddCommGroup ((⨂[𝓞 K] (_ : Fin l), ⋀[𝓞 K]^s V) ⊗[𝓞 K]
      (𝓞 K ⊗[ℤ] orbitLattice v)) := Module.addCommMonoidToAddCommGroup (𝓞 K)

/-- The finite-degree geometric estimate, obtained from the actual nonzero
canonical pairing with its canonical metrics. -/
theorem canonicalPairing_slope_inequality (hspos : 0 < s) (hapos : ∀ j, 0 < a j)
    (hk : ∀ j, 0 < k j)
    (t : ∀ j, OAI.Saxl.Tableau n (rectangle (a j) (k j)))
    (ha : ∀ j (p : PrimeSpectrum (𝓞 K)), Module.rankAtStalk (Dual (𝓞 K) (E j)) p = a j)
    (hl : 0 < l) (v : OAI.Saxl.Tableau n (rectangle s l))
    (hs : ∀ p : PrimeSpectrum (𝓞 K), Module.rankAtStalk V p = s)
    (hne : Geometry.canonicalPairing E hk t ha hl v hs i ≠ 0) :
    (n : ℝ) * ((HermitianMetric.piTensor hE).pullback i hi).slope - rectangleLogCovolume s l ≤
      (n : ℝ) * (∑ j, (hE j).slope) + ∑ j, rectangleLogCovolume (a j) (k j) := by
  have hh := canonicalPairing_image_slope E hE i hi hk t ha hl v hs hne
  have hb := hh.1.trans hh.2
  rw [determinantMetric_slope_of_pos _ hspos hl v hs, HermitianMetric.slope_dual] at hb
  have hr (j) : 0 < Module.finrank K (K ⊗[𝓞 K]
      ((⨂[𝓞 K] (_ : Fin (k j)), ⋀[𝓞 K]^(a j) (Dual (𝓞 K) (E j))) ⊗[𝓞 K]
        (𝓞 K ⊗[ℤ] orbitLattice (t j)))) := by
    let := determinant_generic_nontrivial (t j) (ha j)
    exact Module.finrank_pos
  rw [slope_piTensor _ _ hr] at hb
  simp only [determinantMetric_slope_of_pos _ (hapos _) (hk _) _ (ha _),
    HermitianMetric.slope_dual, mul_neg] at hb
  convert hb using 1
  rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]
  ring

end BostConjecture.Slope.Geometric
