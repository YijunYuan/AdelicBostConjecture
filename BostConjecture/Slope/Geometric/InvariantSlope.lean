/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Slope.Geometric.PairingSlope
public import BostConjecture.Specht.Asymptotics.Limit

/-!
# The geometric slope inequality from an actual complex invariant

Nonvanishing invariants give determinant pairings in arbitrarily large
degrees. The sublinear Specht covolume estimate removes their error terms,
yielding the geometric slope inequality in Section 6 of this paper.
-/

@[expose] public section

noncomputable section

open Module NumberField TensorProduct Filter
open scoped BigOperators Topology

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
  {s : ℕ} {a : ι → ℕ}

/-- The verified Specht asymptotic removes the errors along actual nonzero
canonical pairings of unbounded common rectangular degree. -/
theorem slope_le_of_nonzero_pairings (hspos : 0 < s) (hapos : ∀ j, 0 < a j)
    (ha : ∀ j (p : PrimeSpectrum (𝓞 K)), Module.rankAtStalk (Dual (𝓞 K) (E j)) p = a j)
    (hs : ∀ p : PrimeSpectrum (𝓞 K), Module.rankAtStalk V p = s)
    {d₀ : ℕ} (hd : 0 < d₀)
    (hseq : ∀ r : ℕ, 0 < r → ∃ (l : ℕ) (k : ι → ℕ) (hl : 0 < l) (hk : ∀ j, 0 < k j)
      (t : ∀ j, OAI.Saxl.Tableau (d₀ * r) (rectangle (a j) (k j)))
      (v : OAI.Saxl.Tableau (d₀ * r) (rectangle s l)),
      Geometry.canonicalPairing E hk t ha hl v hs i ≠ 0) :
    ((HermitianMetric.piTensor hE).pullback i hi).slope ≤ ∑ j, (hE j).slope := by
  classical
  choose l k hl hk t v hn using fun r => hseq (r + 1) (Nat.succ_pos r)
  have hv (r) : d₀ * (r + 1) = s * l r := by
    simpa using Fintype.card_congr (rectangleCoordinates (v r))
  have ht (r j) : d₀ * (r + 1) = a j * k r j := by
    simpa using Fintype.card_congr (rectangleCoordinates (t r j))
  have hg {b : ℕ} (hb : 0 < b) (q : ℕ → ℕ)
      (hq : ∀ r, d₀ * (r + 1) = b * q r) : Tendsto q atTop atTop := by
    apply tendsto_atTop.2
    intro c
    filter_upwards [eventually_ge_atTop (b * c)] with r hr
    have hmul : b * c ≤ b * q r := by
      rw [← hq]
      nlinarith
    exact Nat.le_of_mul_le_mul_left hmul hb
  have hsLim := (tendsto_rectangleLogCovolume_div hspos).comp (hg hspos l hv)
  have haLim (j) := (tendsto_rectangleLogCovolume_div (hapos j)).comp
    (hg (hapos j) (fun r => k r j) (fun r => ht r j))
  have hbound (r : ℕ) := canonicalPairing_slope_inequality E hE i hi hspos hapos
    (hk r) (t r) ha (hl r) (v r) hs (hn r)
  have hdiv (r : ℕ) :
      ((HermitianMetric.piTensor hE).pullback i hi).slope -
        rectangleLogCovolume s (l r) / (s * l r : ℕ) ≤
      (∑ j, (hE j).slope) + ∑ j, rectangleLogCovolume (a j) (k r j) / (a j * k r j : ℕ) := by
    have hp : (0 : ℝ) < (d₀ * (r + 1) : ℕ) := by exact_mod_cast Nat.mul_pos hd (Nat.succ_pos r)
    have hb := div_le_div_of_nonneg_right (hbound r) hp.le
    simp only [sub_div, add_div, Finset.sum_div, mul_div_cancel_left₀ _ (ne_of_gt hp)] at hb
    simpa only [← hv r, ← ht r] using hb
  have hsLim' :=
    (tendsto_const_nhds (x := ((HermitianMetric.piTensor hE).pullback i hi).slope)).sub hsLim
  have haLim' := (tendsto_const_nhds (x := ∑ j, (hE j).slope)).add
    (tendsto_finsetSum Finset.univ (fun j _ => haLim j))
  simpa only [sub_zero, Finset.sum_const_zero, add_zero] using
    le_of_tendsto_of_tendsto hsLim' haLim' (Filter.Eventually.of_forall hdiv)

end BostConjecture.Slope.Geometric
