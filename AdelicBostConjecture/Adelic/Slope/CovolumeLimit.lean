/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import AdelicBostConjecture.Adelic.Specht.Degree
public import AdelicBostConjecture.Specht.Asymptotics.Limit

/-!
# Eliminating the rectangular Specht covolume errors

The normalized limit already proved for the actual integral Specht lattice
removes the finite-degree errors in Section 6 of this paper. The scalar
coefficient is arbitrary, so this applies to the mass of the Archimedean places.
-/

@[expose] public section

open Filter
open scoped BigOperators TensorProduct Topology

namespace AdelicBostConjecture.Adelic

open Specht

/-- This paper, Proposition 5.1: the negative slope of the constant rectangular Specht
bundle divided by the tensor degree tends to zero at fixed positive height.
The bases may vary with the width; equation (2.10) identifies every slope with its covolume. -/
theorem tendsto_neg_specht_slope_div {K : Type*} [Field K] [CharZero K]
    (S : ArakelovGeometry.AdelicStructure K) [S.IsProper] [S.IsArchimedeanNormalized]
    [S.HasCommonCountableDenseSubfield] {a : ℕ} (ha : 0 < a)
    (t : ∀ k, OAI.Saxl.Tableau (a * k) (rectangle a k))
    (b : ∀ k, Module.Basis
      (Fin (Module.finrank K (K ⊗[ℤ] orbitLattice (t k)))) ℤ (orbitLattice (t k))) :
    Tendsto (fun k : ℕ => -(latticeBundle S (t k) (b k)).slope / (a * k : ℕ))
      atTop (𝓝 0) := by
  simpa only [latticeBundle_slope_rectangle, neg_mul, neg_neg, mul_div_assoc, mul_zero]
    using (tendsto_rectangleLogCovolume_div ha).const_mul (S.v S.Ωinf).toReal

/-- Along common rectangular degrees, the actual Specht covolume errors are
sublinear. No sign condition is required on their common scalar coefficient. -/
theorem le_of_rectangleLogCovolume_bounds {ι : Type*} [Fintype ι]
    {s d : ℕ} {a : ι → ℕ} (hs : 0 < s) (hd : 0 < d) (ha : ∀ i, 0 < a i)
    (l : ℕ → ℕ) (k : ℕ → ι → ℕ)
    (hl : ∀ r, d * (r + 1) = s * l r)
    (hk : ∀ r i, d * (r + 1) = a i * k r i)
    (c x y : ℝ)
    (hbound : ∀ r : ℕ,
      (d * (r + 1) : ℕ) * x - c * rectangleLogCovolume s (l r) ≤
      (d * (r + 1) : ℕ) * y + c * ∑ i, rectangleLogCovolume (a i) (k r i)) :
    x ≤ y := by
  have hg {b : ℕ} (hb : 0 < b) (q : ℕ → ℕ)
      (hq : ∀ r, d * (r + 1) = b * q r) : Tendsto q atTop atTop := by
    apply tendsto_atTop.2
    intro n
    filter_upwards [eventually_ge_atTop (b * n)] with r hr
    have hmul : b * n ≤ b * q r := by
      rw [← hq]
      nlinarith
    exact Nat.le_of_mul_le_mul_left hmul hb
  have hsLim := (tendsto_rectangleLogCovolume_div hs).comp (hg hs l hl)
  have haLim (i) := (tendsto_rectangleLogCovolume_div (ha i)).comp
    (hg (ha i) (fun r => k r i) (fun r => hk r i))
  have hdiv (r : ℕ) :
      x - c * (rectangleLogCovolume s (l r) / (s * l r : ℕ)) ≤
      y + c * ∑ i, rectangleLogCovolume (a i) (k r i) / (a i * k r i : ℕ) := by
    have hp : (0 : ℝ) < (d * (r + 1) : ℕ) := by
      exact_mod_cast Nat.mul_pos hd (Nat.succ_pos r)
    have hb := div_le_div_of_nonneg_right (hbound r) hp.le
    simp only [sub_div, add_div, mul_div_cancel_left₀ _ (ne_of_gt hp)] at hb
    simp only [mul_div_assoc, Finset.sum_div] at hb
    simpa only [← hl r, ← hk r] using hb
  have hleft := (tendsto_const_nhds (x := x)).sub (hsLim.const_mul c)
  have hright := (tendsto_const_nhds (x := y)).add
    ((tendsto_finsetSum Finset.univ (fun i _ => haLim i)).const_mul c)
  simpa only [mul_zero, sub_zero, Finset.sum_const_zero, add_zero] using
    le_of_tendsto_of_tendsto hleft hright (Filter.Eventually.of_forall hdiv)

end AdelicBostConjecture.Adelic
