/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Specht.Asymptotics.Sampling

/-!
# Exponential moments of the labelled occupancy law

Transport finite-subset averages through the checked block-subset equivalence.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Specht

open Finset

/-- Coordinate expectations under the labelled law are actual subset averages. -/
theorem sum_occupancyMass_apply {a M A : ℕ} (i : Fin a) (f : ℕ → ℝ) :
    ∑ b : Occupancy a M A, occupancyMass b * f (b.val i).val =
      (∑ s ∈ (univ : Finset (Fin a × Fin M)).powersetCard A,
        f (blockFiber s i).card) / ((a * M).choose A : ℝ) := by
  classical
  have he := (occupancyEquiv a M A).sum_comp
    (fun x => f (x.1.val i).val)
  change (∑ s : {s : Finset (Fin a × Fin M) // s.card = A},
      f (blockFiber s.val i).card) = _ at he
  rw [Fintype.sum_sigma] at he
  simp only [sum_const, card_univ, Fintype.card_pi, Fintype.card_finset_len, nsmul_eq_mul,
    Fintype.card_fin, Nat.cast_prod] at he
  rw [← sum_subtype ((univ : Finset (Fin a × Fin M)).powersetCard A)
    (by simp) (fun s => f (blockFiber s i).card)] at he
  unfold occupancyMass
  rw [he]
  simp_rw [div_mul_eq_mul_div]
  rw [← sum_div]

/-- Block-fiber cardinality is the number of selected labelled population elements in that block. -/
theorem card_blockFiber_eq_inter {a M : ℕ} (s : Finset (Fin a × Fin M)) (i : Fin a) :
    (blockFiber s i).card = (s ∩ ({i} ×ˢ univ)).card := by
  apply card_bij (fun j _ => (i, j))
  · intro j hj
    simpa using hj
  · intro j _ l _ h
    exact (Prod.mk.inj h).2
  · intro p hp
    have hs : p ∈ s := (mem_inter.mp hp).1
    have hi : p.1 = i := by
      simpa only [mem_product, mem_singleton, mem_univ, and_true] using (mem_inter.mp hp).2
    refine ⟨p.2, ?_, ?_⟩
    · simpa only [mem_blockFiber, ← hi] using hs
    · exact Prod.ext hi.symm rfl

/-- The actual labelled occupancy exponential moment has the Bernoulli upper bound. -/
theorem sum_occupancyMass_exp_le {a M A : ℕ} (ha : 0 < a) (hM : 0 < M)
    (hA : A ≤ a * M) (i : Fin a) (θ : ℝ) :
    ∑ b : Occupancy a M A, occupancyMass b * Real.exp ((b.val i).val * θ) ≤
      (1 + (1 / (a : ℝ)) * (Real.exp θ - 1)) ^ A := by
  rw [sum_occupancyMass_apply i (fun n => Real.exp ((n : ℝ) * θ))]
  have h := sampling_exp_le ({i} ×ˢ (univ : Finset (Fin M)))
    (show 0 < Fintype.card (Fin a × Fin M) by simpa using Nat.mul_pos ha hM)
    (show A ≤ Fintype.card (Fin a × Fin M) by simpa using hA) θ
  have hp : (M : ℝ) / ((a : ℝ) * M) = 1 / a := by
    have ha0 : (a : ℝ) ≠ 0 := by positivity
    have hM0 : (M : ℝ) ≠ 0 := by positivity
    field_simp
  simp only [card_product, card_singleton, card_univ, Fintype.card_fin, one_mul,
    Fintype.card_prod, Nat.cast_mul, hp, ← card_blockFiber_eq_inter] at h
  exact h

/-- A quadratic exponential remainder gives a sufficient centered Bernoulli estimate. -/
theorem bernoulli_exp_le {p θ : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hθ : |θ| ≤ 1) :
    1 + p * (Real.exp θ - 1) ≤ Real.exp (p * θ + θ ^ 2) := by
  have he := Real.norm_exp_sub_one_sub_id_le (show ‖θ‖ ≤ 1 by simpa using hθ)
  have he' : Real.exp θ - 1 - θ ≤ θ ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using (le_abs_self _).trans he
  have hmul := mul_le_mul_of_nonneg_left he' hp0
  have hsq := mul_le_mul_of_nonneg_right hp1 (sq_nonneg θ)
  have hlin := Real.add_one_le_exp (p * θ + θ ^ 2)
  nlinarith

/-- Centered exponential moments of the existing occupancy law, for small parameters. -/
theorem sum_occupancyMass_centered_exp_le {a M A : ℕ} (ha : 0 < a) (hM : 0 < M)
    (hA : A ≤ a * M) (i : Fin a) {θ : ℝ} (hθ : |θ| ≤ 1) :
    ∑ b : Occupancy a M A, occupancyMass b *
        Real.exp ((((b.val i).val : ℝ) - A / a) * θ) ≤
      Real.exp ((A : ℝ) * θ ^ 2) := by
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hp0 : (0 : ℝ) ≤ 1 / a := by positivity
  have hp1 : (1 / a : ℝ) ≤ 1 := (div_le_one (by positivity)).mpr ha1
  have hb0 : 0 ≤ 1 + (1 / (a : ℝ)) * (Real.exp θ - 1) := by
    have := mul_nonneg hp0 (Real.exp_nonneg θ)
    nlinarith
  have he (b : Occupancy a M A) :
      Real.exp ((((b.val i).val : ℝ) - A / a) * θ) =
        Real.exp (-(A / a : ℝ) * θ) * Real.exp ((b.val i).val * θ) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [he]
  calc
    _ = Real.exp (-(A / a : ℝ) * θ) *
        (∑ b : Occupancy a M A, occupancyMass b * Real.exp ((b.val i).val * θ)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro b _
      ring
    _ ≤ Real.exp (-(A / a : ℝ) * θ) *
        (1 + (1 / (a : ℝ)) * (Real.exp θ - 1)) ^ A :=
      mul_le_mul_of_nonneg_left (sum_occupancyMass_exp_le ha hM hA i θ) (Real.exp_nonneg _)
    _ ≤ Real.exp (-(A / a : ℝ) * θ) * (Real.exp ((1 / (a : ℝ)) * θ + θ ^ 2)) ^ A :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hb0 (bernoulli_exp_le hp0 hp1 hθ) A) (Real.exp_nonneg _)
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring

/-- Exponential Markov inequality for a finite nonnegative weighted sum. -/
theorem sum_tail_le_exp_mul_sum {ι : Type*} [Fintype ι] (w f : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) {θ : ℝ} (hθ : 0 ≤ θ) (u : ℝ) :
    ∑ i ∈ univ.filter (fun i => u ≤ f i), w i ≤
      Real.exp (-θ * u) * ∑ i, w i * Real.exp (θ * f i) := by
  classical
  rw [sum_filter, mul_sum]
  apply sum_le_sum
  intro i _
  by_cases hi : u ≤ f i
  · simp only [hi, ↓reduceIte]
    have he : 1 ≤ Real.exp (-θ * u) * Real.exp (θ * f i) := by
      rw [← Real.exp_add, Real.one_le_exp_iff]
      nlinarith [mul_nonneg hθ (sub_nonneg.mpr hi)]
    calc
      w i = w i * 1 := (mul_one _).symm
      _ ≤ w i * (Real.exp (-θ * u) * Real.exp (θ * f i)) :=
        mul_le_mul_of_nonneg_left he (hw i)
      _ = _ := by ring
  · simp only [hi, ↓reduceIte]
    exact mul_nonneg (Real.exp_nonneg _) (mul_nonneg (hw i) (Real.exp_nonneg _))

/-- A bounded variable with a local quadratic exponential bound has a two-sided tail bound. -/
theorem sum_abs_tail_le_of_exp_bound {ι : Type*} [Fintype ι] (w f : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) {A : ℝ} (hA : 0 < A) (hf : ∀ i, |f i| ≤ A)
    (hmgf : ∀ θ : ℝ, |θ| ≤ 1 → ∑ i, w i * Real.exp (θ * f i) ≤ Real.exp (A * θ ^ 2))
    {u : ℝ} (hu : 0 < u) :
    ∑ i ∈ univ.filter (fun i => u ≤ |f i|), w i ≤ 2 * Real.exp (-u ^ 2 / (4 * A)) := by
  classical
  by_cases huA : u ≤ A
  · let θ := u / (2 * A)
    have hθ0 : 0 ≤ θ := by dsimp [θ]; positivity
    have hθ1 : θ ≤ 1 := by dsimp [θ]; apply (div_le_one (by positivity)).mpr; linarith
    have hθabs : |θ| ≤ 1 := by rwa [abs_of_nonneg hθ0]
    have hexp : -θ * u + A * θ ^ 2 = -u ^ 2 / (4 * A) := by
      dsimp [θ]
      field_simp
      ring
    have hpos : (∑ i ∈ univ.filter (fun i => u ≤ f i), w i) ≤
        Real.exp (-u ^ 2 / (4 * A)) := by
      calc
        _ ≤ _ := sum_tail_le_exp_mul_sum w f hw hθ0 u
        _ ≤ Real.exp (-θ * u) * Real.exp (A * θ ^ 2) :=
          mul_le_mul_of_nonneg_left (hmgf θ hθabs) (Real.exp_nonneg _)
        _ = _ := by rw [← Real.exp_add, hexp]
    have hneg : (∑ i ∈ univ.filter (fun i => u ≤ -f i), w i) ≤
        Real.exp (-u ^ 2 / (4 * A)) := by
      have hn := hmgf (-θ) (by simpa using hθabs)
      simp only [neg_mul, neg_sq] at hn
      calc
        _ ≤ _ := sum_tail_le_exp_mul_sum w (fun i => -f i) hw hθ0 u
        _ ≤ Real.exp (-θ * u) * Real.exp (A * θ ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
          simpa only [mul_neg] using hn
        _ = _ := by rw [← Real.exp_add, hexp]
    have hsplit : (∑ i ∈ univ.filter (fun i => u ≤ |f i|), w i) ≤
        (∑ i ∈ univ.filter (fun i => u ≤ f i), w i) +
          (∑ i ∈ univ.filter (fun i => u ≤ -f i), w i) := by
      simp only [sum_filter, ← sum_add_distrib]
      apply sum_le_sum
      intro i _
      by_cases hi : 0 ≤ f i
      · rw [abs_of_nonneg hi]
        exact le_add_of_nonneg_right (by split_ifs <;> simp [hw i])
      · rw [abs_of_neg (lt_of_not_ge hi)]
        exact le_add_of_nonneg_left (by split_ifs <;> simp [hw i])
    linarith
  · have hempty : (univ.filter (fun i => u ≤ |f i|) : Finset ι) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro i _ hi
      exact huA (hi.trans (hf i))
    rw [hempty, sum_empty]
    positivity

/-- Uniform two-sided concentration for the actual labelled hypergeometric law. -/
theorem occupancyMass_concentration {a M A : ℕ} (ha : 0 < a) (hM : 0 < M)
    (hA0 : 0 < A) (hA : A ≤ a * M) (i : Fin a) {u : ℝ} (hu : 0 < u) :
    ∑ b ∈ (univ : Finset (Occupancy a M A)).filter
        (fun b => u ≤ |((b.val i).val : ℝ) - A / a|), occupancyMass b ≤
      2 * Real.exp (-u ^ 2 / (4 * (A : ℝ))) := by
  apply sum_abs_tail_le_of_exp_bound occupancyMass
    (fun b : Occupancy a M A => ((b.val i).val : ℝ) - A / a)
    occupancyMass_nonneg (by positivity) _ _ hu
  · intro b
    have hbi : (b.val i).val ≤ A := by
      calc
        _ ≤ ∑ j, (b.val j).val := single_le_sum (fun j _ => Nat.zero_le _) (mem_univ i)
        _ = A := b.property
    have hbi' : ((b.val i).val : ℝ) ≤ A := by exact_mod_cast hbi
    have hmean0 : (0 : ℝ) ≤ A / a := by positivity
    have hmean1 : (A / a : ℝ) ≤ A := by
      apply div_le_self (by positivity)
      exact_mod_cast ha
    rw [abs_le]
    have hbi0 : (0 : ℝ) ≤ (b.val i).val := by positivity
    constructor <;> linarith
  · intro θ hθ
    simpa only [mul_comm θ] using sum_occupancyMass_centered_exp_le ha hM hA i hθ

/-- Union bound for simultaneous deviations of the labelled coordinates. -/
theorem occupancyMass_max_concentration {a M A : ℕ} (ha : 0 < a) (hM : 0 < M)
    (hA0 : 0 < A) (hA : A ≤ a * M) {u : ℝ} (hu : 0 < u) :
    ∑ b ∈ (univ : Finset (Occupancy a M A)).filter
        (fun b => ∃ i : Fin a, u ≤ |((b.val i).val : ℝ) - A / a|), occupancyMass b ≤
      2 * a * Real.exp (-u ^ 2 / (4 * (A : ℝ))) := by
  classical
  calc
    _ ≤ ∑ i : Fin a, ∑ b ∈ (univ : Finset (Occupancy a M A)).filter
        (fun b => u ≤ |((b.val i).val : ℝ) - A / a|), occupancyMass b := by
      simp only [sum_filter]
      rw [sum_comm]
      apply sum_le_sum
      intro b _
      split_ifs with hb
      · obtain ⟨i, hi⟩ := hb
        have h := single_le_sum
          (f := fun j : Fin a => if u ≤ |((b.val j).val : ℝ) - A / a|
            then occupancyMass b else 0)
          (fun j _ => by split_ifs <;> simp [occupancyMass_nonneg]) (mem_univ i)
        simpa only [hi, ↓reduceIte] using h
      · apply sum_nonneg
        intro i _
        split_ifs <;> simp [occupancyMass_nonneg]
    _ ≤ ∑ _i : Fin a, 2 * Real.exp (-u ^ 2 / (4 * (A : ℝ))) :=
      sum_le_sum (fun i _ => occupancyMass_concentration ha hM hA0 hA i hu)
    _ = _ := by simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end BostConjecture.Specht
