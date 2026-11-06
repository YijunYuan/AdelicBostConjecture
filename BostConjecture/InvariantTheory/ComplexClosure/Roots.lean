/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Polynomial.CauchyBound
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset
public import Mathlib.Data.Finset.Max
public import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Persistence and bounds for roots of monic complex polynomials

Factorization gives a root near any point where the polynomial has small
value. In a fixed-degree monic family this gives roots converging to each
root of the limiting polynomial, without a simplicity hypothesis.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.InvariantTheory

open Polynomial Filter
open scoped Topology

/-- A closest root satisfies the product bound, even at a multiple root. -/
theorem exists_root_norm_sub_pow_le {p : ℂ[X]} (hp : p.Monic)
    (hd : 0 < p.natDegree) (z : ℂ) :
    ∃ w : ℂ, p.IsRoot w ∧ ‖z - w‖ ^ p.natDegree ≤ ‖p.eval z‖ := by
  have hs := IsAlgClosed.splits p
  have hr : p.roots ≠ 0 := by
    intro h
    simp [hs.natDegree_eq_card_roots, h] at hd
  obtain ⟨w, hw, hmin⟩ := Multiset.exists_min_image (fun w : ℂ => ‖z - w‖₊) hr
  refine ⟨w, (Polynomial.mem_roots hp.ne_zero).mp hw, ?_⟩
  have hb : ‖z - w‖₊ ^ p.natDegree ≤ ‖p.eval z‖₊ := by
    rw [hs.eval_eq_prod_roots_of_monic hp z, hs.natDegree_eq_card_roots]
    change _ ≤ (nnnormHom : ℂ →*₀ NNReal) ((p.roots.map (fun w => z - w)).prod)
    rw [map_multiset_prod, Multiset.map_map]
    have h := Multiset.pow_card_le_prod
      (s := p.roots.map (fun w => ‖z - w‖₊)) (a := ‖z - w‖₊) (by
        intro a ha
        obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.mp ha
        exact hmin v hv)
    simpa using h
  exact_mod_cast hb

/-- Roots persist in any fixed-degree monic family whose values tend to zero. -/
theorem exists_roots_tendsto {α : Type*} {l : Filter α} {p : α → ℂ[X]} {r : ℕ}
    (hp : ∀ a, (p a).Monic) (hd : ∀ a, (p a).natDegree = r) (hr : 0 < r)
    (z : ℂ) (hz : Tendsto (fun a => (p a).eval z) l (𝓝 0)) :
    ∃ w : α → ℂ, (∀ a, (p a).IsRoot (w a)) ∧ Tendsto w l (𝓝 z) := by
  choose w hw hb using fun a => exists_root_norm_sub_pow_le (hp a) (by rw [hd a]; exact hr) z
  refine ⟨w, hw, Metric.tendsto_nhds.mpr ?_⟩
  intro ε hε
  have he : ∀ᶠ a in l, ‖(p a).eval z‖ < ε ^ r := by
    have h := hz.norm.eventually (gt_mem_nhds (show ‖(0 : ℂ)‖ < ε ^ r by
      simpa using pow_pos hε r))
    exact h
  filter_upwards [he] with a ha
  have hb' : ‖z - w a‖ ^ r ≤ ‖(p a).eval z‖ := by simpa [hd a] using hb a
  have hpow : ‖z - w a‖ ^ r < ε ^ r := hb'.trans_lt ha
  have hlt : ‖z - w a‖ < ε := by
    by_contra h
    exact (not_lt_of_ge (pow_le_pow_left₀ hε.le (le_of_not_gt h) r)) hpow
  simpa only [dist_eq_norm, norm_sub_rev] using hlt

/-- Evaluation of a polynomial with polynomial coefficients varies continuously. -/
theorem continuous_eval_map {σ : Type*} (F : Polynomial (MvPolynomial σ ℂ)) (z : ℂ) :
    Continuous (fun a : σ → ℂ => (F.map (MvPolynomial.eval a)).eval z) := by
  simp only [Polynomial.eval_map, Polynomial.eval₂_eq_sum_range]
  exact continuous_finsetSum _ fun i _ => (MvPolynomial.continuous_eval _).mul continuous_const

/-- Persistence applies to specialization in polynomial parameters. -/
theorem exists_roots_tendsto_specialization {σ α : Type*}
    (F : Polynomial (MvPolynomial σ ℂ)) (hF : F.Monic) (hd : 0 < F.natDegree)
    {l : Filter α} {a : α → σ → ℂ} {a₀ : σ → ℂ} (ha : Tendsto a l (𝓝 a₀))
    {z : ℂ} (hz : (F.map (MvPolynomial.eval a₀)).IsRoot z) :
    ∃ w : α → ℂ, (∀ k, (F.map (MvPolynomial.eval (a k))).IsRoot (w k)) ∧
      Tendsto w l (𝓝 z) := by
  apply exists_roots_tendsto (fun k => hF.map _) (fun k => hF.natDegree_map _) hd z
  simpa only [Function.comp_def, hz.eq_zero] using
    (continuous_eval_map F z).continuousAt.tendsto.comp ha

/-- A monic root is bounded by the sum of the norms of the lower coefficients. -/
theorem norm_root_lt_coeff_sum {p : ℂ[X]} (hp : p.Monic) {w : ℂ} (hw : p.IsRoot w) :
    ‖w‖₊ < (∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖₊) + 1 := by
  apply (hw.norm_lt_cauchyBound hp.ne_zero).trans_le
  simp only [Polynomial.cauchyBound, hp.leadingCoeff, nnnorm_one, div_one]
  exact add_le_add (Finset.sup_le fun i hi =>
    Finset.single_le_sum (fun j _ => show (0 : NNReal) ≤ ‖p.coeff j‖₊ from bot_le) hi) le_rfl

/-- All roots over a convergent sequence of parameter values are uniformly bounded. -/
theorem exists_bound_roots_specialization {σ : Type*}
    (F : Polynomial (MvPolynomial σ ℂ)) (hF : F.Monic)
    {a : ℕ → σ → ℂ} {a₀ : σ → ℂ} (ha : Tendsto a atTop (𝓝 a₀)) :
    ∃ B : NNReal, ∀ k w, (F.map (MvPolynomial.eval (a k))).IsRoot w → ‖w‖₊ ≤ B := by
  let C : (σ → ℂ) → NNReal := fun x =>
    (∑ i ∈ Finset.range F.natDegree, ‖MvPolynomial.eval x (F.coeff i)‖₊) + 1
  have hc : Continuous C :=
    (continuous_finsetSum _ fun i _ => (MvPolynomial.continuous_eval _).nnnorm).add
      continuous_const
  have ht : Tendsto (fun k => C (a k)) atTop (𝓝 (C a₀)) := hc.continuousAt.tendsto.comp ha
  obtain ⟨B, hB⟩ := ht.bddAbove_range
  refine ⟨B, fun k w hw => ?_⟩
  have hb := norm_root_lt_coeff_sum (hF.map (MvPolynomial.eval (a k))) hw
  have hb' : ‖w‖₊ < C (a k) := by
    simpa [C, hF.natDegree_map] using hb
  exact hb'.le.trans (hB (Set.mem_range_self k))

end BostConjecture.InvariantTheory
