/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import HarderNarasimhan.Filtration.Exists
public import HarderNarasimhan.PayoffFunction.NashEquilibrium

/-!
# Ordinary slope inequalities in finite-length HN games

Both chain conditions follow from well-founded strict orders. For slope-like
payoffs, the pinned game-value and Nash-equilibrium theorems identify game
semistability with the ordinary inequalities on initial intervals. This is
the bridge required to interpret the intrinsic Hermitian HN specialization.
-/

@[expose] public section

namespace BostConjecture.Slope

open HarderNarasimhan

variable {L S : Type*} [Lattice L] [BoundedOrder L] [CompleteLinearOrder S]

/-- Well-founded descent excludes the bad sequence in the HN game condition. -/
instance adcc_of_wellFoundedLT (μ : PayoffFunction L S) [WellFoundedLT L] : μ.ADCC :=
  ⟨fun _ f _ hf => False.elim (not_strictAnti_of_wellFoundedLT f hf)⟩

variable [WellFoundedGT L] [WellFoundedLT L]
variable (μ : PayoffFunction L S) [μ.IsSlopeLike]

/-- On a finite-length lattice, game semistability is ordinary initial-slope semistability. -/
theorem isSemistable_iff [Nontrivial L] :
    μ.IsSemistable ↔ ∀ x (hx : ⊥ < x), μ ⟨⊥, x, hx⟩ ≤ μ ⊤ := by
  let : μ.StrongDCC := ⟨fun f hf => False.elim (not_strictAnti_of_wellFoundedLT f hf)⟩
  constructor
  · intro h x hx
    have he : μ.max ⊤ = μ ⊤ := PayoffFunction.max_top_eq_apply_iff.mpr
      ((PayoffFunction.min_top_eq_max_top_iff_hasNashEquilibrium (μ := μ)).mpr h.hasNashEquilibrium)
    exact (PayoffFunction.le_max (I := ⊤) ⟨hx, le_top⟩).trans_eq he
  · intro h
    have he : μ.max ⊤ = μ ⊤ := le_antisymm
      (PayoffFunction.max_le fun x hx => h x hx.1) PayoffFunction.apply_le_max
    have hn := (PayoffFunction.min_top_eq_max_top_iff_hasNashEquilibrium (μ := μ)).mp
      (PayoffFunction.max_top_eq_apply_iff.mp he)
    exact PayoffFunction.isSemistable_of_hasNashEquilibrium
      (fun x hx => inferInstance) (fun x hx => inferInstance) hn

omit [BoundedOrder L] in
/-- The same criterion on an arbitrary strict interval. -/
theorem isSemistable_restrict_iff (I : StrictIntvl L) :
    (μ.restrict I).IsSemistable ↔
      ∀ x (hx : I.left < x) (_ : x ≤ I.right), μ ⟨I.left, x, hx⟩ ≤ μ I := by
  rw [isSemistable_iff]
  constructor
  · intro h x hx hxr
    exact h ⟨x, hx.le, hxr⟩ hx
  · intro h x hx
    exact h x.val hx x.property.2

omit [BoundedOrder L] in
/-- A semistable interval's game value is its actual slope-like payoff. -/
lemma A_eq_of_isSemistable (I : StrictIntvl L) (h : (μ.restrict I).IsSemistable) :
    μ.A I = μ I := by
  have hmax : (μ.restrict I).max ⊤ = (μ.restrict I) ⊤ := le_antisymm
    (PayoffFunction.max_le fun x hx => (isSemistable_iff (μ.restrict I)).mp h x hx.1)
    PayoffFunction.apply_le_max
  have hmin := PayoffFunction.min_top_eq_apply_iff.mpr
    (PayoffFunction.max_top_eq_apply_iff.mp hmax)
  rw [(inferInstance : (μ.restrict I).IsSlopeLike).min_eq_A] at hmin
  simpa only [PayoffFunction.A_restrict_apply, PayoffFunction.restrict_apply,
    StrictIntvl.ofSub_top] using hmin

/-- A breakpoint attains the supremum of all initial-interval slopes. -/
theorem max_top_eq_of_isBreakpoint [Nontrivial L] {x : L}
    (hx : μ.IsBreakpoint ⊤ x) : μ.max ⊤ = μ ⟨⊥, x, hx.left_lt⟩ := by
  let : μ.StrongDCC := ⟨fun f hf => False.elim (not_strictAnti_of_wellFoundedLT f hf)⟩
  have hA := A_eq_of_isSemistable μ _ hx.isSemistable_restrict
  apply le_antisymm
  · rw [← PayoffFunction.B_top_eq_max_top]
    apply PayoffFunction.B_le
    intro y hy
    rw [(inferInstance : μ.IsSlopeLike).min_eq_A]
    exact (le_of_not_gt (hx.not_lt y ⟨hy.1.le, hy.2⟩ hy.1.ne)).trans_eq hA
  · exact PayoffFunction.le_max ⟨hx.left_lt, le_top⟩

end BostConjecture.Slope
