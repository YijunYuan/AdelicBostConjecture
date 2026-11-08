/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import HarderNarasimhan.PayoffFunction.Slope
public import HarderNarasimhan.PayoffFunction.Convex
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Slopes on finite-dimensional subspace lattices

The degree is a real-valued function on actual subspaces. Interval degrees are
its differences, and interval ranks are differences of dimensions. Thus the
payoff is slope-like for every degree function, and convex when the degree is
supermodular. Specializing to arithmetic degree requires a separate proof of
supermodularity and identification with Hermitian quotient degrees.

The slope-like proof uses Chen–Jeannin §4.3 through Yijun Yuan's pinned
`HarderNarasimhan.PayoffFunction.isSlopeLike_slope` formalization.
-/

@[expose] public section

open HarderNarasimhan
open scoped NNReal

namespace BostConjecture.Subspace

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- Dimension of a strict subspace interval as a nonnegative real. -/
noncomputable def intervalRank (I : StrictIntvl (Submodule K V)) : ℝ≥0 :=
  (Module.finrank K I.right - Module.finrank K I.left : ℕ)

lemma intervalRank_pos (I : StrictIntvl (Submodule K V)) : 0 < intervalRank I := by
  change (0 : ℝ≥0) < (Module.finrank K I.right - Module.finrank K I.left : ℕ)
  exact_mod_cast Nat.sub_pos_of_lt (Submodule.finrank_strictMono I.lt)

/-- The slope payoff of a degree on subspaces, valued in the complete ordered
space of real cuts. -/
noncomputable def slope (degree : Submodule K V → ℝ) :
    PayoffFunction (Submodule K V) (DedekindCut ℝ) :=
  PayoffFunction.slope intervalRank (fun I => degree I.right - degree I.left)

/-- Additivity along a chain gives the seesaw property; no modularity of degree
across incomparable subspaces is assumed. -/
instance slope_isSlopeLike (degree : Submodule K V → ℝ) : (slope degree).IsSlopeLike := by
  apply PayoffFunction.isSlopeLike_slope
  · intro x y z hxy hyz
    simp only
    ring
  · intro x y z hxy hyz
    have h₁ : Module.finrank K x ≤ Module.finrank K y :=
      (Submodule.finrank_strictMono (K := K) hxy).le
    have h₂ : Module.finrank K y ≤ Module.finrank K z :=
      (Submodule.finrank_strictMono (K := K) hyz).le
    simp only [intervalRank]
    exact_mod_cast (show Module.finrank K z - Module.finrank K x =
      (Module.finrank K y - Module.finrank K x) +
        (Module.finrank K z - Module.finrank K y) by omega)
  · intro x y hxy hzero
    exact False.elim ((intervalRank_pos ⟨x, y, hxy⟩).ne' hzero)

/-- Explicit evaluation of a slope; every strict subspace interval has positive rank. -/
lemma slope_apply (degree : Submodule K V → ℝ) (I : StrictIntvl (Submodule K V)) :
    slope degree I = DedekindCut.principal
      ((degree I.right - degree I.left) / (intervalRank I : ℝ)) := by
  simp [slope, PayoffFunction.slope, intervalRank_pos, div_eq_inv_mul, NNReal.smul_def]

/-- Supermodularity of degree gives exactly the convexity inequality needed by
Harder–Narasimhan games. -/
theorem slope_isConvex (degree : Submodule K V → ℝ)
    (hdegree : ∀ x y, degree x + degree y ≤ degree (x ⊓ y) + degree (x ⊔ y)) :
    (slope degree).IsConvex := by
  constructor
  intro x y hxy
  rw [slope_apply, slope_apply, DedekindCut.principal_le_principal]
  have hrank : intervalRank ⟨x ⊓ y, x, inf_lt_left.2 hxy⟩ =
      intervalRank ⟨y, x ⊔ y, right_lt_sup.2 hxy⟩ := by
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq x y
    simp only [intervalRank]
    congr 1
    omega
  rw [hrank]
  apply div_le_div_of_nonneg_right _ (NNReal.coe_nonneg _)
  linarith [hdegree x y]

end BostConjecture.Subspace
