/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Order.Completion
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Real values of bounded Dedekind cuts

A cut between two principal real cuts represents the supremum of its left set.
This conversion is independent of slope functions and HN filtrations.
-/

@[expose] public section

namespace DedekindCut

/-- The real supremum of a cut's left set. Bounds are required to recover the cut. -/
noncomputable def toReal (c : DedekindCut ℝ) : ℝ := sSup c.left

/-- Between principal real bounds, taking the real value preserves the cut. -/
theorem principal_toReal_of_bounds {c : DedekindCut ℝ} {a b : ℝ}
    (ha : principal a ≤ c) (hb : c ≤ principal b) : principal c.toReal = c := by
  have hne : c.left.Nonempty := ⟨a, principal_le_iff.mp ha⟩
  have hbd : BddAbove c.left := ⟨b, left_subset_left_iff.mpr hb⟩
  apply ext'
  rw [right_principal, ← upperBounds_left]
  ext r
  exact csSup_le_iff hbd hne

end DedekindCut
