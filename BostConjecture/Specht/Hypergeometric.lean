module

public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Basic.Real.Basic

/-!
# Labelled occupancy counting

Intersecting a subset of labelled blocks with each block gives the
multivariate hypergeometric law used in the rectangular prefix distribution.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Specht

open Finset

/-- Occupancies of `a` labelled blocks of size `M`, with total `A`. -/
abbrev Occupancy (a M A : ℕ) := {b : Fin a → Fin (M + 1) // ∑ i, (b i).val = A}

/-- Intersection with one labelled block, expressed in its own coordinates. -/
def blockFiber {a M : ℕ} (s : Finset (Fin a × Fin M)) (i : Fin a) : Finset (Fin M) :=
  univ.filter fun j => (i, j) ∈ s

@[simp] theorem mem_blockFiber {a M : ℕ} (s : Finset (Fin a × Fin M))
    (i : Fin a) (j : Fin M) : j ∈ blockFiber s i ↔ (i, j) ∈ s := by
  simp [blockFiber]

theorem sum_card_blockFiber {a M : ℕ} (s : Finset (Fin a × Fin M)) :
    ∑ i, (blockFiber s i).card = s.card := by
  have hf (i : Fin a) : (blockFiber s i).card = (s.filter fun p => p.1 = i).card := by
    apply card_bij (fun j _ => (i, j))
    · intro j hj
      simp only [mem_filter, mem_blockFiber] at *
      exact ⟨hj, trivial⟩
    · intro j _ l _ h
      exact (Prod.mk.inj h).2
    · intro p hp
      obtain ⟨hp, he⟩ := mem_filter.mp hp
      refine ⟨p.2, ?_, ?_⟩
      · simpa only [mem_blockFiber, ← he] using hp
      · exact Prod.ext he.symm rfl
  simp_rw [hf]
  simpa using sum_card_fiberwise_eq_card_filter s univ Prod.fst

/-- A subset is exactly a tuple of subsets of its blocks, grouped by occupancy. -/
def occupancyEquiv (a M A : ℕ) :
    {s : Finset (Fin a × Fin M) // s.card = A} ≃
      Σ b : Occupancy a M A, (i : Fin a) → {u : Finset (Fin M) // u.card = (b.val i).val} where
  toFun s := ⟨⟨fun i => ⟨(blockFiber s.val i).card, by
      have := card_le_univ (blockFiber s.val i)
      simpa using Nat.lt_succ_of_le this⟩,
      (sum_card_blockFiber s.val).trans s.property⟩,
    fun i => ⟨blockFiber s.val i, rfl⟩⟩
  invFun x := ⟨univ.filter fun p => p.2 ∈ (x.2 p.1).val, by
    rw [← sum_card_blockFiber]
    have hf (i : Fin a) :
        blockFiber (univ.filter fun p : Fin a × Fin M => p.2 ∈ (x.2 p.1).val) i =
          (x.2 i).val := by ext j; simp
    simp_rw [hf, (x.2 _).property]
    exact x.1.property⟩
  left_inv s := by
    apply Subtype.ext
    ext p
    simp
  right_inv x := by
    rcases x with ⟨b, u⟩
    dsimp
    have hf (i : Fin a) :
        blockFiber (univ.filter fun p : Fin a × Fin M => p.2 ∈ (u p.1).val) i =
          (u i).val := by ext j; simp
    apply Sigma.ext
    · apply Subtype.ext
      funext i
      apply Fin.ext
      exact (congrArg Finset.card (hf i)).trans (u i).property
    · apply Function.hfunext rfl
      intro i j hij
      have hij' : i = j := eq_of_heq hij
      subst j
      apply (Subtype.heq_iff_coe_eq (fun s => ?_)).mpr (hf i)
      dsimp only
      rw [hf, (u i).property]

/-- The multivariate Vandermonde identity, by counting actual subsets. -/
theorem sum_occupancy_choose (a M A : ℕ) :
    ∑ b : Occupancy a M A, ∏ i, M.choose (b.val i).val = (a * M).choose A := by
  have h := Fintype.card_congr (occupancyEquiv a M A)
  simpa only [Fintype.card_sigma, Fintype.card_pi, Fintype.card_finset_len,
    Fintype.card_prod, Fintype.card_fin] using h.symm

/-- Probability mass of the labelled multivariate hypergeometric law. -/
def occupancyMass {a M A : ℕ} (b : Occupancy a M A) : ℝ :=
  (∏ i, (M.choose (b.val i).val : ℝ)) / ((a * M).choose A : ℝ)

theorem occupancyMass_nonneg {a M A : ℕ} (b : Occupancy a M A) :
    0 ≤ occupancyMass b := by
  unfold occupancyMass
  apply div_nonneg _ (Nat.cast_nonneg _)
  exact_mod_cast Nat.zero_le (∏ i, M.choose (b.val i).val)

/-- Normalization of the labelled law, including the empty sampling case. -/
theorem sum_occupancyMass {a M A : ℕ} (hA : A ≤ a * M) :
    ∑ b : Occupancy a M A, occupancyMass b = 1 := by
  unfold occupancyMass
  rw [← sum_div]
  have h : (∑ b : Occupancy a M A, ∏ i, (M.choose (b.val i).val : ℝ)) =
      ((a * M).choose A : ℝ) := by exact_mod_cast sum_occupancy_choose a M A
  rw [h, div_self]
  exact_mod_cast (Nat.choose_pos hA).ne'

end BostConjecture.Specht
