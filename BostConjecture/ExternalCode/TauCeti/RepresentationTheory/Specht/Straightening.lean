/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-
Adapted from TauCeti at b3b0334ab9203d9faee4b2f34cd75161463ecdd0.
Replaced the categorical tabloid model by the existing integral word model.
See CONTRIBUTIONS.md for source paths and modifications.
-/
module

public import BostConjecture.ExternalCode.TauCeti.RepresentationTheory.Specht.Garnir
public import BostConjecture.ExternalCode.TauCeti.RepresentationTheory.Specht.GarnirSets
public import BostConjecture.Specht.Tableau.Standard

/-!
# Rational straightening of word polytabloids

Garnir cancellation and an increasing bounded tableau weight express every
polytabloid as a rational combination of standard ones.

## Source

Adapted from <https://github.com/TauCetiProject/TauCeti>, revision
`b3b0334ab9203d9faee4b2f34cd75161463ecdd0`.
Original source:
* `TauCeti.RepresentationTheory.Symmetric.Specht.Straightening`.

The original declaration namespaces and license notices are retained, except for
project-specific adaptations documented in the project contribution records.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Specht

open OAI.Saxl

section FiniteSums

variable {α M : Type*} [AddCommMonoid M] [Preorder M] [AddLeftStrictMono M]

/-- **A set whose weights are all smaller than those of a second set of the same size has the
smaller sum.** The two sets have the same size, so some bijection matches them up, and along it
every weight of the first set is smaller than the weight of its partner. -/
private theorem sum_lt_sum_of_forall_lt (f : α → M) {U V : Finset α}
    (hcard : V.card = U.card) (hU : U.Nonempty) (hlt : ∀ u ∈ U, ∀ v ∈ V, f v < f u) :
    ∑ v ∈ V, f v < ∑ u ∈ U, f u := by
  classical
  induction hU using Finset.Nonempty.cons_induction generalizing V with
  | singleton u =>
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp (by simpa using hcard)
    simpa using hlt u (by simp) v (by simp)
  | cons u U hu _ ih =>
    -- pair `u` off against any label of `V`, and compare the two remaining sums
    obtain ⟨v, hv⟩ : V.Nonempty := Finset.card_pos.mp (by simp [hcard])
    have hcard' : (V.erase v).card = U.card := by
      rw [Finset.card_erase_of_mem hv, hcard, Finset.card_cons]
      simp
    calc ∑ z ∈ V, f z
        = f v + ∑ z ∈ V.erase v, f z := (Finset.add_sum_erase _ f hv).symm
      _ < f u + ∑ z ∈ U, f z :=
          add_lt_add (hlt u (Finset.mem_cons_self _ _) v hv)
            (ih hcard' fun a ha b hb =>
              hlt a (Finset.mem_cons_of_mem ha) b (Finset.mem_of_mem_erase hb))
      _ = ∑ z ∈ Finset.cons u U hu, f z := (Finset.sum_cons _).symm

/-- **A permutation of a set that does not preserve a prescribed part increases the sum over the
other part.** If every weight of `A` exceeds every weight of `X \ A`, and `σ` permutes `X` without
mapping `A` to itself, then `σ` moves some point of `A` into the image of `X \ A`, exchanging a
point for one of strictly larger weight, so that image has the larger sum. -/
private theorem sum_lt_sum_image_sdiff [DecidableEq α] (f : α → M) {X A : Finset α}
    {σ : Equiv.Perm α} (hAX : A ⊆ X) (hXimg : X.image σ = X) (himg : A.image σ ≠ A)
    (hlt : ∀ a ∈ A, ∀ b ∈ X \ A, f b < f a) :
    ∑ z ∈ X \ A, f z < ∑ z ∈ (X \ A).image σ, f z := by
  classical
  have hmemX : ∀ k ∈ X, σ k ∈ X := fun k hk => hXimg ▸ Finset.mem_image_of_mem σ hk
  have hXA : X \ (X \ A) = A := Finset.sdiff_sdiff_eq_self hAX
  have hcard : ((X \ A).image σ).card = (X \ A).card :=
    Finset.card_image_of_injective _ σ.injective
  have hBsub : (X \ A).image σ ⊆ X := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
    exact hmemX k (Finset.sdiff_subset hk)
  -- the image of the second part is not the second part again, since `A` is not preserved
  have hne : (X \ A).image σ ≠ X \ A := by
    intro heq
    refine himg (Finset.eq_of_subset_of_card_le (fun z hz => ?_)
      (le_of_eq (Finset.card_image_of_injective _ σ.injective).symm))
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
    have hnot : σ k ∉ X \ A := by
      intro hcontra
      have himg' : σ k ∈ (X \ A).image σ := heq.symm ▸ hcontra
      obtain ⟨k', hk', hk'eq⟩ := Finset.mem_image.mp himg'
      exact (Finset.mem_sdiff.mp hk').2 (σ.injective hk'eq ▸ hk)
    have hmem := Finset.mem_sdiff.mpr ⟨hmemX k (hAX hk), hnot⟩
    rwa [hXA] at hmem
  -- so the two differ, and what the image gains lies in `A`, above everything it loses
  have hUV := Finset.card_sdiff_comm hcard
  have hUne : (((X \ A).image σ) \ (X \ A)).Nonempty := by
    rw [Finset.sdiff_nonempty]
    exact fun hsub => hne (Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm))
  have hUlt : ∀ u ∈ ((X \ A).image σ) \ (X \ A), ∀ v ∈ (X \ A) \ ((X \ A).image σ), f v < f u := by
    intro u hu v hv
    obtain ⟨huX, huB⟩ := Finset.mem_sdiff.mp hu
    refine hlt u ?_ v (Finset.mem_sdiff.mp hv).1
    have hmem := Finset.mem_sdiff.mpr ⟨hBsub huX, huB⟩
    rwa [hXA] at hmem
  have hlt' := sum_lt_sum_of_forall_lt f hUV.symm hUne hUlt
  -- the two sums agree on the common part, so the two differences compare them
  have h1 := Finset.sum_sdiff (s₁ := (X \ A) ∩ ((X \ A).image σ))
    (s₂ := X \ A) (f := f) Finset.inter_subset_left
  rw [Finset.sdiff_inter_self_left] at h1
  have h2 := Finset.sum_sdiff (s₁ := ((X \ A).image σ) ∩ (X \ A))
    (s₂ := (X \ A).image σ) (f := f) Finset.inter_subset_left
  rw [Finset.sdiff_inter_self_left, Finset.inter_comm] at h2
  calc ∑ z ∈ X \ A, f z
      = (∑ z ∈ (X \ A) \ ((X \ A).image σ), f z) +
        ∑ z ∈ (X \ A) ∩ ((X \ A).image σ), f z := h1.symm
    _ < (∑ z ∈ ((X \ A).image σ) \ (X \ A), f z) +
        ∑ z ∈ (X \ A) ∩ ((X \ A).image σ), f z := by gcongr
    _ = ∑ z ∈ (X \ A).image σ, f z := h2

/-- **Transposing two indices of a sum trades two diagonal terms for off-diagonal ones.** Every
term other than those at `x` and `y` is unchanged, so adding `F x x + F y y` to the transposed sum
gives the original sum with `F x y + F y x` added. -/
private theorem sum_swap_apply_add {ι M : Type*} [DecidableEq ι] [AddCommMonoid M] (F : ι → ι → M)
    {s : Finset ι} {x y : ι} (hx : x ∈ s) (hy : y ∈ s) :
    (∑ k ∈ s, F k (Equiv.swap x y k)) + (F x x + F y y) =
      (∑ k ∈ s, F k k) + (F x y + F y x) := by
  obtain rfl | hne := eq_or_ne x y
  · simp
  have hy' : y ∈ s.erase x := Finset.mem_erase.2 ⟨hne.symm, hy⟩
  -- Split off the terms at `x` and `y`, for an arbitrary summand.
  have split (G : ι → M) : ∑ k ∈ s, G k = G x + (G y + ∑ k ∈ (s.erase x).erase y, G k) := by
    rw [Finset.add_sum_erase _ _ hy', Finset.add_sum_erase _ _ hx]
  -- Away from `x` and `y` the transposition acts trivially.
  have rest : ∑ k ∈ (s.erase x).erase y, F k (Equiv.swap x y k) =
      ∑ k ∈ (s.erase x).erase y, F k k :=
    Finset.sum_congr rfl fun k hk => by
      rw [Equiv.swap_apply_of_ne_of_ne (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk))
        (Finset.ne_of_mem_erase hk)]
  rw [split fun k => F k (Equiv.swap x y k), split fun k => F k k, rest,
    Equiv.swap_apply_left, Equiv.swap_apply_right]
  abel

end FiniteSums

variable {n : ℕ} {μ : YoungDiagram}

/-- The column moment of a tableau: every label weighted by the index of its column.  A Garnir
step at a row inversion increases it, because it moves the small labels of the Garnir set into the
earlier of the two columns the set straddles. -/
private def colMoment (t : Tableau n μ) : ℕ := ∑ k : Fin n, colIndex t k * (k : ℕ)

/-- The row moment of a tableau: every label weighted by the index of its row.  Exchanging two
labels of one column into increasing order increases it, and leaves the column moment alone. -/
private def rowMoment (t : Tableau n μ) : ℕ := ∑ k : Fin n, rowIndex t k * (k : ℕ)

/-- The measure both steps of the straightening algorithm increase: the column moment, weighted
heavily enough that a gain in it outweighs any loss of row moment, plus the row moment. -/
private def straightWeight (t : Tableau n μ) : ℕ :=
  (n ^ 3 + 1) * colMoment t + rowMoment t

/-- A bound for `straightWeight`, which is what makes the straightening algorithm terminate. -/
private def straightBound (n : ℕ) : ℕ := (n ^ 3 + 1) * n ^ 3 + n ^ 3

private theorem tableau_card (t : Tableau n μ) : μ.card = n := by
  simpa using (Fintype.card_congr t).symm

private theorem rowIndex_le_card (t : Tableau n μ) (k : Fin n) :
    rowIndex t k ≤ n := by
  have h := YoungDiagram.mem_iff_lt_colLen.mp (rowIndex_colIndex_mem t k)
  have hc : μ.colLen (colIndex t k) ≤ μ.card := by
    rw [YoungDiagram.colLen_eq_card]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  rw [tableau_card t] at hc
  exact h.le.trans hc

private theorem colIndex_le_card (t : Tableau n μ) (k : Fin n) :
    colIndex t k ≤ n := by
  have h := YoungDiagram.mem_iff_lt_rowLen.mp (rowIndex_colIndex_mem t k)
  have hc : μ.rowLen (rowIndex t k) ≤ μ.card := by
    rw [YoungDiagram.rowLen_eq_card]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  rw [tableau_card t] at hc
  exact h.le.trans hc

private theorem colMoment_le (t : Tableau n μ) : colMoment t ≤ n ^ 3 :=
  calc colMoment t ≤ ∑ _k : Fin n, n * n :=
        Finset.sum_le_sum fun k _ => Nat.mul_le_mul (colIndex_le_card t k) (le_of_lt k.isLt)
    _ = n * (n * n) := by simp
    _ = n ^ 3 := by ring

private theorem rowMoment_le (t : Tableau n μ) : rowMoment t ≤ n ^ 3 :=
  calc rowMoment t ≤ ∑ _k : Fin n, n * n :=
        Finset.sum_le_sum fun k _ => Nat.mul_le_mul (rowIndex_le_card t k) (le_of_lt k.isLt)
    _ = n * (n * n) := by simp
    _ = n ^ 3 := by ring

private theorem straightWeight_le (t : Tableau n μ) : straightWeight t ≤ straightBound n :=
  Nat.add_le_add (Nat.mul_le_mul le_rfl (colMoment_le t)) (rowMoment_le t)

private theorem colMoment_relabel (σ : Equiv.Perm (Fin n)) (t : Tableau n μ) :
    colMoment (relabel σ t) = ∑ k : Fin n, colIndex t k * ((σ k : Fin n) : ℕ) := by
  rw [colMoment]
  simp only [colIndex_relabel]
  rw [← Equiv.sum_comp σ fun k => colIndex t (σ⁻¹ k) * (k : ℕ)]
  simp

private theorem rowMoment_relabel (σ : Equiv.Perm (Fin n)) (t : Tableau n μ) :
    rowMoment (relabel σ t) = ∑ k : Fin n, rowIndex t k * ((σ k : Fin n) : ℕ) := by
  rw [rowMoment]
  simp only [rowIndex_relabel]
  rw [← Equiv.sum_comp σ fun k => rowIndex t (σ⁻¹ k) * (k : ℕ)]
  simp

private theorem straightWeight_lt_of_colMoment_lt {t t' : Tableau n μ}
    (h : colMoment t < colMoment t') : straightWeight t < straightWeight t' :=
  calc straightWeight t = (n ^ 3 + 1) * colMoment t + rowMoment t := rfl
    _ < (n ^ 3 + 1) * colMoment t + (n ^ 3 + 1) :=
        Nat.add_lt_add_left (Nat.lt_succ_of_le (rowMoment_le t)) _
    _ = (n ^ 3 + 1) * (colMoment t + 1) := (Nat.mul_succ _ _).symm
    _ ≤ (n ^ 3 + 1) * colMoment t' := Nat.mul_le_mul le_rfl h
    _ ≤ straightWeight t' := Nat.le_add_right _ _

/-!
## Exchanging two labels of one column -/

/-- **Exchanging two labels of one column that are out of order increases the straightening
measure.**  The exchange leaves every label in its own column, so the column moment is unchanged,
while the smaller of the two labels moves to the earlier row and the row moment grows. -/
private theorem straightWeight_lt_of_swap {t : Tableau n μ} {x y : Fin n}
    (hcol : colIndex t x = colIndex t y) (hrow : rowIndex t x < rowIndex t y) (hyx : y < x) :
    straightWeight t < straightWeight (relabel (Equiv.swap x y) t) := by
  have hc := sum_swap_apply_add (fun k l => colIndex t k * (l : ℕ)) (Finset.mem_univ x)
    (Finset.mem_univ y)
  have hr := sum_swap_apply_add (fun k l => rowIndex t k * (l : ℕ)) (Finset.mem_univ x)
    (Finset.mem_univ y)
  rw [hcol] at hc
  have hcol' : colMoment (relabel (Equiv.swap x y) t) = colMoment t := by
    rw [colMoment_relabel, colMoment]
    refine Nat.add_right_cancel (m := colIndex t y * (x : ℕ) + colIndex t y * (y : ℕ)) ?_
    rw [hc]
    ring
  have hrow' : rowMoment t < rowMoment (relabel (Equiv.swap x y) t) := by
    rw [rowMoment_relabel]
    have hstep : rowMoment t + (rowIndex t x * (x : ℕ) + rowIndex t y * (y : ℕ)) <
        rowMoment t + (rowIndex t x * (y : ℕ) + rowIndex t y * (x : ℕ)) :=
      Nat.add_lt_add_left (mul_add_mul_lt_mul_add_mul hrow (Fin.lt_def.mp hyx)) _
    rw [rowMoment, ← hr] at hstep
    exact lt_of_add_lt_add_right hstep
  simpa only [straightWeight, straightWeight, hcol'] using Nat.add_lt_add_left hrow' _

/-!
## The Garnir step increases the measure -/

/-- **The left half of a Garnir set carries larger labels than the right half**, at a cell where
the columns of `t` increase but its rows do not.  The left half sits in column `j` weakly below
row `i`, so its labels are at least the label at `(i, j)`; the right half sits in column `j + 1`
weakly above row `i`, so its labels are at most the label at `(i, j + 1)`; and the row inversion
puts the second of those below the first. -/
private theorem lt_of_mem_garnirSet {t : Tableau n μ} {i j : ℕ} {x y : Fin n}
    (hinc : ∀ p q : Fin n, colIndex t p = colIndex t q → rowIndex t p < rowIndex t q → p < q)
    (hxr : rowIndex t x = i) (hxc : colIndex t x = j) (hyr : rowIndex t y = i)
    (hyc : colIndex t y = j + 1) (hyx : y < x) {a b : Fin n}
    (ha : a ∈ garnirSetLeft t i j) (hb : b ∈ garnirSet t i j \ garnirSetLeft t i j) :
    b < a := by
  obtain ⟨hac, hai⟩ := mem_garnirSetLeft.mp ha
  obtain ⟨hbmem, hbnot⟩ := Finset.mem_sdiff.mp hb
  have hbc : colIndex t b = j + 1 :=
    colIndex_eq_of_mem_garnirSet_of_notMem_garnirSetLeft hbmem hbnot
  have hbi : rowIndex t b ≤ i := by
    rcases mem_garnirSet.mp hbmem with h | h
    · omega
    · exact h.2
  have hxa : x ≤ a := by
    rcases eq_or_lt_of_le hai with h | h
    · exact le_of_eq (rowIndex_colIndex_injective t (Prod.ext (hxr.trans h) (hxc.trans hac.symm)))
    · exact le_of_lt (hinc x a (by rw [hxc, hac]) (by omega))
  have hby : b ≤ y := by
    rcases eq_or_lt_of_le hbi with h | h
    · exact le_of_eq
        (rowIndex_colIndex_injective t (Prod.ext (h.trans hyr.symm) (hbc.trans hyc.symm)))
    · exact le_of_lt (hinc b y (by rw [hbc, hyc]) (by omega))
  exact lt_of_le_of_lt hby (lt_of_lt_of_le hyx hxa)

/-- Summing over a Garnir set against the column index only sees which of its two halves a label
lies in: the left half contributes the weight `j` and the right half the weight `j + 1`. -/
private theorem sum_colIndex_garnirSet (t : Tableau n μ) (i j : ℕ) (g : Fin n → ℕ) :
    ∑ k ∈ garnirSet t i j, colIndex t k * g k =
      j * (∑ k ∈ garnirSet t i j, g k) + ∑ k ∈ garnirSet t i j \ garnirSetLeft t i j, g k := by
  classical
  have hAX : garnirSetLeft t i j ⊆ garnirSet t i j := garnirSetLeft_subset_garnirSet t i j
  have hBc : ∀ k ∈ garnirSet t i j \ garnirSetLeft t i j,
      colIndex t k * g k = (j + 1) * g k := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_sdiff.mp hk
    rw [colIndex_eq_of_mem_garnirSet_of_notMem_garnirSetLeft hk1 hk2]
  have hAc : ∀ k ∈ garnirSetLeft t i j, colIndex t k * g k = j * g k := fun k hk => by
    rw [(mem_garnirSetLeft.mp hk).1]
  rw [← Finset.sum_sdiff hAX, ← Finset.sum_sdiff (f := g) hAX, Finset.sum_congr rfl hBc,
    Finset.sum_congr rfl hAc, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- **A Garnir permutation that does not preserve the columns increases the column moment.**  It
exchanges labels of the left half of the Garnir set for labels of the right half; the latter are
the smaller ones, and they move into the earlier column. -/
private theorem colMoment_lt_of_garnir {t : Tableau n μ} {i j : ℕ}
    {σ : Equiv.Perm (Fin n)} (hfix : ∀ k ∉ garnirSet t i j, σ k = k)
    (himg : (garnirSetLeft t i j).image σ ≠ garnirSetLeft t i j)
    (hlt : ∀ a ∈ garnirSetLeft t i j, ∀ b ∈ garnirSet t i j \ garnirSetLeft t i j,
      (b : ℕ) < (a : ℕ)) :
    colMoment t < colMoment (relabel σ t) := by
  classical
  have hAX : garnirSetLeft t i j ⊆ garnirSet t i j := garnirSetLeft_subset_garnirSet t i j
  -- `σ` permutes the Garnir set, since it fixes everything outside it
  have hmemX : ∀ k ∈ garnirSet t i j, σ k ∈ garnirSet t i j := by
    intro k hk
    by_contra hnot
    have heq : σ k = k := σ.injective (hfix _ hnot)
    rw [heq] at hnot
    exact hnot hk
  have hXimg : (garnirSet t i j).image σ = garnirSet t i j :=
    Finset.eq_of_subset_of_card_le
      (fun z hz => by obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz; exact hmemX k hk)
      (le_of_eq (Finset.card_image_of_injective _ σ.injective).symm)
  -- the labels outside the Garnir set contribute the same to both moments
  have hout : ∀ k ∈ (garnirSet t i j)ᶜ,
      colIndex t k * ((σ k : Fin n) : ℕ) = colIndex t k * (k : ℕ) :=
    fun k hk => by rw [hfix k (Finset.mem_compl.mp hk)]
  have hsum : ∀ g : Fin n → ℕ,
      ∑ k : Fin n, colIndex t k * g k =
        (∑ k ∈ garnirSet t i j, colIndex t k * g k) +
          ∑ k ∈ (garnirSet t i j)ᶜ, colIndex t k * g k :=
    fun g => (Finset.sum_add_sum_compl _ _).symm
  have himage : ∑ k ∈ garnirSet t i j \ garnirSetLeft t i j, ((σ k : Fin n) : ℕ) =
      ∑ z ∈ (garnirSet t i j \ garnirSetLeft t i j).image σ, (z : ℕ) :=
    (Finset.sum_image fun x _ y _ hxy => σ.injective hxy).symm
  have hfull : ∑ k ∈ garnirSet t i j, ((σ k : Fin n) : ℕ) =
      ∑ k ∈ garnirSet t i j, (k : ℕ) := by
    have h : ∑ z ∈ (garnirSet t i j).image σ, (z : ℕ) =
        ∑ k ∈ garnirSet t i j, ((σ k : Fin n) : ℕ) :=
      Finset.sum_image fun x _ y _ hxy => σ.injective hxy
    simpa only [hXimg] using h.symm
  -- so the two moments differ only in the sum over the right half of the Garnir set
  have hkey := sum_lt_sum_image_sdiff Fin.val hAX hXimg himg hlt
  rw [colMoment_relabel, colMoment, hsum fun k => ((σ k : Fin n) : ℕ),
    hsum fun k => (k : ℕ), Finset.sum_congr rfl hout,
    sum_colIndex_garnirSet t i j fun k => ((σ k : Fin n) : ℕ),
    sum_colIndex_garnirSet t i j fun k => (k : ℕ), hfull, himage]
  omega

/-!
## The straightening algorithm -/

/-- **A row inversion produces one between adjacent columns.**  Walking rightwards from the
earlier of the two cells, the first step at which the label drops is such an inversion. -/
private theorem exists_adjacent_row_inversion (t : Tableau n μ) :
    ∀ (m : ℕ) (x y : Fin n), colIndex t y - colIndex t x ≤ m →
      rowIndex t x = rowIndex t y → colIndex t x < colIndex t y → y < x →
      ∃ u v : Fin n,
        rowIndex t u = rowIndex t v ∧ colIndex t v = colIndex t u + 1 ∧ v < u := by
  intro m
  induction m with
  | zero =>
    intro x y hn _ hcol _
    omega
  | succ n ih =>
    intro x y hn hrow hcol hyx
    by_cases hadj : colIndex t y = colIndex t x + 1
    · exact ⟨x, y, hrow, hadj, hyx⟩
    · have hmem : (rowIndex t x, colIndex t x + 1) ∈ μ := by
        have hcell : (rowIndex t x, colIndex t y) ∈ μ := by
          simpa only [hrow] using rowIndex_colIndex_mem t y
        exact μ.up_left_mem le_rfl (by omega) hcell
      obtain ⟨z, hzr, hzc⟩ := exists_rowIndex_colIndex t hmem
      rcases lt_trichotomy z x with hzx | hzx | hzx
      · exact ⟨x, z, hzr.symm, hzc, hzx⟩
      · exact absurd hzc (by rw [hzx]; omega)
      · refine ih z y ?_ (by rw [hzr, hrow]) ?_ (hyx.trans hzx)
        · omega
        · omega

/-- At a Garnir set, only permutations exchanging the two column halves are needed. -/
theorem polytabloid_mem_span_polytabloid_relabel_garnirSet (t : Tableau n μ) {i j : ℕ}
    (h : (i, j + 1) ∈ μ) :
    polytabloidRat t ∈ Submodule.span ℚ
      ((fun σ => polytabloidRat (relabel σ t)) ''
        {σ : Equiv.Perm (Fin n) | (∀ k ∉ garnirSet t i j, σ k = k) ∧
          (garnirSetLeft t i j).image σ ≠ garnirSetLeft t i j}) := by
  have hindex : {σ : Equiv.Perm (Fin n) | (∀ k ∉ garnirSet t i j, σ k = k) ∧
        σ ∉ columnGroup t} =
      {σ : Equiv.Perm (Fin n) | (∀ k ∉ garnirSet t i j, σ k = k) ∧
        (garnirSetLeft t i j).image σ ≠ garnirSetLeft t i j} := by
    ext σ
    exact and_congr_right fun hσ => not_congr (mem_columnGroup_iff_image_garnirSetLeft_eq hσ)
  simpa only [← hindex] using polytabloidRat_mem_span_relabel t
    (fun _ hk => colLen_colIndex_le_colLen_of_mem_garnirSet hk)
    (by rw [card_garnirSet t h]; exact Nat.lt_succ_self _)

/-- **A tableau that is not standard has its polytabloid in the span of heavier ones.**  If two
labels of one column are out of order, exchanging them is a column permutation, which changes the
polytabloid only by its sign; otherwise the rows fail to increase somewhere, and the Garnir
relation at that cell rewrites the polytabloid in terms of the relabelings that move a label
between the two columns concerned. -/
private theorem polytabloid_mem_span_of_lt (t : Tableau n μ)
    (hns : ¬ ((∀ x y : Fin n,
          colIndex t x = colIndex t y → rowIndex t x < rowIndex t y → x < y) ∧
        ∀ x y : Fin n, rowIndex t x = rowIndex t y → colIndex t x < colIndex t y → x < y)) :
    polytabloidRat t ∈ Submodule.span ℚ
      {v | ∃ t' : Tableau n μ, straightWeight t < straightWeight t' ∧ v = polytabloidRat t'} := by
  classical
  by_cases hinc : ∀ x y : Fin n,
      colIndex t x = colIndex t y → rowIndex t x < rowIndex t y → x < y
  · -- the columns of `t` increase, so a row of `t` is out of order
    have hrowfail : ¬ ∀ x y : Fin n,
        rowIndex t x = rowIndex t y → colIndex t x < colIndex t y → x < y :=
      fun h => hns ⟨hinc, h⟩
    push Not at hrowfail
    obtain ⟨x, y, hrow, hcol, hyx⟩ := hrowfail
    have hne : x ≠ y := fun h => absurd (congrArg (colIndex t) h) hcol.ne
    obtain ⟨u, v, huv, hadj, hvu⟩ := exists_adjacent_row_inversion t _ x y le_rfl hrow hcol
      (lt_of_le_of_ne hyx (Ne.symm hne))
    have hcell : (rowIndex t u, colIndex t u + 1) ∈ μ := by
      have h := rowIndex_colIndex_mem t v
      rwa [← huv, hadj] at h
    refine (Submodule.span_le.mpr ?_)
      (polytabloid_mem_span_polytabloid_relabel_garnirSet t hcell)
    rintro _ ⟨σ, ⟨hfix, himg⟩, rfl⟩
    refine Submodule.subset_span ⟨relabel σ t, ?_, rfl⟩
    refine straightWeight_lt_of_colMoment_lt (colMoment_lt_of_garnir hfix himg fun a ha b hb => ?_)
    exact Fin.lt_def.mp (lt_of_mem_garnirSet hinc rfl rfl huv.symm hadj hvu ha hb)
  · -- a column of `t` is out of order
    push Not at hinc
    obtain ⟨x, y, hcol, hrow, hyx⟩ := hinc
    have hne : x ≠ y := fun h => absurd (congrArg (rowIndex t) h) hrow.ne
    have hswap : Equiv.swap x y ∈ columnGroup t := by
      change ∀ k, colIndex t (Equiv.swap x y k) = colIndex t k
      intro k
      rcases eq_or_ne k x with rfl | hkx
      · rw [Equiv.swap_apply_left, hcol]
      rcases eq_or_ne k y with rfl | hky
      · rw [Equiv.swap_apply_right, hcol]
      · rw [Equiv.swap_apply_of_ne_of_ne hkx hky]
    have hsign : polytabloidRat (relabel (Equiv.swap x y) t) = -polytabloidRat t := by
      rw [polytabloidRat_relabel_of_mem_columnGroup t hswap, Equiv.Perm.sign_swap hne]
      simp
    have hmem : polytabloidRat (relabel (Equiv.swap x y) t) ∈ Submodule.span ℚ
        {v | ∃ t' : Tableau n μ,
          straightWeight t < straightWeight t' ∧ v = polytabloidRat t'} :=
      Submodule.subset_span
        ⟨_, straightWeight_lt_of_swap hcol hrow (lt_of_le_of_ne hyx (Ne.symm hne)), rfl⟩
    rw [hsign] at hmem
    simpa using neg_mem hmem

/-- **The straightening algorithm**: every polytabloid is a rational combination of the
polytabloids of the standard tableaux of the same shape.  The straightening measure increases at
every rewriting step and is bounded, so the rewriting terminates, and it terminates only at a
tableau increasing down its columns and along its rows. -/
theorem polytabloidRat_mem_span_standard (t : Tableau n μ) :
    polytabloidRat t ∈ Submodule.span ℚ
      (Set.range fun T : {t : Tableau n μ // IsStandard t} => polytabloidRat T.val) := by
  classical
  suffices H : ∀ (N : ℕ) (t : Tableau n μ), straightBound n - straightWeight t ≤ N →
      polytabloidRat t ∈ Submodule.span ℚ
        (Set.range fun T : {t : Tableau n μ // IsStandard t} => polytabloidRat T.val) from
    H _ t le_rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro t ht
    by_cases hstd : (∀ x y : Fin n,
          colIndex t x = colIndex t y → rowIndex t x < rowIndex t y → x < y) ∧
        ∀ x y : Fin n, rowIndex t x = rowIndex t y → colIndex t x < colIndex t y → x < y
    · exact Submodule.subset_span ⟨⟨t, ⟨hstd.2⟩, ⟨hstd.1⟩⟩, rfl⟩
    · refine (Submodule.span_le.mpr ?_) (polytabloid_mem_span_of_lt t hstd)
      rintro _ ⟨t', hlt, rfl⟩
      refine ih (straightBound n - straightWeight t') ?_ t' le_rfl
      exact lt_of_lt_of_le
        (Nat.sub_lt_sub_left (lt_of_lt_of_le hlt (straightWeight_le t')) hlt) ht

end BostConjecture.Specht
