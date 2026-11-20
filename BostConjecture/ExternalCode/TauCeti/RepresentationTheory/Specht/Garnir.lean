/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-
Adapted from TauCetiProject/TauCeti at b3b0334ab9203d9faee4b2f34cd75161463ecdd0,
RepresentationTheory/Symmetric/Specht/{Garnir,Straightening}.lean.
The categorical tabloid action is replaced by integral word coordinates.
-/
module

public import BostConjecture.Specht.Tableau.Basic

/-!
# Garnir cancellation in integral word coordinates

An antisymmetrizer on more labels than the available rows annihilates each
column-permuted row word. Collecting its internal column permutations then
gives a rational straightening relation.

## Source

Adapted from <https://github.com/TauCetiProject/TauCeti>, revision
`b3b0334ab9203d9faee4b2f34cd75161463ecdd0`.
Original sources:
* `TauCeti.RepresentationTheory.Symmetric.Specht.Garnir`.
* `TauCeti.RepresentationTheory.Symmetric.Specht.Straightening`.

The original declaration namespaces and license notices are retained, except for
project-specific adaptations documented in the project contribution records.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Specht

open OAI.Saxl

variable {n d : ℕ} {μ : YoungDiagram}

/-- Coefficientwise rational extension of the integral polytabloid. -/
def polytabloidRat (t : Tableau n μ) : (Fin n → Fin (μ.colLen 0)) → ℚ :=
  fun w => (polytabloidInt t w : ℚ)

/-- Relabeling inside a column changes a polytabloid by the permutation sign. -/
theorem polytabloidInt_relabel_of_mem_columnGroup (t : Tableau n μ)
    {g : Equiv.Perm (Fin n)} (hg : g ∈ columnGroup t) :
    polytabloidInt (relabel g t) = (Equiv.Perm.sign g : ℤ) • polytabloidInt t := by
  classical
  let := Fintype.ofFinite (columnGroup t)
  let h : columnGroup t := ⟨g, hg⟩
  rw [polytabloidInt_relabel]
  unfold polytabloidInt
  simp only [map_sum, map_smul, Finset.smul_sum]
  symm
  apply (Equiv.sum_comp (Equiv.mulLeft h) _).symm.trans
  apply Finset.sum_congr rfl
  intro q hq
  change (Equiv.Perm.sign g : ℤ) •
    (Equiv.Perm.sign (g * q.val) : ℤ) •
      wordRepInt n (μ.colLen 0) (g * q.val) (Pi.single (rowWord t) 1) = _
  simp only [map_mul, Units.val_mul, smul_smul, Module.End.mul_apply]
  congr 1
  rcases Int.units_eq_one_or (Equiv.Perm.sign g) with hs | hs <;> simp [hs]

theorem polytabloidRat_relabel_of_mem_columnGroup (t : Tableau n μ)
    {g : Equiv.Perm (Fin n)} (hg : g ∈ columnGroup t) :
    polytabloidRat (relabel g t) = ((Equiv.Perm.sign g : ℤ) : ℚ) • polytabloidRat t := by
  ext w
  simp [polytabloidRat, polytabloidInt_relabel_of_mem_columnGroup t hg]

private def antisymmetrizerInt (X : Finset (Fin n)) :
    Module.End ℤ ((Fin n → Fin d) → ℤ) := by
  classical
  exact ∑ σ ∈ {σ : Equiv.Perm (Fin n) | ∀ k ∉ X, σ k = k},
    (Equiv.Perm.sign σ : ℤ) • wordRepInt n d σ

private theorem antisymmetrizerInt_apply_eq_zero (X : Finset (Fin n))
    (v : (Fin n → Fin d) → ℤ) {x y : Fin n} (hx : x ∈ X) (hy : y ∈ X)
    (hxy : x ≠ y) (hv : wordRepInt n d (Equiv.swap x y) v = v) :
    antisymmetrizerInt X v = 0 := by
  classical
  let s := Equiv.swap x y
  have hs : Equiv.Perm.sign s = -1 := Equiv.Perm.sign_swap hxy
  have hsfix : ∀ k ∉ X, s k = k := fun k hk =>
    Equiv.swap_apply_of_ne_of_ne (fun h => hk (h ▸ hx)) (fun h => hk (h ▸ hy))
  unfold antisymmetrizerInt
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  apply Finset.sum_involution (fun σ _ => σ * s)
  · intro σ hσ
    simp only [map_mul, hs, Units.val_neg, mul_neg_one, neg_smul, Module.End.mul_apply]
    change _ + -((Equiv.Perm.sign σ : ℤ) • wordRepInt n d σ
      (wordRepInt n d (Equiv.swap x y) v)) = 0
    rw [hv, add_neg_cancel]
  · intro σ hσ _ he
    have he' : s = 1 := mul_left_cancel (show σ * s = σ * 1 by simpa using he)
    have h := congrArg (fun g : Equiv.Perm (Fin n) => g x) he'
    simp [s] at h
    exact hxy h.symm
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    intro k hk
    simp [Equiv.Perm.mul_apply, hsfix k hk, hσ k hk]
  · intro σ hσ
    simp [s, mul_assoc]

/-- Pigeonhole among rows after a column permutation. -/
theorem exists_rowWord_relabel_eq (t : Tableau n μ) {X : Finset (Fin n)} {r : ℕ}
    (hX : ∀ k ∈ X, μ.colLen (t k).val.2 ≤ r) (hcard : r < X.card)
    (q : columnGroup t) :
    ∃ x ∈ X, ∃ y ∈ X, x ≠ y ∧ rowWord (relabel q.val t) x =
      rowWord (relabel q.val t) y := by
  have hmaps : ∀ k ∈ X, (t (q.val⁻¹ k)).val.1 ∈ Finset.range r := by
    intro k hk
    have hcol := (q⁻¹).property k
    change (t (q.val⁻¹ k)).val.2 = (t k).val.2 at hcol
    have hlt := YoungDiagram.mem_iff_lt_colLen.mp (t (q.val⁻¹ k)).property
    simpa only [Finset.mem_range] using hlt.trans_le (by rw [hcol]; exact hX k hk)
  obtain ⟨x, hx, y, hy, hxy, he⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (by simpa using hcard) hmaps
  exact ⟨x, hx, y, hy, hxy, Fin.ext he⟩

private theorem antisymmetrizerInt_column_word_eq_zero (t : Tableau n μ)
    {X : Finset (Fin n)} {r : ℕ} (hX : ∀ k ∈ X, μ.colLen (t k).val.2 ≤ r)
    (hcard : r < X.card) (q : columnGroup t) :
    antisymmetrizerInt X
      (wordRepInt n (μ.colLen 0) q.val (Pi.single (rowWord t) 1)) = 0 := by
  obtain ⟨x, hx, y, hy, hxy, he⟩ := exists_rowWord_relabel_eq t hX hcard q
  rw [wordRepInt_single]
  apply antisymmetrizerInt_apply_eq_zero X _ hx hy hxy
  rw [wordRepInt_single]
  congr 1
  funext k
  exact Equiv.apply_swap_eq_self he k

open Classical in
/-- The integral Garnir relation for an oversized set of labels. -/
theorem sum_sign_smul_polytabloidInt_relabel_eq_zero (t : Tableau n μ)
    {X : Finset (Fin n)} {r : ℕ} (hX : ∀ k ∈ X, μ.colLen (t k).val.2 ≤ r)
    (hcard : r < X.card) :
    ∑ σ ∈ {σ : Equiv.Perm (Fin n) | ∀ k ∉ X, σ k = k},
      (Equiv.Perm.sign σ : ℤ) • polytabloidInt (relabel σ t) = 0 := by
  classical
  suffices h : antisymmetrizerInt X (polytabloidInt t) = 0 by
    simpa only [antisymmetrizerInt, LinearMap.sum_apply, LinearMap.smul_apply,
      polytabloidInt_relabel] using h
  unfold polytabloidInt
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro q hq
  rw [map_smul, antisymmetrizerInt_column_word_eq_zero t hX hcard q, smul_zero]

open Classical in
/-- The Garnir relation after coefficientwise extension to the rationals. -/
theorem sum_sign_smul_polytabloidRat_relabel_eq_zero (t : Tableau n μ)
    {X : Finset (Fin n)} {r : ℕ} (hX : ∀ k ∈ X, μ.colLen (t k).val.2 ≤ r)
    (hcard : r < X.card) :
    ∑ σ ∈ {σ : Equiv.Perm (Fin n) | ∀ k ∉ X, σ k = k},
      ((Equiv.Perm.sign σ : ℤ) : ℚ) • polytabloidRat (relabel σ t) = 0 := by
  ext w
  have h := congrFun (sum_sign_smul_polytabloidInt_relabel_eq_zero t hX hcard) w
  simpa [polytabloidRat] using congrArg (fun z : ℤ => (z : ℚ)) h

open Classical in
/-- Collecting internal column permutations in the Garnir relation. -/
theorem card_nsmul_polytabloidRat_add_sum_eq_zero (t : Tableau n μ)
    {X : Finset (Fin n)} {r : ℕ} (hX : ∀ k ∈ X, μ.colLen (t k).val.2 ≤ r)
    (hcard : r < X.card) :
    ({σ : Equiv.Perm (Fin n) | (∀ k ∉ X, σ k = k) ∧ σ ∈ columnGroup t} :
        Finset (Equiv.Perm (Fin n))).card • polytabloidRat t +
      ∑ σ ∈ {σ : Equiv.Perm (Fin n) | (∀ k ∉ X, σ k = k) ∧ σ ∉ columnGroup t},
        ((Equiv.Perm.sign σ : ℤ) : ℚ) • polytabloidRat (relabel σ t) = 0 := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not
    ({σ : Equiv.Perm (Fin n) | ∀ k ∉ X, σ k = k} : Finset (Equiv.Perm (Fin n)))
    (fun σ => σ ∈ columnGroup t)
    (fun σ => ((Equiv.Perm.sign σ : ℤ) : ℚ) • polytabloidRat (relabel σ t))
  rw [sum_sign_smul_polytabloidRat_relabel_eq_zero t hX hcard,
    Finset.filter_filter, Finset.filter_filter] at hsplit
  have hconst : ∀ σ ∈ ({σ : Equiv.Perm (Fin n) |
      (∀ k ∉ X, σ k = k) ∧ σ ∈ columnGroup t} : Finset (Equiv.Perm (Fin n))),
      ((Equiv.Perm.sign σ : ℤ) : ℚ) • polytabloidRat (relabel σ t) = polytabloidRat t := by
    intro σ hσ
    rw [polytabloidRat_relabel_of_mem_columnGroup t (Finset.mem_filter.mp hσ).2.2,
      smul_smul]
    have hsq : ((Equiv.Perm.sign σ : ℤ) : ℚ) * ((Equiv.Perm.sign σ : ℤ) : ℚ) = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
    rw [hsq, one_smul]
  rwa [Finset.sum_congr rfl hconst, Finset.sum_const] at hsplit

/-- Rational Garnir straightening: only permutations that leave the column
group are required. The positive multiplicity of internal permutations is
cancelled over the rationals. -/
theorem polytabloidRat_mem_span_relabel (t : Tableau n μ)
    {X : Finset (Fin n)} {r : ℕ} (hX : ∀ k ∈ X, μ.colLen (t k).val.2 ≤ r)
    (hcard : r < X.card) :
    polytabloidRat t ∈ Submodule.span ℚ
      ((fun σ => polytabloidRat (relabel σ t)) ''
        {σ : Equiv.Perm (Fin n) | (∀ k ∉ X, σ k = k) ∧ σ ∉ columnGroup t}) := by
  classical
  have hpos : 0 < ({σ : Equiv.Perm (Fin n) |
      (∀ k ∉ X, σ k = k) ∧ σ ∈ columnGroup t} : Finset (Equiv.Perm (Fin n))).card :=
    Finset.card_pos.mpr ⟨1, by simp⟩
  have hne : (({σ : Equiv.Perm (Fin n) |
      (∀ k ∉ X, σ k = k) ∧ σ ∈ columnGroup t} : Finset (Equiv.Perm (Fin n))).card : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hpos.ne'
  refine (Submodule.smul_mem_iff _ hne).mp ?_
  rw [Nat.cast_smul_eq_nsmul, eq_neg_of_add_eq_zero_left
    (card_nsmul_polytabloidRat_add_sum_eq_zero t hX hcard)]
  refine neg_mem (Submodule.sum_mem _ fun σ hσ => Submodule.smul_mem _ _ ?_)
  exact Submodule.subset_span ⟨σ, (Finset.mem_filter.mp hσ).2, rfl⟩

end BostConjecture.Specht
