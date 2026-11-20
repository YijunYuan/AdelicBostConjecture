/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Specht.Seminormal.Central

/-!
# Standard prefix diagrams

Restriction to an initial label interval uses the existing enumerating
tableaux and Young diagrams. Its content sum is the scalar of the central
transposition operator on the restricted Specht module.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Specht

open OAI.Saxl

variable {n : ℕ} {μ : YoungDiagram} {t : Tableau n μ}

/-- Labels in a standard tableau are monotone in the northwest order. -/
theorem IsStandard.label_mono [ht : IsStandard t] {b c : μ}
    (h : b.val ≤ c.val) : t.symm b ≤ t.symm c := by
  let a : μ := ⟨(b.val.1, c.val.2), μ.up_left_mem h.1 le_rfl c.property⟩
  have hba : t.symm b ≤ t.symm a := by
    rcases h.2.eq_or_lt with he | he
    · have : b = a := Subtype.ext (Prod.ext rfl he)
      simp [this]
    · exact (ht.rowStandard.label_lt (t.symm b) (t.symm a) (by simp [a]) (by simpa [a] using he)).le
  have hac : t.symm a ≤ t.symm c := by
    rcases h.1.eq_or_lt with he | he
    · have : a = c := Subtype.ext (Prod.ext he rfl)
      simp [this]
    · exact (ht.columnStandard.label_lt (t.symm a) (t.symm c)
        (by simp [a]) (by simpa [a] using he)).le
  exact hba.trans hac

/-- This paper, Definition 4.6. Labels in the formalization start at zero.

The boxes whose labels are in the first `m` positions. -/
def prefixShape (t : Tableau n μ) [ht : IsStandard t] (m : ℕ) (hm : m ≤ n) : YoungDiagram where
  cells := Finset.univ.image (fun i : Fin m => (t (Fin.castLE hm i)).val)
  isLowerSet := by
    intro c b hbc hc
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hc
    have hcμ : c ∈ μ := hi ▸ (t (Fin.castLE hm i)).property
    have hbμ : b ∈ μ := μ.isLowerSet hbc hcμ
    have hle := IsStandard.label_mono (t := t) (b := ⟨b, hbμ⟩) (c := ⟨c, hcμ⟩) hbc
    have hc' : (⟨c, hcμ⟩ : μ) = t (Fin.castLE hm i) := Subtype.ext hi.symm
    rw [hc', t.symm_apply_apply] at hle
    have hb : (t.symm ⟨b, hbμ⟩).val < m := lt_of_le_of_lt hle i.isLt
    refine Finset.mem_image.mpr ⟨⟨_, hb⟩, Finset.mem_univ _, ?_⟩
    simp

@[simp] theorem mem_prefixShape [ht : IsStandard t] (m : ℕ) (hm : m ≤ n)
    (b : μ) : b.val ∈ prefixShape t m hm ↔ (t.symm b).val < m := by
  constructor
  · rintro h
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
    have he : t (Fin.castLE hm i) = b := Subtype.ext hi
    simp [← he]
  · intro h
    refine Finset.mem_image.mpr ⟨⟨_, h⟩, Finset.mem_univ _, ?_⟩
    simp

/-- The original labeling restricted to its prefix diagram. -/
def prefixTableau (t : Tableau n μ) [ht : IsStandard t] (m : ℕ) (hm : m ≤ n) :
    Tableau m (prefixShape t m hm) :=
  Equiv.ofBijective
    (fun i => ⟨(t (Fin.castLE hm i)).val,
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩)
    ⟨by
      intro i j h
      have he : t (Fin.castLE hm i) = t (Fin.castLE hm j) :=
        Subtype.ext (congrArg (fun x : prefixShape t m hm => x.val) h)
      exact Fin.ext (congrArg (fun x : Fin n => x.val) (t.injective he)), by
      rintro ⟨b, hb⟩
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hb
      exact ⟨i, Subtype.ext hi⟩⟩

instance prefixTableau_isStandard [ht : IsStandard t] (m : ℕ) (hm : m ≤ n) :
    IsStandard (prefixTableau t m hm) := by
  refine ⟨⟨?_⟩, ⟨?_⟩⟩
  · intro i j hr hc
    exact ht.rowStandard.label_lt (Fin.castLE hm i) (Fin.castLE hm j) hr hc
  · intro i j hc hr
    exact ht.columnStandard.label_lt (Fin.castLE hm i) (Fin.castLE hm j) hc hr

@[simp] theorem card_prefixShape [ht : IsStandard t] (m : ℕ) (hm : m ≤ n) :
    (prefixShape t m hm).card = m := by
  simpa using (Fintype.card_congr (prefixTableau t m hm)).symm

theorem prefixShape_le [ht : IsStandard t] (m : ℕ) (hm : m ≤ n) :
    prefixShape t m hm ≤ μ := by
  intro b hb
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hb
  exact (t (Fin.castLE hm i)).property

/-- The prefix content sum is computed in the original tableau. -/
theorem diagramContent_prefixShape [ht : IsStandard t] (m : ℕ) (hm : m ≤ n) :
    diagramContent (prefixShape t m hm) =
      ∑ j : Fin m, tableauContent t (Fin.castLE hm j) :=
  (sum_tableauContent (prefixTableau t m hm)).symm

end BostConjecture.Specht
