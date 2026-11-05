module

public import BostConjecture.Specht.Complement
public import BostConjecture.Specht.ShiftedCount

/-!
# Prefix counting for rectangular standard tableaux

The suffix is rotated and its labels reversed. Gluing is the inverse
operation, on the same enumerating tableaux used by the Specht basis.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Specht

open OAI.Saxl

variable {μ : YoungDiagram} {a k m l : ℕ}

/-- Glue a prefix and a reversed, rotated complementary tableau. -/
def glueRectangleTableau (hμ : μ ≤ rectangle a k) (t : Tableau m μ)
    (u : Tableau l (rectangleComplement μ a k)) : Tableau (m + l) (rectangle a k) :=
  finSumFinEquiv.symm.trans
    ((Equiv.sumCongr t (Fin.revPerm.trans u)).trans (rectangleSplitEquiv hμ))

@[simp] theorem glueRectangleTableau_castAdd (hμ : μ ≤ rectangle a k) (t : Tableau m μ)
    (u : Tableau l (rectangleComplement μ a k)) (i : Fin m) :
    (glueRectangleTableau hμ t u (Fin.castAdd l i)).val = (t i).val := by
  simp [glueRectangleTableau, rectangleSplitEquiv]

@[simp] theorem glueRectangleTableau_natAdd (hμ : μ ≤ rectangle a k) (t : Tableau m μ)
    (u : Tableau l (rectangleComplement μ a k)) (i : Fin l) :
    (glueRectangleTableau hμ t u (Fin.natAdd m i)).val = rotateCell a k (u i.rev).val := by
  simp [glueRectangleTableau, rectangleSplitEquiv]


private theorem glueRectangleTableau_label_mono (hμ : μ ≤ rectangle a k)
    {t : Tableau m μ} {u : Tableau l (rectangleComplement μ a k)}
    (ht : IsStandard t) (hu : IsStandard u) (i j : Fin (m + l))
    (h : (glueRectangleTableau hμ t u i).val ≤ (glueRectangleTableau hμ t u j).val) :
    i ≤ j := by
  cases i using Fin.addCases with
  | left i =>
    cases j using Fin.addCases with
    | left j =>
      simp only [glueRectangleTableau_castAdd] at h
      have hh := ht.label_mono (b := t i) (c := t j) h
      change i ≤ j
      simpa using hh
    | right j => exact le_of_lt (by change i.val < m + j.val; omega)
  | right i =>
    cases j using Fin.addCases with
    | left j =>
      simp only [glueRectangleTableau_natAdd, glueRectangleTableau_castAdd] at h
      have hn := (mem_rectangleComplement.mp (u i.rev).property).2
      exact (hn (μ.isLowerSet h (t j).property)).elim
    | right j =>
      simp only [glueRectangleTableau_natAdd] at h
      have hh : (u j.rev).val ≤ (u i.rev).val := by
        have hr : rotateCell a k (rotateCell a k (u j.rev).val) ≤
            rotateCell a k (rotateCell a k (u i.rev).val) :=
          ⟨Nat.sub_le_sub_left h.1 _, Nat.sub_le_sub_left h.2 _⟩
        simpa only [rotateCell_rotateCell (rectangleComplement_le μ a k (u j.rev).property),
          rotateCell_rotateCell (rectangleComplement_le μ a k (u i.rev).property)] using hr
      have hm := hu.label_mono (b := u j.rev) (c := u i.rev) hh
      simp only [Equiv.symm_apply_apply] at hm
      have hle : i ≤ j := by simpa only [Fin.rev_rev] using Fin.rev_strictAnti.antitone hm
      change m + i.val ≤ m + j.val
      exact Nat.add_le_add_left hle m

/-- Gluing standard complementary fillings yields a standard rectangular tableau. -/
theorem glueRectangleTableau_isStandard (hμ : μ ≤ rectangle a k)
    {t : Tableau m μ} {u : Tableau l (rectangleComplement μ a k)}
    (ht : IsStandard t) (hu : IsStandard u) : IsStandard (glueRectangleTableau hμ t u) := by
  constructor
  · intro i j hr hq
    have hle := glueRectangleTableau_label_mono hμ ht hu i j ⟨hr.le, hq.le⟩
    exact lt_of_le_of_ne hle (by intro he; subst j; exact hq.ne rfl)
  · intro i j hq hr
    have hle := glueRectangleTableau_label_mono hμ ht hu i j ⟨hr.le, hq.le⟩
    exact lt_of_le_of_ne hle (by intro he; subst j; exact hr.ne rfl)

/-- The prefix of the glued tableau is precisely the chosen subdiagram. -/
theorem prefixShape_glueRectangleTableau (hμ : μ ≤ rectangle a k)
    {t : Tableau m μ} {u : Tableau l (rectangleComplement μ a k)}
    (ht : IsStandard t) (hu : IsStandard u) :
    prefixShape (glueRectangleTableau_isStandard hμ ht hu) m (Nat.le_add_right m l) = μ := by
  ext c
  change c ∈ Finset.univ.image (fun i : Fin m =>
    (glueRectangleTableau hμ t u (Fin.castLE (Nat.le_add_right m l) i)).val) ↔ c ∈ μ.cells
  constructor
  · rintro hc
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hc
    change (glueRectangleTableau hμ t u (Fin.castAdd l i)).val ∈ μ.cells
    simp
  · intro hc
    refine Finset.mem_image.mpr ⟨t.symm ⟨c, hc⟩, Finset.mem_univ _, ?_⟩
    change (glueRectangleTableau hμ t u (Fin.castAdd l (t.symm ⟨c, hc⟩))).val = c
    simp


/-- Transport the actual prefix tableau to its specified shape. -/
def prefixTableauOfShape {T : Tableau (m + l) (rectangle a k)} (hT : IsStandard T)
    (hP : prefixShape hT m (Nat.le_add_right m l) = μ) : Tableau m μ :=
  (prefixTableau hT m (Nat.le_add_right m l)).trans
    (Equiv.subtypeEquivRight fun c => by rw [hP])

@[simp] theorem prefixTableauOfShape_apply {T : Tableau (m + l) (rectangle a k)}
    (hT : IsStandard T) (hP : prefixShape hT m (Nat.le_add_right m l) = μ) (i : Fin m) :
    (prefixTableauOfShape hT hP i).val = (T (Fin.castAdd l i)).val := rfl

theorem prefixTableauOfShape_isStandard {T : Tableau (m + l) (rectangle a k)}
    (hT : IsStandard T) (hP : prefixShape hT m (Nat.le_add_right m l) = μ) :
    IsStandard (prefixTableauOfShape hT hP) := by
  constructor
  · intro i j hr hq
    exact hT.1 (Fin.castAdd l i) (Fin.castAdd l j) hr hq
  · intro i j hq hr
    exact hT.2 (Fin.castAdd l i) (Fin.castAdd l j) hq hr

/-- Suffix labels lie outside the specified prefix diagram. -/
theorem suffix_not_mem {T : Tableau (m + l) (rectangle a k)}
    (hT : IsStandard T) (hP : prefixShape hT m (Nat.le_add_right m l) = μ) (i : Fin l) :
    (T (Fin.natAdd m i)).val ∉ μ := by
  rw [← hP, mem_prefixShape]
  simp

/-- Extract the suffix, reversing both its labels and its box coordinates. -/
def complementTableauOfShape {T : Tableau (m + l) (rectangle a k)}
    (hT : IsStandard T) (hP : prefixShape hT m (Nat.le_add_right m l) = μ) :
    Tableau l (rectangleComplement μ a k) :=
  Equiv.ofBijective
    (fun i => ⟨rotateCell a k (T (Fin.natAdd m i.rev)).val,
      (rotateCell_mem_rectangleComplement (T (Fin.natAdd m i.rev)).property).mpr
        (suffix_not_mem hT hP i.rev)⟩)
    ⟨by
      intro i j h
      have he := congrArg (fun c : (rectangleComplement μ a k).cells =>
        rotateCell a k c.val) h
      simp only [rotateCell_rotateCell (T (Fin.natAdd m i.rev)).property,
        rotateCell_rotateCell (T (Fin.natAdd m j.rev)).property] at he
      have hi : Fin.natAdd m i.rev = Fin.natAdd m j.rev := T.injective (Subtype.ext he)
      have hr : i.rev = j.rev := Fin.ext (by exact Nat.add_left_cancel (congrArg Fin.val hi))
      simpa only [Fin.rev_rev] using congrArg Fin.rev hr
    , by
      intro c
      let b : (rectangle a k).cells :=
        ⟨rotateCell a k c.val, rotateCell_mem (rectangleComplement_le μ a k c.property)⟩
      let i := T.symm b
      have hi : m ≤ i.val := by
        by_contra hh
        have hb : b.val ∈ prefixShape hT m (Nat.le_add_right m l) :=
          (mem_prefixShape hT m (Nat.le_add_right m l) b).mpr (by omega)
        rw [hP] at hb
        exact (mem_rectangleComplement.mp c.property).2 hb
      let j : Fin l := ⟨i.val - m, by have := i.isLt; omega⟩
      refine ⟨j.rev, ?_⟩
      apply Subtype.ext
      have he : Fin.natAdd m j = i := Fin.ext (by dsimp [j]; omega)
      simp only [Fin.rev_rev, he]
      change rotateCell a k (T (T.symm b)).val = c.val
      rw [T.apply_symm_apply]
      exact rotateCell_rotateCell (rectangleComplement_le μ a k c.property)⟩

@[simp] theorem complementTableauOfShape_apply {T : Tableau (m + l) (rectangle a k)}
    (hT : IsStandard T) (hP : prefixShape hT m (Nat.le_add_right m l) = μ) (i : Fin l) :
    (complementTableauOfShape hT hP i).val = rotateCell a k (T (Fin.natAdd m i.rev)).val := rfl

private theorem rotate_row_comparison {a k : ℕ} {c d : ℕ × ℕ}
    (hc : c ∈ rectangle a k) (hd : d ∈ rectangle a k)
    (hr : (rotateCell a k c).1 = (rotateCell a k d).1)
    (hq : (rotateCell a k c).2 < (rotateCell a k d).2) : d.1 = c.1 ∧ d.2 < c.2 := by
  rcases c with ⟨r, q⟩
  rcases d with ⟨s, p⟩
  simp only [mem_rectangle, rotateCell] at *
  constructor <;> omega

private theorem rotate_col_comparison {a k : ℕ} {c d : ℕ × ℕ}
    (hc : c ∈ rectangle a k) (hd : d ∈ rectangle a k)
    (hq : (rotateCell a k c).2 = (rotateCell a k d).2)
    (hr : (rotateCell a k c).1 < (rotateCell a k d).1) : d.2 = c.2 ∧ d.1 < c.1 := by
  rcases c with ⟨r, q⟩
  rcases d with ⟨s, p⟩
  simp only [mem_rectangle, rotateCell] at *
  constructor <;> omega

/-- The extracted rotated suffix is standard. -/
theorem complementTableauOfShape_isStandard {T : Tableau (m + l) (rectangle a k)}
    (hT : IsStandard T) (hP : prefixShape hT m (Nat.le_add_right m l) = μ) :
    IsStandard (complementTableauOfShape hT hP) := by
  constructor
  · intro i j hr hq
    have h := rotate_row_comparison (T (Fin.natAdd m i.rev)).property
      (T (Fin.natAdd m j.rev)).property hr hq
    have hh := hT.1 (Fin.natAdd m j.rev) (Fin.natAdd m i.rev) h.1 h.2
    have hrev : j.rev < i.rev := by
      change m + j.rev.val < m + i.rev.val at hh
      exact Nat.lt_of_add_lt_add_left hh
    simpa only [Fin.rev_rev] using Fin.rev_strictAnti hrev
  · intro i j hq hr
    have h := rotate_col_comparison (T (Fin.natAdd m i.rev)).property
      (T (Fin.natAdd m j.rev)).property hq hr
    have hh := hT.2 (Fin.natAdd m j.rev) (Fin.natAdd m i.rev) h.1 h.2
    have hrev : j.rev < i.rev := by
      change m + j.rev.val < m + i.rev.val at hh
      exact Nat.lt_of_add_lt_add_left hh
    simpa only [Fin.rev_rev] using Fin.rev_strictAnti hrev


/-- The actual rectangular prefix fiber is the product of the two standard-tableau types. -/
def rectanglePrefixEquiv (hμ : μ ≤ rectangle a k) :
    {T : {T : Tableau (m + l) (rectangle a k) // IsStandard T} //
      prefixShape T.property m (Nat.le_add_right m l) = μ} ≃
    {t : Tableau m μ // IsStandard t} ×
      {u : Tableau l (rectangleComplement μ a k) // IsStandard u} where
  toFun X :=
    (⟨prefixTableauOfShape X.val.property X.property,
       prefixTableauOfShape_isStandard X.val.property X.property⟩,
     ⟨complementTableauOfShape X.val.property X.property,
       complementTableauOfShape_isStandard X.val.property X.property⟩)
  invFun P :=
    ⟨⟨glueRectangleTableau hμ P.1.val P.2.val,
       glueRectangleTableau_isStandard hμ P.1.property P.2.property⟩,
     prefixShape_glueRectangleTableau hμ P.1.property P.2.property⟩
  left_inv X := by
    apply Subtype.ext
    apply Subtype.ext
    apply Equiv.ext
    intro i
    apply Subtype.ext
    cases i using Fin.addCases <;> simp
  right_inv P := by
    apply Prod.ext
    · apply Subtype.ext
      apply Equiv.ext
      intro i
      apply Subtype.ext
      simp
    · apply Subtype.ext
      apply Equiv.ext
      intro i
      apply Subtype.ext
      simp only [complementTableauOfShape_apply, glueRectangleTableau_natAdd, Fin.rev_rev]
      exact rotateCell_rotateCell (rectangleComplement_le μ a k (P.2.val i).property)

/-- Exact counting of a rectangular prefix fiber by complementary standard tableaux. -/
theorem card_rectanglePrefix (hμ : μ ≤ rectangle a k) :
    Nat.card {T : {T : Tableau (m + l) (rectangle a k) // IsStandard T} //
      prefixShape T.property m (Nat.le_add_right m l) = μ} =
    Fintype.card {t : Tableau m μ // IsStandard t} *
      Fintype.card {u : Tableau l (rectangleComplement μ a k) // IsStandard u} := by
  rw [Nat.card_congr (rectanglePrefixEquiv hμ)]
  simp only [Nat.card_eq_fintype_card, Fintype.card_prod]

end BostConjecture.Specht



