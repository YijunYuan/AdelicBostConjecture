module

public import BostConjecture.Specht.Rectangle
public import BostConjecture.Specht.Prefix

/-!
# Rotation and complements inside a rectangle

The complement of a Young subdiagram becomes a Young diagram after a
half-turn. Its tableaux supply the suffix factor in rectangular prefix counting.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Specht

open OAI.Saxl

/-- Half-turn of coordinates in an `a` by `k` rectangle. -/
def rotateCell (a k : ℕ) (c : ℕ × ℕ) : ℕ × ℕ := (a - 1 - c.1, k - 1 - c.2)

theorem rotateCell_mem {a k : ℕ} {c : ℕ × ℕ} (hc : c ∈ rectangle a k) :
    rotateCell a k c ∈ rectangle a k := by
  obtain ⟨hr, hq⟩ := mem_rectangle.mp hc
  simp only [rotateCell, mem_rectangle]
  omega

@[simp] theorem rotateCell_rotateCell {a k : ℕ} {c : ℕ × ℕ}
    (hc : c ∈ rectangle a k) : rotateCell a k (rotateCell a k c) = c := by
  obtain ⟨hr, hq⟩ := mem_rectangle.mp hc
  apply Prod.ext <;> simp only [rotateCell] <;> omega

/-- The rotated complement of a Young diagram within a rectangle. -/
def rectangleComplement (μ : YoungDiagram) (a k : ℕ) : YoungDiagram where
  cells := (rectangle a k).cells.filter fun c => rotateCell a k c ∉ μ
  isLowerSet := by
    intro c b hbc hc
    obtain ⟨hc, hn⟩ := Finset.mem_filter.mp hc
    have hb := (rectangle a k).isLowerSet hbc hc
    refine Finset.mem_filter.mpr ⟨hb, ?_⟩
    intro h
    apply hn
    exact μ.isLowerSet ⟨Nat.sub_le_sub_left hbc.1 _, Nat.sub_le_sub_left hbc.2 _⟩ h

@[simp] theorem mem_rectangleComplement {μ : YoungDiagram} {a k : ℕ} {c : ℕ × ℕ} :
    c ∈ rectangleComplement μ a k ↔ c ∈ rectangle a k ∧ rotateCell a k c ∉ μ := by
  change c ∈ (rectangle a k).cells.filter _ ↔ _
  simp only [Finset.mem_filter, YoungDiagram.mem_cells]

theorem rectangleComplement_le (μ : YoungDiagram) (a k : ℕ) :
    rectangleComplement μ a k ≤ rectangle a k := fun _ h => (mem_rectangleComplement.mp h).1

/-- Rotation exchanges the complement with the omitted boxes. -/
theorem rotateCell_mem_rectangleComplement {μ : YoungDiagram} {a k : ℕ} {c : ℕ × ℕ}
    (hc : c ∈ rectangle a k) :
    rotateCell a k c ∈ rectangleComplement μ a k ↔ c ∉ μ := by
  simp only [mem_rectangleComplement, rotateCell_mem hc, rotateCell_rotateCell hc, true_and]

@[simp] theorem rectangleComplement_involutive {μ : YoungDiagram} {a k : ℕ}
    (hμ : μ ≤ rectangle a k) : rectangleComplement (rectangleComplement μ a k) a k = μ := by
  ext c
  simp only [YoungDiagram.mem_cells]
  constructor
  · intro hc
    obtain ⟨hr, hc⟩ := mem_rectangleComplement.mp hc
    simpa only [rotateCell_mem_rectangleComplement hr, not_not] using hc
  · intro hc
    exact mem_rectangleComplement.mpr ⟨hμ hc, by
      simpa only [rotateCell_mem_rectangleComplement (hμ hc), not_not] using hc⟩

/-- Splitting the rectangle into the prefix diagram and its rotated complement. -/
def rectangleSplitEquiv {μ : YoungDiagram} {a k : ℕ} (hμ : μ ≤ rectangle a k) :
    μ.cells ⊕ (rectangleComplement μ a k).cells ≃ (rectangle a k).cells where
  toFun := Sum.elim (fun c => ⟨c, hμ c.property⟩)
    (fun c => ⟨rotateCell a k c, rotateCell_mem (rectangleComplement_le μ a k c.property)⟩)
  invFun c := if h : c.val ∈ μ then Sum.inl ⟨c, h⟩ else
    Sum.inr ⟨rotateCell a k c, (rotateCell_mem_rectangleComplement c.property).mpr h⟩
  left_inv c := by
    rcases c with c | c
    · simp
    · have hc := (mem_rectangleComplement.mp c.property).2
      simp only [Sum.elim_inr, hc, ↓reduceDIte, Sum.inr.injEq]
      exact Subtype.ext (rotateCell_rotateCell (rectangleComplement_le μ a k c.property))
  right_inv c := by
    dsimp
    split_ifs with hc
    · rfl
    · exact Subtype.ext (rotateCell_rotateCell c.property)

/-- Complementary cardinalities add to the rectangle size. -/
theorem card_add_card_rectangleComplement {μ : YoungDiagram} {a k : ℕ}
    (hμ : μ ≤ rectangle a k) : μ.card + (rectangleComplement μ a k).card = a * k := by
  have h := Fintype.card_congr (rectangleSplitEquiv hμ)
  simp only [Fintype.card_sum, Fintype.card_coe] at h
  change μ.card + (rectangleComplement μ a k).card = (rectangle a k).card at h
  rwa [card_rectangle] at h

private theorem rowLen_le_rectangle {μ : YoungDiagram} {a k r : ℕ}
    (hμ : μ ≤ rectangle a k) : μ.rowLen r ≤ k := by
  by_contra h
  have hm : (r, k) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
  have := (mem_rectangle.mp (hμ hm)).2
  omega

/-- Complement row lengths are reversed and subtracted from the rectangle width. -/
theorem rowLen_rectangleComplement {μ : YoungDiagram} {a k r : ℕ}
    (hμ : μ ≤ rectangle a k) (hr : r < a) :
    (rectangleComplement μ a k).rowLen r = k - μ.rowLen (a - 1 - r) := by
  apply eq_of_forall_lt_iff
  intro q
  rw [← YoungDiagram.mem_iff_lt_rowLen, mem_rectangleComplement]
  rw [mem_rectangle]
  simp only [hr, true_and, rotateCell, YoungDiagram.mem_iff_lt_rowLen]
  have hb := rowLen_le_rectangle (r := a - 1 - r) hμ
  omega

end BostConjecture.Specht
