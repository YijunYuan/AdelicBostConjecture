module

public import BostConjecture.Specht.Filtration
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Branching by restriction at a removable corner

The frozen-tail coefficient map on the largest-label filtration has image the
smaller Specht space and kernel the preceding filtration step. All spaces use
the existing orthonormal word realization.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Specht

open OAI.Saxl

variable {n m : ℕ} {μ : YoungDiagram}

/-- In a row-standard tableau, the largest label is at the right end of its row. -/
theorem RowStandard.last_col_eq_of_row_eq {t u : Tableau (n + 1) μ}
    (ht : RowStandard t) (hu : RowStandard u)
    (hr : (t (Fin.last n)).val.1 = (u (Fin.last n)).val.1) :
    t (Fin.last n) = u (Fin.last n) := by
  apply Subtype.ext
  apply Prod.ext hr
  apply le_antisymm
  · by_contra! h
    have hi := hu (Fin.last n) (u.symm (t (Fin.last n)))
      (by simpa using hr.symm) (by simpa using h)
    exact (not_lt_of_ge (Fin.le_last _)) hi
  · by_contra! h
    have hi := ht (Fin.last n) (t.symm (u (Fin.last n)))
      (by simpa using hr) (by simpa using h)
    exact (not_lt_of_ge (Fin.le_last _)) hi

/-- Two tableaux placing the largest label in the same box differ by a prefix permutation. -/
theorem exists_prefixPerm_relabel {t u : Tableau (n + 1) μ}
    (h : t (Fin.last n) = u (Fin.last n)) :
    ∃ g : Equiv.Perm (Fin n), relabel (prefixPerm (Nat.le_succ n) g) t = u := by
  let p := t.trans u.symm
  have hfix : ∀ i : Fin (n + 1), n ≤ i.val → p i = i := by
    intro i hi
    have he : i = Fin.last n := Fin.ext (by simp only [Fin.val_last]; omega)
    subst i
    change u.symm (t (Fin.last n)) = Fin.last n
    rw [h, u.symm_apply_apply]
  refine ⟨restrictPrefixPerm (Nat.le_succ n) p hfix, ?_⟩
  rw [prefixPerm_restrictPrefixPerm]
  apply Equiv.ext
  intro i
  simp [relabel, p]

/-- Frozen-tail restriction between real Hilbert word spaces. -/
def prefixSliceReal {t : Tableau n μ} (ht : IsStandard t) (hm : m ≤ n) :
    EuclideanSpace ℝ (Fin n → Fin (μ.colLen 0)) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin m → Fin ((prefixShape ht m hm).colLen 0)) where
  toFun x := WithLp.toLp 2 (fun w => x (extendPrefixWord ht hm w))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem prefixSliceReal_realCast {t : Tableau n μ} (ht : IsStandard t)
    (hm : m ≤ n) (x : (Fin n → Fin (μ.colLen 0)) → ℤ) :
    prefixSliceReal ht hm (realCast n (μ.colLen 0) x) =
      realCast m ((prefixShape ht m hm).colLen 0) (prefixSlice ht hm x) := rfl

@[simp] theorem prefixSliceReal_polytabloid {t : Tableau n μ} (ht : IsStandard t)
    (hm : m ≤ n) :
    prefixSliceReal ht hm (realCast n (μ.colLen 0) (polytabloidInt t)) =
      realCast m ((prefixShape ht m hm).colLen 0)
        (polytabloidInt (prefixTableau ht m hm)) := by
  rw [prefixSliceReal_realCast, prefixSlice_polytabloidInt]

/-- Restriction commutes with the real prefix position action. -/
theorem prefixSliceReal_wordRepReal {t : Tableau n μ} (ht : IsStandard t)
    (hm : m ≤ n) (g : Equiv.Perm (Fin m))
    (x : EuclideanSpace ℝ (Fin n → Fin (μ.colLen 0))) :
    prefixSliceReal ht hm (wordRepReal n (μ.colLen 0) (prefixPerm hm g) x) =
      wordRepReal m ((prefixShape ht m hm).colLen 0) g (prefixSliceReal ht hm x) := by
  ext w
  exact congrArg x (extendPrefixWord_comp ht hm w g).symm

/-- The row word of the original tableau is the extension of its prefix row word. -/
@[simp] theorem extendPrefixWord_rowWord {t : Tableau n μ} (ht : IsStandard t)
    (hm : m ≤ n) :
    extendPrefixWord ht hm (rowWord (prefixTableau ht m hm)) = rowWord t := by
  funext i
  by_cases hi : i.val < m
  · change extendPrefixWord ht hm _ (Fin.castLE hm ⟨i.val, hi⟩) = _
    rw [extendPrefixWord_castLE]
    rfl
  · exact extendPrefixWord_of_le ht hm _ i (le_of_not_gt hi)

/-- Leading row words in the chosen corner stratum occur among the slice coordinates. -/
theorem exists_extendPrefixWord_eq_rowWord {t u : Tableau (n + 1) μ}
    (ht : IsStandard t) (hu : RowStandard u)
    (hr : (rowWord u (Fin.last n)).val = (rowWord t (Fin.last n)).val) :
    ∃ w, extendPrefixWord ht (Nat.le_succ n) w = rowWord u := by
  obtain ⟨g, rfl⟩ := exists_prefixPerm_relabel (ht.1.last_col_eq_of_row_eq hu hr.symm)
  refine ⟨rowWord (prefixTableau ht n (Nat.le_succ n)) ∘ (g⁻¹ : Equiv.Perm (Fin n)), ?_⟩
  rw [extendPrefixWord_comp, extendPrefixWord_rowWord, rowWord_relabel, prefixPerm_inv]

/-- A standard generator in a strictly earlier row is killed by the corner slice. -/
theorem prefixSliceReal_standardRealBasis_eq_zero {t : Tableau (n + 1) μ}
    (ht : IsStandard t) (T : {u : Tableau (n + 1) μ // IsStandard u})
    (hT : (rowWord T.val (Fin.last n)).val < (rowWord t (Fin.last n)).val) :
    prefixSliceReal ht (Nat.le_succ n) (standardRealBasis t T) = 0 := by
  ext w
  change (standardRealBasis t T).val (extendPrefixWord ht (Nat.le_succ n) w) = 0
  rw [standardRealBasis_coe]
  change (polytabloidInt T.val (extendPrefixWord ht (Nat.le_succ n) w) : ℝ) = 0
  suffices hz : polytabloidInt T.val (extendPrefixWord ht (Nat.le_succ n) w) = 0 by
    rw [hz, Int.cast_zero]
  by_contra hz
  have hle := T.property.2.last_row_le_of_polytabloidInt_ne_zero hz
  rw [extendPrefixWord_of_le ht (Nat.le_succ n) _ _ le_rfl] at hle
  exact (not_le_of_gt hT) hle

/-- A standard generator in the corner row maps into the smaller Specht space. -/
theorem prefixSliceReal_standardRealBasis_mem {t : Tableau (n + 1) μ}
    (ht : IsStandard t) (T : {u : Tableau (n + 1) μ // IsStandard u})
    (hT : (rowWord T.val (Fin.last n)).val = (rowWord t (Fin.last n)).val) :
    prefixSliceReal ht (Nat.le_succ n) (standardRealBasis t T) ∈
      realSpan (prefixTableau ht n (Nat.le_succ n)) := by
  obtain ⟨g, hg⟩ := exists_prefixPerm_relabel
    (ht.1.last_col_eq_of_row_eq T.property.1 hT.symm)
  rw [standardRealBasis_coe, ← hg, polytabloidInt_relabel, ← wordRepReal_realCast,
    prefixSliceReal_wordRepReal, prefixSliceReal_polytabloid]
  apply wordRepReal_mem_realSpan
  exact Submodule.subset_span ⟨_, polytabloidInt_mem_orbitLattice _, rfl⟩

/-- Restriction of the entire filtration step lands in the smaller Specht space. -/
theorem prefixSliceReal_mem_realSpan {t : Tableau (n + 1) μ} (ht : IsStandard t)
    {x : realSpan t} (hx : x ∈ lastRowSubspace t (rowWord t (Fin.last n)).val) :
    prefixSliceReal ht (Nat.le_succ n) x.val ∈
      realSpan (prefixTableau ht n (Nat.le_succ n)) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨T, hT, rfl⟩ := hx
    rcases hT.eq_or_lt with hT | hT
    · exact prefixSliceReal_standardRealBasis_mem ht T hT
    · rw [prefixSliceReal_standardRealBasis_eq_zero ht T hT]
      exact Submodule.zero_mem _
  | zero => simp
  | add x y hx hy ihx ihy =>
    simpa only [Submodule.coe_add, map_add] using Submodule.add_mem _ ihx ihy
  | smul a x hx ih =>
    simpa only [Submodule.coe_smul, map_smul] using Submodule.smul_mem _ a ih

/-- The actual branching restriction map, with its image condition proved. -/
def branchingMap {t : Tableau (n + 1) μ} (ht : IsStandard t) :
    lastRowSubspace t (rowWord t (Fin.last n)).val →ₗ[ℝ]
      realSpan (prefixTableau ht n (Nat.le_succ n)) where
  toFun x := ⟨prefixSliceReal ht (Nat.le_succ n) x.val.val,
    prefixSliceReal_mem_realSpan ht x.property⟩
  map_add' _ _ := by ext w; rfl
  map_smul' _ _ := by ext w; rfl

/-- Each smaller orbit vector lifts inside the chosen filtration step. -/
theorem branchingMap_lift_orbit {t : Tableau (n + 1) μ} (ht : IsStandard t)
    (g : Equiv.Perm (Fin n)) :
    ∃ x, branchingMap ht x =
      realSpechtRep (prefixTableau ht n (Nat.le_succ n)) g
        (standardRealBasis (prefixTableau ht n (Nat.le_succ n))
          ⟨_, prefixTableau_isStandard ht n (Nat.le_succ n)⟩) := by
  let y := realSpechtRep t (prefixPerm (Nat.le_succ n) g) (standardRealBasis t ⟨t, ht⟩)
  have hy : y ∈ lastRowSubspace t (rowWord t (Fin.last n)).val := by
    apply prefixPerm_mem_lastRowSubspace
    exact Submodule.subset_span ⟨⟨t, ht⟩, le_rfl, rfl⟩
  refine ⟨⟨y, hy⟩, ?_⟩
  apply Subtype.ext
  change prefixSliceReal ht (Nat.le_succ n)
      (wordRepReal _ _ (prefixPerm (Nat.le_succ n) g) (standardRealBasis t ⟨t, ht⟩).val) = _
  rw [prefixSliceReal_wordRepReal, standardRealBasis_coe, prefixSliceReal_polytabloid]
  rw [realSpechtRep_coe, standardRealBasis_coe]

/-- The branching restriction is onto the actual smaller Specht space. -/
theorem branchingMap_surjective {t : Tableau (n + 1) μ} (ht : IsStandard t) :
    Function.Surjective (branchingMap ht) := by
  rw [← LinearMap.range_eq_top]
  apply top_unique
  intro y _
  rw [← (standardRealBasis (prefixTableau ht n (Nat.le_succ n))).sum_repr y]
  apply Submodule.sum_mem
  intro T _
  apply Submodule.smul_mem
  let u := prefixTableau ht n (Nat.le_succ n)
  obtain ⟨x, hx⟩ := branchingMap_lift_orbit ht (u.trans T.val.symm)
  refine ⟨x, hx.trans ?_⟩
  apply Subtype.ext
  rw [realSpechtRep_standardRealBasis_coe, standardRealBasis_coe]
  congr 2
  apply Equiv.ext
  intro i
  simp [relabel, u]

/-- The strict preceding step, including the zero step when the row is zero. -/
def lastRowSubspaceLT (t : Tableau (n + 1) μ) (r : ℕ) : Submodule ℝ (realSpan t) :=
  Submodule.span ℝ {x | ∃ T : {u : Tableau (n + 1) μ // IsStandard u},
    (rowWord T.val (Fin.last n)).val < r ∧ standardRealBasis t T = x}

theorem lastRowSubspaceLT_le (t : Tableau (n + 1) μ) (r : ℕ) :
    lastRowSubspaceLT t r ≤ lastRowSubspace t r := by
  apply Submodule.span_le.mpr
  rintro _ ⟨T, hT, rfl⟩
  exact Submodule.subset_span ⟨T, hT.le, rfl⟩

/-- Restriction annihilates the preceding filtration step. -/
theorem prefixSliceReal_eq_zero_of_mem_lastRowSubspaceLT {t : Tableau (n + 1) μ}
    (ht : IsStandard t) {x : realSpan t}
    (hx : x ∈ lastRowSubspaceLT t (rowWord t (Fin.last n)).val) :
    prefixSliceReal ht (Nat.le_succ n) x.val = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨T, hT, rfl⟩ := hx
    exact prefixSliceReal_standardRealBasis_eq_zero ht T hT
  | zero => simp
  | add x y hx hy ihx ihy => simp only [Submodule.coe_add, map_add, ihx, ihy, add_zero]
  | smul a x hx ih => simp only [Submodule.coe_smul, map_smul, ih, smul_zero]

/-- The kernel is exactly the preceding standard-basis filtration step. -/
theorem branchingMap_eq_zero_iff {t : Tableau (n + 1) μ} (ht : IsStandard t)
    (x : lastRowSubspace t (rowWord t (Fin.last n)).val) :
    branchingMap ht x = 0 ↔ x.val ∈ lastRowSubspaceLT t (rowWord t (Fin.last n)).val := by
  constructor
  · intro hx
    have hlead (U : {u : Tableau (n + 1) μ // IsStandard u})
        (hU : (rowWord t (Fin.last n)).val ≤ (rowWord U.val (Fin.last n)).val) :
        x.val.val (rowWord U.val) = 0 := by
      rcases hU.eq_or_lt with hU | hU
      · obtain ⟨w, hw⟩ := exists_extendPrefixWord_eq_rowWord ht U.property.1 hU.symm
        have he := congrArg (fun y => y.val w) hx
        change x.val.val (extendPrefixWord ht (Nat.le_succ n) w) = 0 at he
        rwa [hw] at he
      · exact (mem_lastRowSubspace_iff t _ x.val).mp x.property _ hU
    rw [← (standardRealBasis t).sum_repr x.val]
    apply Submodule.sum_mem
    intro T _
    by_cases hT : (rowWord T.val (Fin.last n)).val < (rowWord t (Fin.last n)).val
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨T, hT, rfl⟩)
    · rw [standardRealBasis_repr_eq_zero_of_leading_zero t x.val _ hlead T (le_of_not_gt hT),
        zero_smul]
      exact Submodule.zero_mem _
  · intro hx
    apply Subtype.ext
    exact prefixSliceReal_eq_zero_of_mem_lastRowSubspaceLT ht hx

/-- Kernel identification inside the filtration step. -/
theorem ker_branchingMap {t : Tableau (n + 1) μ} (ht : IsStandard t) :
    LinearMap.ker (branchingMap ht) =
      (lastRowSubspaceLT t (rowWord t (Fin.last n)).val).comap
        (lastRowSubspace t (rowWord t (Fin.last n)).val).subtype := by
  ext x
  exact branchingMap_eq_zero_iff ht x

/-- The branching quotient is the smaller Specht space, not an assumed model. -/
def branchingQuotientEquiv {t : Tableau (n + 1) μ} (ht : IsStandard t) :
    ((lastRowSubspace t (rowWord t (Fin.last n)).val) ⧸
      (lastRowSubspaceLT t (rowWord t (Fin.last n)).val).comap
        (lastRowSubspace t (rowWord t (Fin.last n)).val).subtype) ≃ₗ[ℝ]
      realSpan (prefixTableau ht n (Nat.le_succ n)) :=
  (Submodule.quotEquivOfEq _ _ (ker_branchingMap ht).symm).trans
    ((branchingMap ht).quotKerEquivOfSurjective (branchingMap_surjective ht))

@[simp] theorem branchingQuotientEquiv_mk {t : Tableau (n + 1) μ} (ht : IsStandard t)
    (x : lastRowSubspace t (rowWord t (Fin.last n)).val) :
    branchingQuotientEquiv ht (Submodule.Quotient.mk x) = branchingMap ht x := rfl

/-- The induced quotient map still restricts the actual word coefficients. -/
theorem branchingQuotientEquiv_mk_apply {t : Tableau (n + 1) μ} (ht : IsStandard t)
    (x : lastRowSubspace t (rowWord t (Fin.last n)).val)
    (w : Fin n → Fin ((prefixShape ht n (Nat.le_succ n)).colLen 0)) :
    (branchingQuotientEquiv ht (Submodule.Quotient.mk x)).val w =
      x.val.val (extendPrefixWord ht (Nat.le_succ n) w) := rfl

/-- Equivariance of restriction, on all representatives of the quotient. -/
theorem branchingMap_equivariant {t : Tableau (n + 1) μ} (ht : IsStandard t)
    (g : Equiv.Perm (Fin n)) (x : lastRowSubspace t (rowWord t (Fin.last n)).val) :
    branchingMap ht
      ⟨realSpechtRep t (prefixPerm (Nat.le_succ n) g) x.val,
        prefixPerm_mem_lastRowSubspace t _ g x.property⟩ =
      realSpechtRep (prefixTableau ht n (Nat.le_succ n)) g (branchingMap ht x) := by
  apply Subtype.ext
  exact prefixSliceReal_wordRepReal ht (Nat.le_succ n) g x.val.val

/-- Equivariance of the quotient equivalence, expressed on its surjective set of representatives. -/
theorem branchingQuotientEquiv_mk_action {t : Tableau (n + 1) μ} (ht : IsStandard t)
    (g : Equiv.Perm (Fin n)) (x : lastRowSubspace t (rowWord t (Fin.last n)).val) :
    branchingQuotientEquiv ht (Submodule.Quotient.mk
      ⟨realSpechtRep t (prefixPerm (Nat.le_succ n) g) x.val,
        prefixPerm_mem_lastRowSubspace t _ g x.property⟩) =
      realSpechtRep (prefixTableau ht n (Nat.le_succ n)) g
        (branchingQuotientEquiv ht (Submodule.Quotient.mk x)) :=
  branchingMap_equivariant ht g x

end BostConjecture.Specht
