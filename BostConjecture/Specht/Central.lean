module

public import BostConjecture.Specht.Content

/-!
# The central transposition sum and total content

The existing rank-one column antisymmetrizer on the complex tabloid module
identifies the central transposition action. The scalar is computed by the
integral word coefficients, then transported to the actual real Specht span.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Specht

open OAI.Saxl

variable {n : ℕ} {μ : YoungDiagram}

private theorem sum_symmetric_pairs {M : Type*} [AddCommGroup M]
    (f : Fin n → Fin n → M) (hf : ∀ i j, f i j = f j i) :
    ∑ i, ∑ j, f i j = (∑ i, f i i) +
      (∑ i, ∑ j ∈ Finset.Iio i, f j i) + (∑ i, ∑ j ∈ Finset.Iio i, f j i) := by
  classical
  have he (i j : Fin n) : f i j =
      (if j < i then f i j else 0) + (if i = j then f i j else 0) +
        (if i < j then f i j else 0) := by
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h, h.ne, h.not_gt]
    · simp
    · simp [h, h.ne', h.not_gt]
  have hfilter (i : Fin n) : Finset.univ.filter (fun j => j < i) = Finset.Iio i := by
    ext j
    simp
  have hl : (∑ i, ∑ j, if j < i then f i j else 0) =
      ∑ i, ∑ j ∈ Finset.Iio i, f j i := by
    simp only [← Finset.sum_filter, hfilter]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hf i j
  have hu : (∑ i, ∑ j, if i < j then f i j else 0) =
      ∑ i, ∑ j ∈ Finset.Iio i, f j i := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_filter, hfilter]
  calc
    ∑ i, ∑ j, f i j = ∑ i, ∑ j,
        ((if j < i then f i j else 0) + (if i = j then f i j else 0) +
          (if i < j then f i j else 0)) := by
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => he i j
    _ = _ := by
      simp only [Finset.sum_add_distrib, hl, hu, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true]
      abel

/-- The central sum of all transpositions in the existing complex word action. -/
def centralWordOperator (n d : ℕ) : Module.End ℂ (WordSpace n d) :=
  ∑ j, ∑ i ∈ Finset.Iio j, wordRep n d (Equiv.swap i j)

private theorem wordRep_commute_all_swaps (d : ℕ) (g : Equiv.Perm (Fin n)) :
    Commute (wordRep n d g) (∑ i : Fin n, ∑ j : Fin n, wordRep n d (Equiv.swap i j)) := by
  change _ * _ = _ * _
  simp only [Finset.mul_sum, Finset.sum_mul, ← map_mul, Equiv.mul_swap_eq_swap_mul]
  calc
    _ = ∑ i : Fin n, ∑ j : Fin n, wordRep n d (Equiv.swap (g i) j * g) := by
      exact Finset.sum_congr rfl fun i _ =>
        Equiv.sum_comp g (fun j => wordRep n d (Equiv.swap (g i) j * g))
    _ = _ := Equiv.sum_comp g (fun i => ∑ j : Fin n, wordRep n d (Equiv.swap i j * g))

/-- Conjugation permutes the transpositions in the central sum. -/
theorem wordRep_commute_centralWordOperator (d : ℕ) (g : Equiv.Perm (Fin n)) :
    Commute (wordRep n d g) (centralWordOperator n d) := by
  have h := (wordRep_commute_all_swaps d g).eq
  have hp := sum_symmetric_pairs (fun i j : Fin n => wordRep n d (Equiv.swap i j))
    (fun i j => by rw [Equiv.swap_comm])
  simp only [Equiv.swap_self, ← Equiv.Perm.one_def, map_one,
    Finset.sum_const, Finset.card_univ] at hp
  rw [hp] at h
  simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul] at h
  change _ + wordRep n d g * centralWordOperator n d +
      wordRep n d g * centralWordOperator n d =
    _ + centralWordOperator n d * wordRep n d g +
      centralWordOperator n d * wordRep n d g at h
  have hh : (2 : ℂ) • (wordRep n d g * centralWordOperator n d) =
      (2 : ℂ) • (centralWordOperator n d * wordRep n d g) := by
    simp only [two_smul]
    exact add_left_cancel (by simpa only [add_assoc] using h)
  exact smul_right_injective _ (by norm_num : (2 : ℂ) ≠ 0) hh

/-- The existing rank-one column antisymmetrizer identifies the central action's line. -/
theorem centralWordOperator_polytabloid_mem (t : Tableau n μ) :
    centralWordOperator n (μ.colLen 0) (polytabloid t) ∈
      Submodule.span ℂ {polytabloid t} := by
  classical
  let := Fintype.ofFinite (columnGroup t)
  have hx : centralWordOperator n (μ.colLen 0) (Pi.single (rowWord t) 1) ∈ tabloidSub t := by
    simp only [centralWordOperator, LinearMap.sum_apply]
    exact Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun i _ =>
      (tabloidSub t).apply_mem_toSubmodule _ (mem_cyclic _ _)
  have hc := columnAlt_tabloid t hx
  have he : columnAlt t * centralWordOperator n (μ.colLen 0) =
      centralWordOperator n (μ.colLen 0) * columnAlt t := by
    unfold columnAlt
    simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]
    exact Finset.sum_congr rfl fun g _ =>
      congrArg (fun x => _ • x) (wordRep_commute_centralWordOperator (μ.colLen 0) g.val).eq
  rw [← Module.End.mul_apply, he, Module.End.mul_apply, columnAlt_row] at hc
  exact hc

/-- Sum of the signed contents of all boxes of a Young diagram. -/
def diagramContent (μ : YoungDiagram) : ℤ := by
  letI : Fintype μ := inferInstanceAs (Fintype μ.cells)
  exact ∑ b : μ, ((b.val.2 : ℤ) - b.val.1)

theorem sum_tableauContent (t : Tableau n μ) :
    ∑ j, tableauContent t j = diagramContent μ := by
  let : Fintype μ := inferInstanceAs (Fintype μ.cells)
  exact Equiv.sum_comp t (fun b : μ => (b.val.2 : ℤ) - b.val.1)

/-- The central scalar is determined by the proved integral word coefficients. -/
theorem centralWordOperator_polytabloid_rowWord {t : Tableau n μ} (ht : IsStandard t) :
    centralWordOperator n (μ.colLen 0) (polytabloid t) (rowWord t) =
      (diagramContent μ : ℂ) := by
  classical
  have hc (w) : polytabloid t w = (polytabloidInt t w : ℂ) :=
    (congrFun (complexCast_polytabloid t) w).symm
  simp only [centralWordOperator, LinearMap.sum_apply, Finset.sum_apply]
  change (∑ j, ∑ i ∈ Finset.Iio j, polytabloid t (rowWord t ∘ Equiv.swap i j)) = _
  simp_rw [hc, ← Int.cast_sum, sum_polytabloidInt_rowWord_swap ht]
  rw [sum_tableauContent]

/-- The central sum acts by the total diagram content on a standard polytabloid. -/
theorem centralWordOperator_polytabloid {t : Tableau n μ} (ht : IsStandard t) :
    centralWordOperator n (μ.colLen 0) (polytabloid t) =
      (diagramContent μ : ℂ) • polytabloid t := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (centralWordOperator_polytabloid_mem t)
  have he := congrFun hc (rowWord t)
  simp only [Pi.smul_apply, smul_eq_mul, polytabloid_rowWord, mul_one,
    centralWordOperator_polytabloid_rowWord ht] at he
  simpa only [he] using hc.symm

/-- The central content identity already holds before scalar extension. -/
theorem sum_wordRepInt_polytabloid_eq_content {t : Tableau n μ} (ht : IsStandard t) :
    ∑ j, ∑ i ∈ Finset.Iio j, wordRepInt n (μ.colLen 0) (Equiv.swap i j) (polytabloidInt t) =
      diagramContent μ • polytabloidInt t := by
  apply complexCast_injective
  simpa only [map_sum, complexCast_wordRep, complexCast_polytabloid, map_smul,
    Int.cast_smul_eq_zsmul, centralWordOperator, LinearMap.sum_apply] using
    centralWordOperator_polytabloid ht

/-- The central sum has total content as its scalar on the actual real standard basis. -/
theorem sum_murphyOperator_standardRealBasis (t : Tableau n μ)
    (T : {u : Tableau n μ // IsStandard u}) :
    (∑ j, murphyOperator t j) (standardRealBasis t T) =
      (diagramContent μ : ℝ) • standardRealBasis t T := by
  apply Subtype.ext
  simp only [murphyOperator, LinearMap.sum_apply, Submodule.coe_sum, Submodule.coe_smul,
    realSpechtRep_coe, standardRealBasis_coe, wordRepReal_realCast]
  have h := congrArg (realCast n (μ.colLen 0))
    (sum_wordRepInt_polytabloid_eq_content T.property)
  simpa only [map_sum, map_smul, Int.cast_smul_eq_zsmul] using h

/-- The sum of the actual real Murphy operators is the total-content scalar operator. -/
theorem sum_murphyOperator_eq (t : Tableau n μ) :
    (∑ j, murphyOperator t j) = (diagramContent μ : ℝ) • (1 : Module.End ℝ (realSpan t)) := by
  apply (standardRealBasis t).ext
  intro T
  simpa using sum_murphyOperator_standardRealBasis t T

/-- The central content identity on every vector of the canonical integral orbit lattice. -/
theorem sum_wordRepInt_eq_content_of_mem_orbitLattice (t : Tableau n μ)
    {z : (Fin n → Fin (μ.colLen 0)) → ℤ} (hz : z ∈ orbitLattice t) :
    ∑ j, ∑ i ∈ Finset.Iio j, wordRepInt n (μ.colLen 0) (Equiv.swap i j) z =
      diagramContent μ • z := by
  let x : realSpan t := ⟨realCast n (μ.colLen 0) z, Submodule.subset_span ⟨z, hz, rfl⟩⟩
  have h := congrArg (fun f : Module.End ℝ (realSpan t) => (f x).val)
    (sum_murphyOperator_eq t)
  simp only [murphyOperator, LinearMap.sum_apply, Submodule.coe_sum, LinearMap.smul_apply,
    Module.End.one_apply, Submodule.coe_smul, realSpechtRep_coe] at h
  apply realCast_injective
  simpa only [map_sum, map_smul, ← wordRepReal_realCast, Int.cast_smul_eq_zsmul] using h

end BostConjecture.Specht
