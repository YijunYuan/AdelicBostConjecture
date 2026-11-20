/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.ExternalCode.TauCeti.RepresentationTheory.Specht.Straightening
public import BostConjecture.Specht.Lattice.Metric

/-!
# Standard polytabloids as a real basis

Rational straightening and coefficientwise scalar extension identify the real
orbit span with the span of standard polytabloids. Their integral coordinates
then provide the full-rank sublattice needed for the Gram covolume bound.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Specht

open OAI.Saxl Module

variable {n d : ℕ} {μ : YoungDiagram}

instance standardTableauFintype : Fintype {t : Tableau n μ // IsStandard t} :=
  Fintype.ofFinite _

/-- Coefficientwise extension of rational words to orthonormal real word coordinates. -/
private def ratRealCast (n d : ℕ) :
    ((Fin n → Fin d) → ℚ) →ₗ[ℚ] EuclideanSpace ℝ (Fin n → Fin d) where
  toFun x := WithLp.toLp 2 (fun w => (x w : ℝ))
  map_add' x y := by ext w; simp
  map_smul' a x := by ext w; simp [← Rat.cast_smul_eq_qsmul ℝ]

private theorem ratRealCast_polytabloid (u : Tableau n μ) :
    ratRealCast n (μ.colLen 0) (polytabloidRat u) =
      realCast n (μ.colLen 0) (polytabloidInt u) := by
  ext w
  simp [ratRealCast, realCast, polytabloidRat]

/-- Rational straightening also spans the same integral vectors over the reals. -/
theorem realCast_polytabloid_mem_span_standard (u : Tableau n μ) :
    realCast n (μ.colLen 0) (polytabloidInt u) ∈ Submodule.span ℝ
      (Set.range fun T : {t : Tableau n μ // IsStandard t} =>
        realCast n (μ.colLen 0) (polytabloidInt T.val)) := by
  rw [← ratRealCast_polytabloid]
  have h := polytabloidRat_mem_span_standard u
  generalize he : polytabloidRat u = x at h ⊢
  clear he
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨T, rfl⟩ := hx
    rw [ratRealCast_polytabloid]
    exact Submodule.subset_span ⟨T, rfl⟩
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [map_add, SetLike.mem_coe] using Submodule.add_mem _ ihx ihy
  | smul a x hx ih =>
    simpa only [map_smul, ← Rat.cast_smul_eq_qsmul ℝ] using Submodule.smul_mem _ (a : ℝ) ih

/-- Every polytabloid of the shape belongs to the same integral orbit lattice. -/
theorem polytabloidInt_mem_orbitLattice_of_tableau (t u : Tableau n μ) :
    polytabloidInt u ∈ orbitLattice t := by
  rw [orbitLattice_eq_span_polytabloids]
  exact Submodule.subset_span ⟨u, rfl⟩

/-- The real orbit span is exactly the span of standard integral polytabloids. -/
theorem realSpan_eq_span_standard (t : Tableau n μ) :
    realSpan t = Submodule.span ℝ
      (Set.range fun T : {t : Tableau n μ // IsStandard t} =>
        realCast n (μ.colLen 0) (polytabloidInt T.val)) := by
  apply le_antisymm
  · rw [realSpan, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [orbitLattice_eq_span_polytabloids] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, rfl⟩ := hx
      exact realCast_polytabloid_mem_span_standard u
    | zero => simp
    | add x y hx hy ihx ihy =>
      simpa only [map_add, SetLike.mem_coe] using Submodule.add_mem _ ihx ihy
    | smul a x hx ih =>
      simpa only [map_smul, ← Int.cast_smul_eq_zsmul ℝ, SetLike.mem_coe] using
        Submodule.smul_mem _ (a : ℝ) ih
  · rw [Submodule.span_le]
    rintro _ ⟨T, rfl⟩
    exact Submodule.subset_span
      ⟨polytabloidInt T.val, polytabloidInt_mem_orbitLattice_of_tableau t T.val, rfl⟩

/-- Standard polytabloids remain independent in orthonormal real word coordinates. -/
theorem linearIndependent_real_standard_polytabloid :
    LinearIndependent ℝ (fun T : {t : Tableau n μ // IsStandard t} =>
      realCast n (μ.colLen 0) (polytabloidInt T.val)) := by
  apply LinearIndependent.of_comp (EuclideanSpace.equiv (Fin n → Fin (μ.colLen 0)) ℝ).toLinearMap
  exact linearIndependent_standard_polytabloid ℝ

/-- This paper, Remark 3.8. The standard basis theorem is [Kuenzer–Nebe, Section 2.1][kn] and
[Ryom-Hansen, Section 2][rh].

The standard polytabloids form a real basis of the actual orbit span. -/
def standardRealBasis (t : Tableau n μ) :
    Basis {t : Tableau n μ // IsStandard t} ℝ (realSpan t) :=
  (Basis.span linearIndependent_real_standard_polytabloid).map
    (LinearEquiv.ofEq _ _ (realSpan_eq_span_standard t).symm)

@[simp] theorem standardRealBasis_coe (t : Tableau n μ)
    (T : {t : Tableau n μ // IsStandard t}) :
    (standardRealBasis t T : EuclideanSpace ℝ (Fin n → Fin (μ.colLen 0))) =
      realCast n (μ.colLen 0) (polytabloidInt T.val) := by
  simp [standardRealBasis, Basis.span_apply]

/-- The standard real basis consists of vectors in the full integral orbit lattice. -/
theorem standardRealBasis_mem_spanLattice (t : Tableau n μ)
    (T : {t : Tableau n μ // IsStandard t}) : standardRealBasis t T ∈ spanLattice t := by
  change (standardRealBasis t T : EuclideanSpace ℝ (Fin n → Fin (μ.colLen 0))) ∈ realLattice t
  rw [standardRealBasis_coe]
  exact ⟨polytabloidInt T.val, polytabloidInt_mem_orbitLattice_of_tableau t T.val, rfl⟩

/-- This paper, Proposition 3.15, rank equality in (3.13). See [Kuenzer–Nebe, Section 2.1][kn].

The canonical integral orbit rank equals the number of standard tableaux. -/
theorem finrank_orbitLattice_eq_card_standard (t : Tableau n μ) :
    finrank ℤ (orbitLattice t) = Fintype.card {t : Tableau n μ // IsStandard t} := by
  rw [(latticeEquiv t).finrank_eq, ZLattice.rank ℝ (spanLattice t)]
  exact finrank_eq_card_basis (standardRealBasis t)

/-- This paper, equation (3.17), upper bound.

The logarithmic standard Gram bound, with its basis and integrality hypotheses discharged. -/
theorem two_mul_log_covolume_le_log_det_standard_gram (t : Tableau n μ) :
    2 * Real.log (ZLattice.covolume (spanLattice t)) ≤
      Real.log (Matrix.gram ℝ (standardRealBasis t)).det := by
  classical
  exact two_mul_log_covolume_le_log_det_gram t (standardRealBasis t)
    (standardRealBasis_mem_spanLattice t)

end BostConjecture.Specht
