module

public import BostConjecture.Arithmetic.QuotientSubmoduleDegree
public import BostConjecture.Arithmetic.Semistable

/-!
# Semistability of intrinsic quotient intervals

For a submodule of an induced quotient, take its integral inverse image,
then saturate it in the original bundle. Exact degree and unchanged rank
compare its slope with the corresponding generic interval. Consequently
ordinary interval inequalities imply semistability of the actual quotient.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct HarderNarasimhan

namespace BostConjecture.Arithmetic.HermitianMetric

variable {K : Type*} [Field K] [NumberField K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]
variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]

/-- Viewing a submodule of a submodule inside the original module preserves degree. -/
lemma degree_submodule_map (h : HermitianMetric (K := K) M)
    (T : Submodule (𝓞 K) M) (R : Submodule (𝓞 K) T) :
    ((h.submodule T).submodule R).degree = (h.submodule (R.map T.subtype)).degree := by
  let e := Submodule.equivMapOfInjective T.subtype T.injective_subtype R
  apply degree_eq_of_equiv _ _ e
  intro σ x y
  have he : (R.map T.subtype).subtype.comp e.toLinearMap = T.subtype.comp R.subtype := rfl
  change (h.fiber σ).inner
    ((fiberMap (R.map T.subtype).subtype σ).comp (fiberMap e.toLinearMap σ) x)
    ((fiberMap (R.map T.subtype).subtype σ).comp (fiberMap e.toLinearMap σ) y) = _
  rw [← fiberMap_comp, he, fiberMap_comp]
  rfl

omit [NumberField K] [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M] in
/-- The generic rank of a submodule does not depend on its intermediate ambient module. -/
lemma finrank_submodule_map (T : Submodule (𝓞 K) M) (R : Submodule (𝓞 K) T) :
    Module.finrank K (K ⊗[𝓞 K] R) =
      Module.finrank K (K ⊗[𝓞 K] (R.map T.subtype)) :=
  ((Submodule.equivMapOfInjective T.subtype T.injective_subtype R).baseChange
    (𝓞 K) K _ _).finrank_eq

/-- Nested restriction to an included submodule preserves its intrinsic degree. -/
lemma degree_submodule_comap (h : HermitianMetric (K := K) M)
    {P T : Submodule (𝓞 K) M} (hPT : P ≤ T) :
    ((h.submodule T).submodule (P.comap T.subtype)).degree = (h.submodule P).degree := by
  exact (h.degree_submodule_map T (P.comap T.subtype)).trans
    (congrArg (fun S : Submodule (𝓞 K) M => (h.submodule S).degree)
      ((Submodule.map_comap_subtype T P).trans (inf_eq_right.mpr hPT)))

omit [NumberField K] [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M] in
/-- Nested restriction preserves generic rank. -/
lemma finrank_submodule_comap {P T : Submodule (𝓞 K) M} (hPT : P ≤ T) :
    Module.finrank K (K ⊗[𝓞 K] (P.comap T.subtype)) =
      Module.finrank K (K ⊗[𝓞 K] P) := by
  rw [finrank_submodule_map, Submodule.map_comap_subtype, inf_eq_right.mpr hPT]

/-- Every positive-rank submodule of an interval quotient is bounded by the
saturated interval obtained from its inverse image. -/
theorem quotient_submodule_slope_le_interval (h : HermitianMetric (K := K) M)
    {X Y : Submodule K (K ⊗[𝓞 K] M)} (hXY : X ≤ Y)
    (N : Submodule (𝓞 K) (integralPart Y ⧸ (integralPart X).comap (integralPart Y).subtype))
    (hN : 0 < Module.finrank K (K ⊗[𝓞 K] N)) :
    ∃ Z : Submodule K (K ⊗[𝓞 K] M), ∃ _ : X < Z, Z ≤ Y ∧
      (((h.submodule (integralPart Y)).quotient
        ((integralPart X).comap (integralPart Y).subtype)).submodule N).slope ≤
      ((h.submodule (integralPart Z)).quotient
        ((integralPart X).comap (integralPart Z).subtype)).slope := by
  let T := integralPart Y
  let P := (integralPart X).comap T.subtype
  let R := N.comap P.mkQ
  let S := R.map T.subtype
  let Z := S.baseChange K
  have hPR : P ≤ R := le_quotient_preimage P N
  have hXS : integralPart X ≤ S := by
    intro x hx
    let y : T := ⟨x, integralPart_mono hXY hx⟩
    exact ⟨y, hPR hx, rfl⟩
  have hST : S ≤ T := by
    rintro x ⟨y, _, rfl⟩
    exact y.property
  have hXZ : X ≤ Z := by
    rw [← baseChange_integralPart X]
    exact Submodule.baseChange_mono K hXS
  have hZY : Z ≤ Y := by
    rw [← baseChange_integralPart Y]
    exact Submodule.baseChange_mono K hST
  have hrR : Module.finrank K (K ⊗[𝓞 K] R) = Module.finrank K Z := by
    let : Module.Flat (𝓞 K) K := IsLocalization.flat K (nonZeroDivisors (𝓞 K))
    exact (finrank_submodule_map T R).trans
      (Submodule.toBaseChange.toLinearEquiv K S).finrank_eq
  have hrP : Module.finrank K (K ⊗[𝓞 K] P) = Module.finrank K X :=
    (finrank_submodule_comap (integralPart_mono hXY)).trans (integralPart_generic_finrank X)
  have hrN : Module.finrank K (K ⊗[𝓞 K] N) =
      Module.finrank K Z - Module.finrank K X := by
    rw [finrank_quotient_submodule P N, hrR, hrP]
  have hXZ' : X < Z := lt_of_le_of_ne hXZ (by
    intro he
    rw [← he, Nat.sub_self] at hrN
    omega)
  refine ⟨Z, hXZ', hZY, ?_⟩
  have hdN := (h.submodule T).degree_quotient_submodule P N
  rw [degree_submodule_map, degree_submodule_comap h (integralPart_mono hXY)] at hdN
  have hd : ((((h.submodule T).quotient P).submodule N)).degree ≤
      h.subspaceDegree Z - h.subspaceDegree X := by
    rw [hdN]
    exact sub_le_sub_right (h.degree_le_saturation S) _
  rw [slope, slope, hrN, subspaceQuotient_finrank hXZ'.le,
    ← subspaceDegree_sub_eq_quotient h hXZ'.le]
  exact div_le_div_of_nonneg_right hd (Nat.cast_nonneg _)

/-- Semistability on a generic interval is genuine semistability of its
induced integral quotient, against every integral submodule. -/
theorem quotient_isSemistable_of_interval (h : HermitianMetric (K := K) M)
    {X Y : Submodule K (K ⊗[𝓞 K] M)} (hXY : X < Y)
    (hs : ∀ Z (_ : X < Z), Z ≤ Y →
      ((h.submodule (integralPart Z)).quotient
        ((integralPart X).comap (integralPart Z).subtype)).slope ≤
      ((h.submodule (integralPart Y)).quotient
        ((integralPart X).comap (integralPart Y).subtype)).slope) :
    ((h.submodule (integralPart Y)).quotient
      ((integralPart X).comap (integralPart Y).subtype)).IsSemistable := by
  intro N hN
  obtain ⟨Z, hXZ, hZY, hNZ⟩ := h.quotient_submodule_slope_le_interval hXY.le N hN
  exact hNZ.trans (hs Z hXZ hZY)

/-- Genuine quotient semistability is equivalent to all generic interval inequalities. -/
theorem quotient_isSemistable_iff_interval (h : HermitianMetric (K := K) M)
    {X Y : Submodule K (K ⊗[𝓞 K] M)} (hXY : X < Y) :
    ((h.submodule (integralPart Y)).quotient
      ((integralPart X).comap (integralPart Y).subtype)).IsSemistable ↔
    ∀ Z (_ : X < Z), Z ≤ Y →
      ((h.submodule (integralPart Z)).quotient
        ((integralPart X).comap (integralPart Z).subtype)).slope ≤
      ((h.submodule (integralPart Y)).quotient
        ((integralPart X).comap (integralPart Y).subtype)).slope := by
  refine ⟨?_, h.quotient_isSemistable_of_interval hXY⟩
  intro hs Z hXZ hZY
  let T := integralPart Y
  let P := (integralPart X).comap T.subtype
  let R := (integralPart Z).comap T.subtype
  let N := R.map P.mkQ
  have hPR : P ≤ R := Submodule.comap_mono (integralPart_mono hXZ.le)
  have he : N.comap P.mkQ = R := by
    exact Submodule.comap_map_eq_self (by simpa using hPR)
  have hrR : Module.finrank K (K ⊗[𝓞 K] R) = Module.finrank K Z :=
    (finrank_submodule_comap (integralPart_mono hZY)).trans (integralPart_generic_finrank Z)
  have hrP : Module.finrank K (K ⊗[𝓞 K] P) = Module.finrank K X :=
    (finrank_submodule_comap (integralPart_mono hXY.le)).trans (integralPart_generic_finrank X)
  have hrN : Module.finrank K (K ⊗[𝓞 K] N) =
      Module.finrank K Z - Module.finrank K X := by
    rw [finrank_quotient_submodule P N, he, hrR, hrP]
  have hdN : (((h.submodule T).quotient P).submodule N).degree =
      h.subspaceDegree Z - h.subspaceDegree X := by
    have hd := (h.submodule T).degree_quotient_submodule P N
    have he' := congrArg (fun U : Submodule (𝓞 K) T => ((h.submodule T).submodule U).degree) he
    rw [he', degree_submodule_comap h (integralPart_mono hZY),
      degree_submodule_comap h (integralPart_mono hXY.le)] at hd
    exact hd
  have hN : 0 < Module.finrank K (K ⊗[𝓞 K] N) := by
    rw [hrN]
    exact Nat.sub_pos_of_lt (Submodule.finrank_strictMono hXZ)
  have hb := hs N hN
  rw [slope, hdN, hrN] at hb
  rw [slope, ← subspaceDegree_sub_eq_quotient h hXZ.le, subspaceQuotient_finrank hXZ.le]
  exact hb

/-- The interval game and the actual induced Hermitian quotient have the same semistability. -/
theorem quotient_isSemistable_iff_game (h : HermitianMetric (K := K) M)
    {X Y : Submodule K (K ⊗[𝓞 K] M)} (hXY : X < Y) :
    ((h.submodule (integralPart Y)).quotient
      ((integralPart X).comap (integralPart Y).subtype)).IsSemistable ↔
    ((BostConjecture.Subspace.slope h.subspaceDegree).restrict ⟨X, Y, hXY⟩).IsSemistable := by
  rw [h.quotient_isSemistable_iff_interval hXY, BostConjecture.Slope.isSemistable_restrict_iff]
  simp only [h.subspaceSlope_eq_quotient, DedekindCut.principal_le_principal]

end BostConjecture.Arithmetic.HermitianMetric
