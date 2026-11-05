module

public import BostConjecture.Arithmetic.LineCoordinates
public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient

/-!
# The index of fractional ideals

For nonzero fractional ideals `J ≤ I`, their additive relative index equals
`N(J) / N(I)`. The proof uses Mathlib's integral bases of fractional ideals,
the norm as a change-of-basis determinant, and the index-determinant theorem.
It does not require either ideal to be principal.
-/

@[expose] public section

noncomputable section

open NumberField Module
open scoped nonZeroDivisors

namespace BostConjecture.Arithmetic

variable {K : Type*} [Field K] [NumberField K]

private def idealBasisIndexEquiv (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Free.ChooseBasisIndex ℤ (𝓞 K) ≃ Free.ChooseBasisIndex ℤ I :=
  Fintype.equivOfCardEq (by
    rw [← finrank_eq_card_chooseBasisIndex, ← finrank_eq_card_chooseBasisIndex,
      NumberField.fractionalIdeal_rank])

private def idealBasis (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Basis (Free.ChooseBasisIndex ℤ (𝓞 K)) ℚ K :=
  (basisOfFractionalIdeal K I).reindex (idealBasisIndexEquiv I).symm

private lemma idealBasis_closure (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (I.val : Submodule (𝓞 K) K).toAddSubgroup = AddSubgroup.closure (Set.range (idealBasis I)) := by
  have hspan : Submodule.span ℤ (Set.range (idealBasis I)) =
      (I.val : Submodule (𝓞 K) K).restrictScalars ℤ := by
    ext x
    simp only [idealBasis, Basis.coe_reindex, Equiv.symm_symm, EquivLike.range_comp]
    exact NumberField.mem_span_basisOfFractionalIdeal K
  ext x
  change x ∈ (I.val : Submodule (𝓞 K) K).restrictScalars ℤ ↔
    x ∈ (AddSubgroup.closure (Set.range (idealBasis I))).toIntSubmodule
  rw [AddSubgroup.toIntSubmodule_closure, hspan]

/-- The relative additive index of nonzero fractional ideals is their norm ratio. -/
theorem fractionalIdeal_relIndex (I J : FractionalIdeal (𝓞 K)⁰ K)
    (hI : I ≠ 0) (hJ : J ≠ 0) (hJI : J ≤ I) :
    ((J : Submodule (𝓞 K) K).toAddSubgroup.relIndex
      (I : Submodule (𝓞 K) K).toAddSubgroup : ℚ) =
      FractionalIdeal.absNorm J / FractionalIdeal.absNorm I := by
  classical
  let i := Units.mk0 I hI
  let j := Units.mk0 J hJ
  have hi := det_basisOfFractionalIdeal_eq_absNorm K i (idealBasisIndexEquiv i)
  have hj := det_basisOfFractionalIdeal_eq_absNorm K j (idealBasisIndexEquiv j)
  change |(integralBasis K).det (idealBasis i)| = FractionalIdeal.absNorm I at hi
  change |(integralBasis K).det (idealBasis j)| = FractionalIdeal.absNorm J at hj
  have hindex := AddSubgroup.relIndex_eq_abs_det _ _ hJI (idealBasis j) (idealBasis i)
    (idealBasis_closure j) (idealBasis_closure i)
  change ((J : Submodule (𝓞 K) K).toAddSubgroup.relIndex
    (I : Submodule (𝓞 K) K).toAddSubgroup : ℚ) = _ at hindex
  rw [hindex]
  apply (eq_div_iff (FractionalIdeal.absNorm_eq_zero_iff.not.mpr hI)).mpr
  rw [← hi, ← hj, ← abs_mul, mul_comm, Basis.det_mul_det]

/-- The finite quotient by a nonzero integral section has cardinality given by
the ratio of the two fractional-ideal norms in any injective coordinate. -/
theorem coordinate_quotient_card {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]
    [Module.Finite (𝓞 K) M] [Nontrivial M]
    (f : M →ₗ[𝓞 K] K) (hf : Function.Injective f) {x : M} (hx : x ≠ 0) :
    (Nat.card (M ⧸ (𝓞 K ∙ x)) : ℚ) =
      FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 K)⁰ (f x)) /
        FractionalIdeal.absNorm (coordinateIdeal f) := by
  have hfx : f x ≠ 0 := fun heq => hx (hf (by simpa using heq))
  have hmap : (𝓞 K ∙ x).toAddSubgroup.map f.toAddMonoidHom =
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ (f x) : Submodule (𝓞 K) K).toAddSubgroup := by
    change ((𝓞 K ∙ x).map f).toAddSubgroup = _
    rw [Submodule.map_span, Set.image_singleton]
    rfl
  have hi := AddSubgroup.relIndex_map_map_of_injective (f := f.toAddMonoidHom)
    (𝓞 K ∙ x).toAddSubgroup ⊤ hf
  rw [hmap, AddSubgroup.map_top, ← f.range_toAddSubgroup,
    AddSubgroup.relIndex_top_right] at hi
  have hn := fractionalIdeal_relIndex (coordinateIdeal f)
    (FractionalIdeal.spanSingleton (𝓞 K)⁰ (f x)) (coordinateIdeal_ne_zero f hf)
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hfx)
    (FractionalIdeal.spanSingleton_le_iff_mem.mpr ⟨x, rfl⟩)
  change ((FractionalIdeal.spanSingleton (𝓞 K)⁰ (f x) : Submodule (𝓞 K) K).toAddSubgroup.relIndex
    f.range.toAddSubgroup : ℚ) = _ at hn
  rw [hi] at hn
  exact hn

/-- The quotient in the section formula is genuinely finite. -/
theorem coordinate_quotient_finite {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]
    [Module.Finite (𝓞 K) M] [Nontrivial M]
    (f : M →ₗ[𝓞 K] K) (hf : Function.Injective f) {x : M} (hx : x ≠ 0) :
    Finite (M ⧸ (𝓞 K ∙ x)) := by
  apply Nat.finite_of_card_ne_zero
  intro hzero
  have hn := coordinate_quotient_card f hf hx
  rw [hzero, Nat.cast_zero] at hn
  have hfx : f x ≠ 0 := fun heq => hx (hf (by simpa using heq))
  have hp : FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 K)⁰ (f x)) ≠ 0 :=
    FractionalIdeal.absNorm_eq_zero_iff.not.mpr
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hfx)
  have hI : FractionalIdeal.absNorm (coordinateIdeal f) ≠ 0 :=
    FractionalIdeal.absNorm_eq_zero_iff.not.mpr (coordinateIdeal_ne_zero f hf)
  exact (div_ne_zero hp hI) hn.symm

end BostConjecture.Arithmetic
