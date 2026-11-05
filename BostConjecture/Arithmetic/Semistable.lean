module

public import BostConjecture.Arithmetic.SubspaceSupermodular
public import BostConjecture.Arithmetic.DegreeIsometry
public import BostConjecture.Slope.FiniteLength

/-!
# Intrinsic Hermitian semistability

Semistability quantifies over all positive-rank integral submodules. Saturation
and the proved determinant degree identify it with ordinary semistability on
the generic subspace lattice, including nonfree projective modules.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct HarderNarasimhan

namespace BostConjecture.Arithmetic.HermitianMetric

variable {K : Type*} [Field K] [NumberField K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]
variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]

/-- Every positive-rank integral submodule has slope at most the ambient slope. -/
def IsSemistable (h : HermitianMetric (K := K) M) : Prop :=
  ∀ P : Submodule (𝓞 K) M, 0 < Module.finrank K (K ⊗[𝓞 K] P) →
    (h.submodule P).slope ≤ h.slope

@[simp]
lemma degree_submodule_top (h : HermitianMetric (K := K) M) :
    (h.submodule ⊤).degree = h.degree :=
  degree_eq_of_equiv _ _ (Submodule.topEquiv : (⊤ : Submodule (𝓞 K) M) ≃ₗ[𝓞 K] M)
    (fun _ _ _ => rfl)

@[simp]
lemma slope_submodule_top (h : HermitianMetric (K := K) M) :
    (h.submodule ⊤).slope = h.slope := by
  rw [slope, slope, degree_submodule_top]
  rw [(Submodule.topEquiv.baseChange (𝓞 K) K (⊤ : Submodule (𝓞 K) M) M).finrank_eq]

/-- Saturation preserves generic rank and increases slope. -/
lemma slope_le_saturation (h : HermitianMetric (K := K) M)
    (P : Submodule (𝓞 K) M) :
    (h.submodule P).slope ≤ (h.submodule (integralPart (P.baseChange K))).slope := by
  let : Module.Flat (𝓞 K) K := IsLocalization.flat K (nonZeroDivisors (𝓞 K))
  have hr := (Submodule.toBaseChange.toLinearEquiv K P).finrank_eq.trans
    (integralPart_generic_finrank (P.baseChange K)).symm
  rw [slope, slope, hr]
  exact div_le_div_of_nonneg_right (h.degree_le_saturation P) (Nat.cast_nonneg _)

/-- Testing saturated integral parts suffices for genuine integral semistability. -/
theorem isSemistable_iff_subspaces (h : HermitianMetric (K := K) M) :
    h.IsSemistable ↔ ∀ X : Submodule K (K ⊗[𝓞 K] M), ⊥ < X →
      (h.submodule (integralPart X)).slope ≤ h.slope := by
  constructor
  · intro hs X hX
    apply hs
    rw [integralPart_generic_finrank]
    exact (Submodule.finrank_strictMono hX).trans_le' (by simp)
  · intro hs P hP
    let : Module.Flat (𝓞 K) K := IsLocalization.flat K (nonZeroDivisors (𝓞 K))
    have hX : ⊥ < P.baseChange K := by
      apply bot_lt_iff_ne_bot.mpr
      intro he
      have hr := (Submodule.toBaseChange.toLinearEquiv K P).finrank_eq
      rw [he] at hr
      simp [hr] at hP
    exact (h.slope_le_saturation P).trans (hs _ hX)

variable [Nontrivial (K ⊗[𝓞 K] M)]

/-- The total generic payoff is the actual ambient Hermitian slope. -/
lemma subspaceSlope_top (h : HermitianMetric (K := K) M) :
    BostConjecture.Subspace.slope h.subspaceDegree ⊤ = DedekindCut.principal h.slope := by
  rw [show (⊤ : StrictIntvl (Submodule K (K ⊗[𝓞 K] M))) = ⟨⊥, ⊤, bot_lt_top⟩ from rfl,
    subspaceSlope_apply_bot, integralPart_top, slope_submodule_top]

/-- The finite-length game specializes to semistability against all integral submodules. -/
theorem isSemistable_iff_game (h : HermitianMetric (K := K) M) :
    h.IsSemistable ↔ (BostConjecture.Subspace.slope h.subspaceDegree).IsSemistable := by
  rw [BostConjecture.Slope.isSemistable_iff, h.isSemistable_iff_subspaces]
  simp only [h.subspaceSlope_apply_bot, h.subspaceSlope_top,
    DedekindCut.principal_le_principal]

end BostConjecture.Arithmetic.HermitianMetric
