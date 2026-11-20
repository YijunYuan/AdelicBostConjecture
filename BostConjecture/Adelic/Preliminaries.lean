/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Basic
public import ArakelovGeometry.AdelicVectorBundle.Construction.Tensor.Pair
public import ArakelovGeometry.AdelicVectorBundle.Degree.Basic
public import ArakelovGeometry.AdelicVectorBundle.Dual.Restriction
public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Hermitian.Degree
public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Hermitian.Dual
public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Hermitian.Uniqueness
public import ArakelovGeometry.AdelicVectorBundle.Operator.StrongHeight
public import ArakelovGeometry.AdelicVectorBundle.Slope.LinearMap
public import ArakelovGeometry.AdelicVectorBundle.Slope.LinearMapFinite
public import ArakelovGeometry.AdelicVectorBundle.Tensor.Hermitian
public import BostConjecture.Adelic.Basic
public import BostConjecture.Adelic.Slope.DeterminantPower

/-!
# Hermitian adelic preliminaries

Proposition 2.3, Proposition 2.4 and Theorem 2.5 of this paper are assembled here from
ArakelovGeometry. The constructions use induced and quotient norms on completed fibers.
The extremal slopes and map heights take values in `EReal`, allowing zero bundles as well.

## References

* [Chen–Moriwaki, Propositions 4.1.19, 4.1.24 and 4.1.32][cm]: adelic constructions.
* [Chen–Moriwaki, Proposition 4.3.31][cm]: slope inequalities for linear maps.
* [Chen–Moriwaki, Propositions 4.3.37, 4.3.38 and 4.3.41][cm]: the HN filtration.
-/

@[expose] public section

noncomputable section

open MeasureTheory Module
open scoped TensorProduct

namespace ArakelovGeometry.AdelicVectorBundle

universe u w

variable {K : Type u} [Field K] [Countable K] {S : AdelicStructure K}
  [S.IsProper] [S.IsArchimedeanNormalized]

omit [S.IsProper] in
/-- This paper, Proposition 2.3: restrictions, quotients, duals, orthogonal tensors and
determinant lines are Hermitian adelic bundles. See [Chen–Moriwaki, Proposition 4.1.32][cm]. -/
theorem isHermitian_standard_constructions (V W : AdelicVectorBundle S)
    [V.IsHermitian] [W.IsHermitian] (U : Submodule K V) :
    (V.restrictOfNormMeasurability U).IsHermitian ∧
      (V.quotientOfNormMeasurability U).IsHermitian ∧
      V.dualOfNormMeasurability.IsHermitian ∧
      (V ⊗ʰ W).IsHermitian ∧ V.determinantOfNormMeasurability.IsHermitian :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    V.determinantOfNormMeasurability_isLine.isHermitian⟩

omit [Countable K] [S.IsProper] [S.IsArchimedeanNormalized] in
/-- This paper, Proposition 2.3: quotient duality is an isometry onto the annihilator.
This is [Chen–Moriwaki, Proposition 1.1.20][cm] on every completed fiber. -/
theorem quotient_dual_norm_eq_annihilator (V : AdelicVectorBundle S)
    (U : Submodule K V) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] Module.Dual K (V ⧸ U)) :
    (V.toNormFamily.quotient U).dual.norm ω z =
      (V.toNormFamily.dual.restrict U.dualAnnihilator).norm ω
        ((U.dualQuotEquivDualAnnihilator.baseChange K (S.ϕ ω).Completion) z) :=
  V.toNormFamily.quotient_dual_annihilator_norm_eq U ω z

omit [Countable K] [S.IsProper] in
/-- This paper, Proposition 2.3: restriction duality is the quotient by the annihilator.
See [Chen–Moriwaki, Section 1.2.3][cm] for the ultrametric duality statement. -/
theorem dual_quotient_norm_eq_restriction (V : AdelicVectorBundle S) [V.IsHermitian]
    (U : Submodule K V) (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] (Module.Dual K V ⧸ U.dualAnnihilator)) :
    (V.toNormFamily.dual.quotient U.dualAnnihilator).norm ω z =
      (V.toNormFamily.restrict U).dual.norm ω
        (((Subspace.quotAnnihilatorEquiv U).baseChange K (S.ϕ ω).Completion) z) :=
  V.toNormFamily.dual_quotient_annihilator_norm_eq U ω z

omit [S.IsProper] in
/-- This paper, Section 2.4, the height used in Proposition 2.4: a nonzero Hermitian map
has integrable local height and its height is the ordinary real integral.
This is [Chen–Moriwaki, Proposition 4.3.16][cm]. -/
theorem integrable_localHeight_and_mapHeight_eq_integral (V W : AdelicVectorBundle S)
    [V.IsHermitian] [W.IsHermitian] (f : V →ₗ[K] W) (hf : f ≠ 0) :
    Integrable (V.toNormFamily.localHeight W.toNormFamily ⟨f, hf⟩) S.v ∧
      V.mapHeight W f =
        ((∫ ω, V.toNormFamily.localHeight W.toNormFamily ⟨f, hf⟩ ω ∂S.v) : ℝ) :=
  ⟨V.integrable_localHeight_of_isStronglyAdelic W ⟨f, hf⟩,
    V.mapHeight_eq_integral_of_isStronglyAdelic W hf⟩

/-- This paper, Proposition 2.4: the nonzero, injective and surjective slope inequalities.
These are the three assertions of [Chen–Moriwaki, Proposition 4.3.31][cm]. -/
theorem slope_bounds_of_nonzero_map (V W : AdelicVectorBundle S)
    (f : V →ₗ[K] W) (hf : f ≠ 0) :
    V.minimalSlope ≤ W.maximalSlope + V.mapHeight W f ∧
      (Function.Injective f → V.maximalSlope ≤ W.maximalSlope + V.mapHeight W f) ∧
      (Function.Surjective f → V.minimalSlope ≤ W.minimalSlope + V.mapHeight W f) :=
  ⟨V.minimalSlope_le_maximalSlope_add_mapHeight_of_ne_zero W f hf,
    V.maximalSlope_le_maximalSlope_add_mapHeight_of_injective W f,
    fun hs => V.minimalSlope_le_minimalSlope_add_mapHeight_of_surjective W f hs hf⟩

/-- This paper, Theorem 2.5: the canonical flag has positive length, semistable grades,
strictly decreasing slopes and additive degree. Its construction is
[Chen–Moriwaki, Section 4.3.10 and Proposition 4.3.37][cm]. -/
theorem hermitianHNFlag_spec (V : AdelicVectorBundle S) [V.IsHermitian]
    (hr : 0 < finrank K V) :
    0 < V.hermitianHNLength ∧
      V.hermitianHNFlag 0 = ⊥ ∧
      V.hermitianHNFlag (Fin.last V.hermitianHNLength) = ⊤ ∧
      StrictMono V.hermitianHNFlag ∧
      (∀ i, (V.hermitianHNFactor i).IsMeanSlopeSemistable) ∧
      StrictAnti (fun i => (V.hermitianHNFactor i).slope) ∧
      (∑ i, (finrank K (V.hermitianHNFactor i) : ℝ) *
        (V.hermitianHNFactor i).slope) = V.degree :=
  ⟨V.hermitianHNLength_pos_of_finrank_pos hr, V.hermitianHNFlag_zero,
    V.hermitianHNFlag_last, V.hermitianHNFlag_strictMono,
    V.isMeanSlopeSemistable_hermitianHNFactor, V.hermitianHNFactor_slope_strictAnti,
    V.sum_hermitianHNFactor_rank_mul_slope_eq_degree⟩

/-- This paper, Theorem 2.5: the first and last HN weights are the extremal slopes.
The last-weight identity is [Chen–Moriwaki, Proposition 4.3.41][cm]. -/
theorem hermitianHNOrderedSlope_extrema (V : AdelicVectorBundle.{max u w} S) [V.IsHermitian]
    (hr : 0 < finrank K V) :
    (V.hermitianHNOrderedSlope ⟨0, hr⟩ : EReal) = V.maximalSlope ∧
      (V.hermitianHNOrderedSlope (⟨0, hr⟩ : Fin (finrank K V)).rev : EReal) =
        V.minimalSlope :=
  ⟨V.hermitianHNOrderedSlope_zero_eq_maximalSlope hr,
    V.hermitianHNOrderedSlope_last_eq_minimalSlope hr⟩

/-- This paper, Theorem 2.5: a filtration with semistable grades of their threshold slopes
is the HN filtration. This is [Chen–Moriwaki, Proposition 4.3.38][cm], expressed as equality
of the associated decreasing real filtrations. -/
theorem eq_hermitianHNFiltration_of_semistable_grades (V : AdelicVectorBundle S)
    [V.IsHermitian] (F : ℝ → Submodule K V) (hF : Antitone F)
    (hbot : ∃ t, F t = ⊥) (htop : ∃ t, F t = ⊤)
    (hleft : ∀ t, ∃ ε : ℝ, 0 < ε ∧ ∀ s, t - ε < s → s ≤ t → F s = F t)
    (hgraded : ∀ t,
      let W := ⨆ s : {s : ℝ // t < s}, F s.val
      let Q := quotientOfNormMeasurability (V.restrictOfNormMeasurability (F t))
        (W.comap (F t).subtype)
      finrank K ((F t) ⧸ W.comap (F t).subtype) = 0 ∨
        Q.IsMeanSlopeSemistable ∧ Q.slope = t) :
    F = V.hermitianHNFiltration :=
  V.hermitianHNFiltration_unique F hF hbot htop hleft hgraded

end ArakelovGeometry.AdelicVectorBundle
