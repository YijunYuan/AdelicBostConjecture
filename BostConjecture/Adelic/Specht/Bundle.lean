/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Adelic.Specht.Coordinates
public import ArakelovGeometry.AdelicVectorBundle.Basic
public import ArakelovGeometry.AdelicVectorBundle.NormFamily.Hermitian.Basis
public import ArakelovGeometry.AdelicVectorBundle.NormFamily.Completion.Density
public import ArakelovGeometry.AdelicVectorBundle.Measurability.Countable
public import ArakelovGeometry.AdelicVectorBundle.Tensor.Hermitian.InnerProduct
import ArakelovGeometry.AdelicVectorBundle.NormFamily.Domination.Subquotient
import ArakelovGeometry.AdelicCurve.Basic

/-!
# The constant adelic Specht bundle

The module is `K ⊗[ℤ] orbitLattice t`. At infinite places the norm is the
restriction of the Euclidean **word** norm. At finite places it is the maximum
of the coefficients in an integral lattice basis. In particular, the lattice
basis is not made orthonormal at infinity.

This constructs the bundle in this paper, Lemma 6.1 (page 25). The countable
common dense subfield is used only for measurability of the actual dual norm.
The degree calculation and representation-theoretic semistability are separate.
-/

@[expose] public section
noncomputable section

namespace BostConjecture.Specht

open Module ArakelovGeometry MeasureTheory
open scoped TensorProduct

variable {K : Type*} [Field K] [CharZero K] (S : AdelicStructure K)
  {n : ℕ} {μ : YoungDiagram} (t : OAI.Saxl.Tableau n μ)

/-- The restriction of the ambient word-basis Hermitian family. Its infinite
fibres give the Specht Gram metric; its finite fibres are not used below. -/
def wordNormFamily : NormFamily S (K ⊗[ℤ] orbitLattice t) :=
  (NormFamily.ofBasisHermitian S _ (Pi.basisFun K (Fin n → Fin (μ.colLen 0)))).pullback
    (wordCoordinates K t) (wordCoordinates_injective K t)

variable {ι : Type*} [Fintype ι] (b : Basis ι ℤ (orbitLattice t))

/-- The actual constant Specht norms: word Gram at infinity and lattice max
at finite places. The basis is an integral basis of the full orbit lattice. -/
def latticeNormFamily : NormFamily S (K ⊗[ℤ] orbitLattice t) :=
  (wordNormFamily S t).piecewise
    (NormFamily.ofBasisHermitian S _ (b.baseChange K)) S.Ωinf

/-- The finite-place norm is exactly the completed integral-basis maximum. -/
theorem latticeNormFamily_norm_finite (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (x : (S.ϕ ω).Completion ⊗[K] (K ⊗[ℤ] orbitLattice t)) :
    (latticeNormFamily S t b).norm ω x =
      ‖((b.baseChange K).baseChange (S.ϕ ω).Completion).equivFun x‖ := by
  have hn : ω ∉ S.Ωinf := fun h => h hω
  simp only [latticeNormFamily, NormFamily.piecewise_norm, ite_eq_right hn,
    NormFamily.ofBasisHermitian_norm_of_finite _ ω hω, NormFamily.ofBasis_norm]

/-- At infinity the norm is the square root of the sum of squared word
coefficients, rather than squared lattice-basis coefficients. -/
theorem latticeNormFamily_norm_infinite (ω : S.Ω) (hω : ω ∈ S.Ωinf)
    (x : (S.ϕ ω).Completion ⊗[K] (K ⊗[ℤ] orbitLattice t)) :
    (latticeNormFamily S t b).norm ω x =
      Real.sqrt (∑ w, ‖fibreWordCoordinates t x w‖ ^ 2) := by
  simp only [latticeNormFamily, NormFamily.piecewise_norm, ite_eq_left hω,
    wordNormFamily, NormFamily.pullback_norm,
    NormFamily.ofBasisHermitian_norm_of_infinite _ ω hω,
    fibreWordCoordinates_eq_basis]

/-- Rational norm evaluations are measurable finite coordinate expressions. -/
instance latticeNormFamily_isMeasurable : (latticeNormFamily S t b).IsMeasurable := by
  classical
  constructor
  intro x
  have hword := (NormFamily.ofBasisHermitian_isMeasurable
    (S := S) (Pi.basisFun K (Fin n → Fin (μ.colLen 0)))).pullback
      (wordCoordinates K t) (wordCoordinates_injective K t)
  have hb := NormFamily.ofBasisHermitian_isMeasurable (S := S) (b.baseChange K)
  have hm : Measurable (fun ω => if ω ∈ S.Ωinf then
      (wordNormFamily S t).norm ω ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] x) else
      (NormFamily.ofBasisHermitian S _ (b.baseChange K)).norm ω
        ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] x)) :=
    Measurable.ite (p := fun ω => ω ∈ S.Ωinf) S.measurableSet_Ωinf (hword x) (hb x)
  convert hm using 1
  ext ω
  by_cases hω : ω ∈ S.Ωinf <;>
    simp [latticeNormFamily, NormFamily.piecewise_norm, hω, wordNormFamily]

variable [hS : S.IsArchimedeanNormalized]

/-- The original completed scalar actions and norms satisfy the Hermitian
condition. No replacement of the Gram matrix is involved. -/
instance latticeNormFamily_isHermitian : (latticeNormFamily S t b).IsHermitian := by
  have hw := (NormFamily.ofBasisHermitian_isHermitian
    (S := S) (Pi.basisFun K (Fin n → Fin (μ.colLen 0)))).pullback
      (wordCoordinates K t) (wordCoordinates_injective K t)
  have hb := NormFamily.ofBasisHermitian_isHermitian (S := S) (b.baseChange K)
  constructor
  · constructor
    intro ω hω x y
    have hn : ω ∉ S.Ωinf := fun h => h hω
    simpa only [latticeNormFamily, NormFamily.piecewise_norm, ite_eq_right hn] using hb.1 ω hω x y
  · intro ω hω
    simpa only [latticeNormFamily, NormFamily.piecewise_norm, ite_eq_left hω, wordNormFamily]
      using hw.2 ω hω

include hS
/-- Strong domination follows from the checked pullback and splicing theorems
for actual norm families. Finiteness of the Archimedean mass is proved by AG. -/
instance latticeNormFamily_isStronglyDominated :
    (latticeNormFamily S t b).IsStronglyDominated := by
  have hfin := S.v_Ωinf_lt_top_of_isRCLike
  have hw := (NormFamily.ofBasisHermitian_isStronglyDominated_of_measure_lt_top
    (S := S) (Pi.basisFun K (Fin n → Fin (μ.colLen 0))) hfin).pullback
      (wordCoordinates K t) (wordCoordinates_injective K t)
  exact hw.piecewise
    (NormFamily.ofBasisHermitian_isStronglyDominated_of_measure_lt_top (b.baseChange K) hfin)
    hfin S.Ωinf

/-- Domination of the family and its actual completed dual. -/
instance latticeNormFamily_isDominated : (latticeNormFamily S t b).IsDominated :=
  (latticeNormFamily_isStronglyDominated S t b).isDominated

/-- The constant adelic bundle with its actual word Gram metric. -/
abbrev latticeBundle [hcount : S.HasCommonCountableDenseSubfield] :
    AdelicVectorBundle S where
  carrier := K ⊗[ℤ] orbitLattice t
  toNormFamily := latticeNormFamily S t b
  toIsAdelic := {
    isMeasurable := latticeNormFamily_isMeasurable S t b
    dual_isMeasurable :=
      (latticeNormFamily_isMeasurable S t b).dual_of_common_countable_dense_subfield hcount
    isDominated := latticeNormFamily_isDominated S t b }

@[simp]
theorem latticeBundle_toNormFamily [hcount : S.HasCommonCountableDenseSubfield] :
    (latticeBundle S t b).toNormFamily = latticeNormFamily S t b := rfl

/-- The constructed adelic bundle is Hermitian. -/
instance latticeBundle_isHermitian [S.HasCommonCountableDenseSubfield] :
    (latticeBundle S t b).IsHermitian :=
  latticeNormFamily_isHermitian S t b

/-- The inner product selected from the Hermitian norm is the actual word
Gram inner product. This fixes the metric used by determinant constructions. -/
theorem latticeNormFamily_inner (ω : S.Ω) (hω : ω ∈ S.Ωinf) :
    letI := hS ω hω
    letI := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
    letI := (latticeNormFamily S t b).fibreNormedAddCommGroup ω
    letI := (latticeNormFamily S t b).fibreNormedSpace ω
    letI := (latticeNormFamily S t b).fiberInnerProductSpace ω hω
    ∀ x y : (S.ϕ ω).Completion ⊗[K] (K ⊗[ℤ] orbitLattice t),
      inner (S.ϕ ω).Completion x y =
        ∑ w, star (fibreWordCoordinates t x w) * fibreWordCoordinates t y w := by
  let := hS ω hω
  let := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
  let := (latticeNormFamily S t b).fibreNormedAddCommGroup ω
  let := (latticeNormFamily S t b).fibreNormedSpace ω
  let := (latticeNormFamily S t b).fiberInnerProductSpace ω hω
  let f : ((S.ϕ ω).Completion ⊗[K] (K ⊗[ℤ] orbitLattice t)) →ₗᵢ[(S.ϕ ω).Completion]
      EuclideanSpace (S.ϕ ω).Completion (Fin n → Fin (μ.colLen 0)) :=
    { toLinearMap := (WithLp.linearEquiv 2 (S.ϕ ω).Completion _).symm.toLinearMap.comp
        (fibreWordCoordinates t)
      norm_map' := fun x => by
        change ‖(WithLp.linearEquiv 2 (S.ϕ ω).Completion _).symm
          (fibreWordCoordinates t x)‖ = (latticeNormFamily S t b).norm ω x
        rw [latticeNormFamily_norm_infinite S t b ω hω]
        exact PiLp.norm_eq_of_L2 _ }
  intro x y
  rw [← f.inner_map_map]
  change inner (S.ϕ ω).Completion
    ((WithLp.linearEquiv 2 (S.ϕ ω).Completion _).symm (fibreWordCoordinates t x))
    ((WithLp.linearEquiv 2 (S.ϕ ω).Completion _).symm (fibreWordCoordinates t y)) = _
  simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]

/-- Integral vectors have exactly their integer word Gram pairing at every
Archimedean completion, with no normalization factor. -/
theorem latticeNormFamily_inner_integral (ω : S.Ω) (hω : ω ∈ S.Ωinf) :
    letI := hS ω hω
    letI := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
    letI := (latticeNormFamily S t b).fibreNormedAddCommGroup ω
    letI := (latticeNormFamily S t b).fibreNormedSpace ω
    letI := (latticeNormFamily S t b).fiberInnerProductSpace ω hω
    ∀ x y : orbitLattice t,
      inner (S.ϕ ω).Completion
        ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] ((1 : K) ⊗ₜ[ℤ] x))
        ((1 : (S.ϕ ω).Completion) ⊗ₜ[K] ((1 : K) ⊗ₜ[ℤ] y)) =
        (∑ w, x.val w * y.val w : ℤ) := by
  let := hS ω hω
  let := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
  let := (latticeNormFamily S t b).fibreNormedAddCommGroup ω
  let := (latticeNormFamily S t b).fibreNormedSpace ω
  let := (latticeNormFamily S t b).fiberInnerProductSpace ω hω
  intro x y
  simp [latticeNormFamily_inner S t b ω hω]

end BostConjecture.Specht
