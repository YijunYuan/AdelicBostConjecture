/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Adelic.Specht.Coordinates
public import ArakelovGeometry.AdelicVectorBundle.Construction.Basis
public import ArakelovGeometry.AdelicVectorBundle.NormFamily.Completion.Density
public import ArakelovGeometry.AdelicVectorBundle.Measurability.Countable
import ArakelovGeometry.AdelicVectorBundle.NormFamily.Domination.Subquotient

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
  simp only [latticeNormFamily, NormFamily.piecewise_norm, if_neg hn,
    NormFamily.ofBasisHermitian_norm_of_finite _ ω hω, NormFamily.ofBasis_norm]

/-- At infinity the norm is the square root of the sum of squared word
coefficients, rather than squared lattice-basis coefficients. -/
theorem latticeNormFamily_norm_infinite (ω : S.Ω) (hω : ω ∈ S.Ωinf)
    (x : (S.ϕ ω).Completion ⊗[K] (K ⊗[ℤ] orbitLattice t)) :
    (latticeNormFamily S t b).norm ω x =
      Real.sqrt (∑ w, ‖fibreWordCoordinates t x w‖ ^ 2) := by
  simp only [latticeNormFamily, NormFamily.piecewise_norm, if_pos hω,
    wordNormFamily, NormFamily.pullback_norm,
    NormFamily.ofBasisHermitian_norm_of_infinite _ ω hω,
    fibreWordCoordinates_eq_basis]

/-- Rational norm evaluations are measurable finite coordinate expressions. -/
theorem latticeNormFamily_isMeasurable : (latticeNormFamily S t b).IsMeasurable := by
  classical
  intro x
  have hword := (NormFamily.ofBasisHermitian_isMeasurable
    (S := S) (Pi.basisFun K (Fin n → Fin (μ.colLen 0)))).pullback
      (wordCoordinates K t) (wordCoordinates_injective K t)
  have hb := NormFamily.ofBasisHermitian_isMeasurable (S := S) (b.baseChange K)
  simpa only [latticeNormFamily, NormFamily.piecewise_norm, ite_apply] using
    Measurable.ite S.measurableSet_Ωinf (hword x) (hb x)

variable (hS : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)

/-- The original completed scalar actions and norms satisfy the Hermitian
condition. No replacement of the Gram matrix is involved. -/
theorem latticeNormFamily_isHermitian : (latticeNormFamily S t b).IsHermitian hS := by
  have hw := (NormFamily.ofBasisHermitian_isHermitian
    (S := S) (Pi.basisFun K (Fin n → Fin (μ.colLen 0))) hS).pullback
      (wordCoordinates K t) (wordCoordinates_injective K t)
  have hb := NormFamily.ofBasisHermitian_isHermitian (S := S) (b.baseChange K) hS
  constructor
  · intro ω hω x y
    have hn : ω ∉ S.Ωinf := fun h => h hω
    simpa only [latticeNormFamily, NormFamily.piecewise_norm, if_neg hn] using hb.1 ω hω x y
  · intro ω hω
    simpa only [latticeNormFamily, NormFamily.piecewise_norm, if_pos hω] using hw.2 ω hω

/-- Strong domination follows from the checked pullback and splicing theorems
for actual norm families. Finiteness of the Archimedean mass is proved by AG. -/
theorem latticeNormFamily_isStronglyDominated :
    (latticeNormFamily S t b).IsStronglyDominated := by
  have hfin := S.v_Ωinf_lt_top_of_isRCLike hS
  have hw := (NormFamily.ofBasisHermitian_isStronglyDominated_of_measure_lt_top
    (S := S) (Pi.basisFun K (Fin n → Fin (μ.colLen 0))) hfin).pullback
      (wordCoordinates K t) (wordCoordinates_injective K t) hS
  exact hw.piecewise
    (NormFamily.ofBasisHermitian_isStronglyDominated_of_measure_lt_top (b.baseChange K) hfin)
    hfin S.Ωinf

/-- Domination of the family and its actual completed dual. -/
theorem latticeNormFamily_isDominated : (latticeNormFamily S t b).IsDominated :=
  (latticeNormFamily_isStronglyDominated S t b hS).isDominated

/-- The constant adelic bundle with its actual word Gram metric. -/
def latticeBundle (hcount : S.HasCommonCountableDenseSubfield) :
    AdelicVectorBundle S (K ⊗[ℤ] orbitLattice t) where
  toNormFamily := latticeNormFamily S t b
  isMeasurable := latticeNormFamily_isMeasurable S t b
  dual_isMeasurable := (latticeNormFamily_isMeasurable S t b).dual_of_common_countable_dense_subfield
    hcount
  isDominated := latticeNormFamily_isDominated S t b hS

@[simp]
theorem latticeBundle_toNormFamily (hcount : S.HasCommonCountableDenseSubfield) :
    (latticeBundle S t b hS hcount).toNormFamily = latticeNormFamily S t b := rfl

/-- The constructed adelic bundle is Hermitian. -/
theorem latticeBundle_isHermitian (hcount : S.HasCommonCountableDenseSubfield) :
    (latticeBundle S t b hS hcount).IsHermitian hS :=
  latticeNormFamily_isHermitian S t b hS

end BostConjecture.Specht
