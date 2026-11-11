/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Adelic.Slope.DeterminantSpecht
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Independent products of the actual determinant–Specht bundles

The auxiliary tensor bundle and its dual in Section 6 are semistable because
each determinant–Specht factor has an absolutely irreducible isometric action.
The groups act independently. No semistability of the original bundles is assumed.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace BostConjecture.Adelic

open ArakelovGeometry ArakelovGeometry.AdelicVectorBundle Specht Module

universe u v w

variable {K : Type u} [Field K] [CharZero K] {S : AdelicStructure.{u, v} K}
  [S.IsProper] {ι : Type w} [Fintype ι]
  {E : ι → Type u} [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]
  [∀ i, FiniteDimensional K (E i)] (V : ∀ i, AdelicVectorBundle S (E i))
  (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
  (hcount : S.HasCommonCountableDenseSubfield)
  (k : ι → ℕ) {n : ι → ℕ}
  (t : ∀ i, OAI.Saxl.Tableau (n i) (rectangle (finrank K (E i)) (k i)))
  (b : ∀ i, Basis (Fin (finrank K (K ⊗[ℤ] orbitLattice (t i)))) ℤ (orbitLattice (t i)))

/-- Independent permutation groups make the actual auxiliary tensor bundle
and its actual dual semistable. The degrees of different factors may differ. -/
theorem determinantSpechtBundle_tensor_isMeanSlopeSemistable_and_dual :
    (orthogonalTensorOfMeasurableBase
      (fun i => determinantSpechtBundle (V i) hN hcount (k i) (t i) (b i))
      (Or.inr hcount) hN
      (fun i => determinantSpechtBundle_isHermitian
        (V i) hN hcount (k i) (t i) (b i))).IsMeanSlopeSemistable (Or.inr hcount) hN ∧
    ((orthogonalTensorOfMeasurableBase
      (fun i => determinantSpechtBundle (V i) hN hcount (k i) (t i) (b i))
      (Or.inr hcount) hN
      (fun i => determinantSpechtBundle_isHermitian
        (V i) hN hcount (k i) (t i) (b i))).dualOfMeasurableBase
          (Or.inr hcount)).IsMeanSlopeSemistable (Or.inr hcount) hN := by
  let ρ (i : ι) :=
    (Representation.trivial K (Equiv.Perm (Fin (n i)))
      (⨂[K] (_ : Fin (k i)), ⋀[K]^(finrank K (E i)) (E i))).tprod
        (Arithmetic.representationBaseChange K (Arithmetic.Specht.integralRepresentation (t i)))
  let : ∀ i, (Arithmetic.representationBaseChange (AlgebraicClosure K) (ρ i)).IsIrreducible :=
    fun i => by
      let := Arithmetic.Specht.integralRepresentation_baseChange_isAbsolutelyIrreducible
        K (AlgebraicClosure K) (t i)
      exact Arithmetic.isIrreducible_baseChange_trivialLineTensor
        (determinantPower_isLine (V i) (Or.inr hcount) hN (k i)) _ (AlgebraicClosure K)
  apply isMeanSlopeSemistable_orthogonalTensor_and_dual_of_isIrreducible_baseChange
    _ (Or.inr hcount) hN _
    (fun i => (determinantSpechtBundle_isMeanSlopeSemistable_and_dual
      (V i) hN hcount (k i) (t i) (b i)).1.1) ρ (AlgebraicClosure K)
  intro i
  exact NormFamily.orthogonalTensorPair_norm_trivialLineTensor
    (determinantPower (V i) (Or.inr hcount) hN (k i)).toNormFamily
    (latticeBundle S (t i) (b i) hN hcount).toNormFamily hN
    (determinantPower_isHermitian (V i) (Or.inr hcount) hN (k i))
    (latticeBundle_isHermitian S (t i) (b i) hN hcount)
    (Arithmetic.representationBaseChange K (Arithmetic.Specht.integralRepresentation (t i)))
    (latticeNormFamily_orbitAction S (t i) (b i))

end BostConjecture.Adelic
