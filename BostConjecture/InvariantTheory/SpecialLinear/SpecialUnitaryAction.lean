/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.InvariantTheory.SpecialLinear.SpecialUnitaryDensity
public import BostConjecture.InvariantTheory.Plucker.Coordinates
public import Mathlib.Topology.Algebra.Star.Unitary
public import Mathlib.Topology.Algebra.Group.Matrix
public import Mathlib.Topology.Algebra.MvPolynomial

/-!
# The compact special-unitary subgroup of the actual Plücker action

The compact special-unitary groups act on the same exterior tensor space
as the special-linear groups. This restriction supplies the compact group
used to average homogeneous polynomials.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.InvariantTheory

open Module exteriorPower
open scoped TensorProduct Matrix.Norms.L2Operator

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

instance specialUnitary_isTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup ι ℂ) where
  continuous_inv := continuous_induced_rng.mpr (by
    change Continuous fun u : Matrix.specialUnitaryGroup ι ℂ => star (u.val)
    exact continuous_subtype_val.star)

/-- The determinant-one unitary matrices form a compact group. -/
instance specialUnitary_compactSpace [Nonempty ι] :
    CompactSpace (Matrix.specialUnitaryGroup ι ℂ) := by
  apply isCompact_iff_compactSpace.mp
  have hc : IsClosed (Matrix.specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) := by
    change IsClosed ((unitary (Matrix ι ι ℂ) : Set (Matrix ι ι ℂ)) ∩
      {M : Matrix ι ι ℂ | M.det = 1})
    exact isClosed_unitary.inter (isClosed_eq continuous_id.matrix_det continuous_const)
  apply (isCompact_closedBall (0 : Matrix ι ι ℂ) 1).of_isClosed_subset hc
  intro M hM
  rw [Metric.mem_closedBall, dist_zero_right, CStarRing.norm_of_mem_unitary hM.1]

/-- Inclusion of the existing special-unitary matrix group in the special-linear group. -/
def specialUnitaryToSpecialLinear :
    Matrix.specialUnitaryGroup ι ℂ →* Matrix.SpecialLinearGroup ι ℂ where
  toFun u := ⟨u.val, u.property.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

variable {U W : Type*} [AddCommGroup U] [Module ℂ U] [AddCommGroup W] [Module ℂ W]

/-- Inclusion transported through the specified bases, with the actual intrinsic target. -/
def specialUnitaryPluckerGroupHom (bU : Basis ι ℂ U) (bW : Basis κ ℂ W) :
    Matrix.specialUnitaryGroup ι ℂ × Matrix.specialUnitaryGroup κ ℂ →*
      SpecialLinearGroup ℂ U × SpecialLinearGroup ℂ W :=
  (((Matrix.SpecialLinearGroup.toLin_equiv bU).toMonoidHom).comp
    specialUnitaryToSpecialLinear).prodMap
    (((Matrix.SpecialLinearGroup.toLin_equiv bW).toMonoidHom).comp
      specialUnitaryToSpecialLinear)

variable [LinearOrder (ι × κ)]

/-- The compact subgroup acts on the same exterior tensor space. -/
def specialUnitaryPluckerRepresentation (bU : Basis ι ℂ U) (bW : Basis κ ℂ W) (s : ℕ) :
    Representation ℂ (Matrix.specialUnitaryGroup ι ℂ × Matrix.specialUnitaryGroup κ ℂ)
      (⋀[ℂ]^s (U ⊗[ℂ] W)) :=
  (pluckerRepresentation ℂ U W s).comp (specialUnitaryPluckerGroupHom bU bW)

omit [LinearOrder (ι × κ)] in
/-- The matrix entries of the transported compact elements are the original entries. -/
theorem matrixPairEntries_specialUnitaryPluckerGroupHom
    (bU : Basis ι ℂ U) (bW : Basis κ ℂ W)
    (g : Matrix.specialUnitaryGroup ι ℂ × Matrix.specialUnitaryGroup κ ℂ) :
    matrixPairEntries bU bW
      ((specialUnitaryPluckerGroupHom bU bW g).1 : U →ₗ[ℂ] U)
      ((specialUnitaryPluckerGroupHom bU bW g).2 : W →ₗ[ℂ] W) =
      Sum.elim (Function.uncurry g.1.val) (Function.uncurry g.2.val) := by
  funext i
  cases i with
  | inl ij =>
    change bU.coord ij.1
      ((Matrix.SpecialLinearGroup.toLin_equiv bU (specialUnitaryToSpecialLinear g.1) :
        U →ₗ[ℂ] U) (bU ij.2)) = _
    rw [Matrix.SpecialLinearGroup.toLin_equiv.toLinearMap_eq]
    rw [Basis.coord_apply, ← LinearMap.toMatrix_apply, LinearMap.toMatrix_toLin]
    rfl
  | inr ij =>
    change bW.coord ij.1
      ((Matrix.SpecialLinearGroup.toLin_equiv bW (specialUnitaryToSpecialLinear g.2) :
        W →ₗ[ℂ] W) (bW ij.2)) = _
    rw [Matrix.SpecialLinearGroup.toLin_equiv.toLinearMap_eq]
    rw [Basis.coord_apply, ← LinearMap.toMatrix_apply, LinearMap.toMatrix_toLin]
    rfl

/-- Every coordinate of the actual compact orbit is continuous. -/
theorem continuous_specialUnitaryPlucker_coord
    (bU : Basis ι ℂ U) (bW : Basis κ ℂ W) (s : ℕ)
    (z : ⋀[ℂ]^s (U ⊗[ℂ] W)) (I : Set.powersetCard (ι × κ) s) :
    Continuous fun g => ((bU.tensorProduct bW).exteriorPower s).coord I
      (specialUnitaryPluckerRepresentation bU bW s g z) := by
  have he (g) := aeval_pluckerOrbitPolynomial_specialLinear bU bW s z
    (specialUnitaryPluckerGroupHom bU bW g) I
  simp only [matrixPairEntries_specialUnitaryPluckerGroupHom] at he
  simp_rw [specialUnitaryPluckerRepresentation, MonoidHom.comp_apply, ← he]
  have hL : Continuous (fun g : Matrix.specialUnitaryGroup ι ℂ ×
      Matrix.specialUnitaryGroup κ ℂ => (g.1.val : Matrix ι ι ℂ)) :=
    continuous_subtype_val.comp continuous_fst
  have hR : Continuous (fun g : Matrix.specialUnitaryGroup ι ℂ ×
      Matrix.specialUnitaryGroup κ ℂ => (g.2.val : Matrix κ κ ℂ)) :=
    continuous_subtype_val.comp continuous_snd
  apply (MvPolynomial.continuous_eval _).comp
  apply continuous_pi
  intro i
  cases i with
  | inl ij =>
    exact (continuous_apply ij.2).comp
      ((continuous_apply ij.1).comp hL)
  | inr ij =>
    exact (continuous_apply ij.2).comp
      ((continuous_apply ij.1).comp hR)

/-- All linear observations of the compact Plücker action are continuous. -/
theorem continuous_specialUnitaryPlucker_dual
    (bU : Basis ι ℂ U) (bW : Basis κ ℂ W) (s : ℕ)
    (z : ⋀[ℂ]^s (U ⊗[ℂ] W)) (ℓ : Dual ℂ (⋀[ℂ]^s (U ⊗[ℂ] W))) :
    Continuous fun g => ℓ (specialUnitaryPluckerRepresentation bU bW s g z) := by
  let b := (bU.tensorProduct bW).exteriorPower s
  have he (g) : ℓ (specialUnitaryPluckerRepresentation bU bW s g z) =
      ∑ i, b.coord i (specialUnitaryPluckerRepresentation bU bW s g z) * ℓ (b i) := by
    conv_lhs => rw [← b.sum_repr (specialUnitaryPluckerRepresentation bU bW s g z)]
    simp only [map_sum, map_smul, smul_eq_mul, Basis.coord_apply]
  simp_rw [he]
  apply continuous_finsetSum
  exact fun i _ => (continuous_specialUnitaryPlucker_coord bU bW s z i).mul_const _

end BostConjecture.InvariantTheory
