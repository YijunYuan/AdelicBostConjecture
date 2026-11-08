/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import BostConjecture.Tensor.Metric.Basic

/-!
# The complex Gram metric on exterior powers

An orthonormal frame gives Euclidean coordinates on the full exterior power.
The cross Gram determinant formula proves that the resulting metric is
independent of that frame. This is the metric on the Plücker representation.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Balanced

open exteriorPower
open scoped ComplexConjugate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- The exterior metric transported from the exterior coordinates of an
orthonormal basis. Its Gram formula makes the choice of basis immaterial. -/
@[instance_reducible]
def exteriorCore (b : OrthonormalBasis ι ℂ E) (s : ℕ) :
    InnerProductSpace.Core ℂ (⋀[ℂ]^s E) := by
  let e := (b.toBasis.exteriorPower s).equivFun ≪≫ₗ
    (WithLp.linearEquiv 2 ℂ (Set.powersetCard ι s → ℂ)).symm
  letI := NormedAddCommGroup.induced _ _ e e.injective
  letI := InnerProductSpace.induced e.toLinearMap
  exact InnerProductSpace.toCore

theorem exteriorCore_inner (b : OrthonormalBasis ι ℂ E) (s : ℕ)
    (x y : ⋀[ℂ]^s E) :
    (exteriorCore b s).inner x y =
      ∑ I, star ((b.toBasis.exteriorPower s).repr x I) *
        (b.toBasis.exteriorPower s).repr y I := by
  change inner ℂ (WithLp.toLp 2 ((b.toBasis.exteriorPower s).equivFun x))
    (WithLp.toLp 2 ((b.toBasis.exteriorPower s).equivFun y)) = _
  simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]

theorem exteriorCore_inner_ιMulti_left (b : OrthonormalBasis ι ℂ E) (s : ℕ)
    (x : Fin s → E) (y : ⋀[ℂ]^s E) :
    (exteriorCore b s).inner (ιMulti ℂ s x) y =
      pairingDual ℂ E s (ιMulti ℂ s (fun i => innerₛₗ ℂ (x i))) y := by
  let : InnerProductSpace.Core ℂ (⋀[ℂ]^s E) := exteriorCore b s
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ⋀[ℂ]^s E)
  let := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (⋀[ℂ]^s E))
  have h : innerₛₗ ℂ (ιMulti ℂ s x) =
      pairingDual ℂ E s (ιMulti ℂ s (fun i => innerₛₗ ℂ (x i))) := by
    apply (b.toBasis.exteriorPower s).ext
    intro I
    change (exteriorCore b s).inner (ιMulti ℂ s x) ((b.toBasis.exteriorPower s) I) = _
    rw [exteriorCore_inner]
    simp only [Module.Basis.repr_self, Finsupp.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [basis_repr_apply, ιMultiDual_apply_ιMulti, basis_apply, ιMulti_family,
      pairingDual_ιMulti_ιMulti]
    rw [← Matrix.det_conjTranspose]
    congr 1
    ext i j
    simp [Module.Basis.coord_apply, b.coe_toBasis_repr_apply, b.repr_apply_apply,
      inner_conj_symm]
  exact DFunLike.congr_fun h y

/-- The complex exterior metric has the cross Gram determinant pairing on wedges. -/
theorem exteriorCore_inner_ιMulti (b : OrthonormalBasis ι ℂ E) (s : ℕ)
    (x y : Fin s → E) :
    (exteriorCore b s).inner (ιMulti ℂ s x) (ιMulti ℂ s y) =
      (Matrix.of fun i j => inner ℂ (x i) (y j)).det := by
  rw [exteriorCore_inner_ιMulti_left, pairingDual_ιMulti_ιMulti]
  exact Matrix.det_transpose _

/-- The Gram formula uniquely determines the Hermitian metric on the full exterior power. -/
theorem exteriorCore_unique (b : OrthonormalBasis ι ℂ E) (s : ℕ)
    (c : InnerProductSpace.Core ℂ (⋀[ℂ]^s E))
    (hc : ∀ x y : Fin s → E, c.inner (ιMulti ℂ s x) (ιMulti ℂ s y) =
      (Matrix.of fun i j => inner ℂ (x i) (y j)).det) : c = exteriorCore b s := by
  have hinner : c.inner = (exteriorCore b s).inner := by
    funext x y
    apply Tensor.inner_ext_of_span (ιMulti ℂ s) (ιMulti_span ℂ s E)
      c (exteriorCore b s) LinearMap.id LinearMap.id _ x y
    exact fun v w => (hc v w).trans (exteriorCore_inner_ιMulti b s v w).symm
  have hinj : Function.Injective
      (fun d : InnerProductSpace.Core ℂ (⋀[ℂ]^s E) => d.inner) := by
    rintro ⟨⟨⟨ci⟩, cs, cp, ca, cm⟩, cd⟩ ⟨⟨⟨di⟩, ds, dp, da, dm⟩, dd⟩ h
    cases h
    rfl
  exact hinj hinner

theorem exteriorCore_eq {κ : Type*} [Fintype κ] [LinearOrder κ]
    (b : OrthonormalBasis ι ℂ E) (c : OrthonormalBasis κ ℂ E) (s : ℕ) :
    exteriorCore b s = exteriorCore c s :=
  exteriorCore_unique c s (exteriorCore b s) (exteriorCore_inner_ιMulti b s)

variable [FiniteDimensional ℂ E] {s : ℕ}

instance complexExteriorCore : InnerProductSpace.Core ℂ (⋀[ℂ]^s E) :=
  exteriorCore (stdOrthonormalBasis ℂ E) s

instance complexExteriorNormedAddCommGroup : NormedAddCommGroup (⋀[ℂ]^s E) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)

instance complexExteriorInnerProductSpace : InnerProductSpace ℂ (⋀[ℂ]^s E) :=
  InnerProductSpace.ofCore _

theorem exterior_inner_ιMulti (x y : Fin s → E) :
    inner ℂ (ιMulti ℂ s x) (ιMulti ℂ s y) =
      (Matrix.of fun i j => inner ℂ (x i) (y j)).det :=
  exteriorCore_inner_ιMulti (stdOrthonormalBasis ℂ E) s x y

theorem exterior_norm_sq_ιMulti (x : Fin s → E) :
    ‖ιMulti ℂ s x‖ ^ 2 = ((Matrix.of fun i j => inner ℂ (x i) (x j)).det).re := by
  rw [← exterior_inner_ιMulti, inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

theorem exterior_inner_eq (b : OrthonormalBasis ι ℂ E) (x y : ⋀[ℂ]^s E) :
    inner ℂ x y = ∑ I, star ((b.toBasis.exteriorPower s).repr x I) *
      (b.toBasis.exteriorPower s).repr y I := by
  change (exteriorCore (stdOrthonormalBasis ℂ E) s).inner x y = _
  rw [exteriorCore_eq (stdOrthonormalBasis ℂ E) b s, exteriorCore_inner]

/-- The increasing exterior wedges of an orthonormal basis are orthonormal. -/
def exteriorOrthonormalBasis (b : OrthonormalBasis ι ℂ E) (s : ℕ) :
    OrthonormalBasis (Set.powersetCard ι s) ℂ (⋀[ℂ]^s E) :=
  (b.toBasis.exteriorPower s).toOrthonormalBasis <| by
    classical
    rw [orthonormal_iff_ite]
    intro I J
    rw [exterior_inner_eq b]
    simp only [Module.Basis.repr_self]
    simp [Finsupp.single_apply, apply_ite, eq_comm]

@[simp]
theorem exteriorOrthonormalBasis_toBasis (b : OrthonormalBasis ι ℂ E) (s : ℕ) :
    (exteriorOrthonormalBasis b s).toBasis = b.toBasis.exteriorPower s :=
  (b.toBasis.exteriorPower s).toBasis_toOrthonormalBasis _

@[simp]
theorem exteriorOrthonormalBasis_apply (b : OrthonormalBasis ι ℂ E) (s : ℕ)
    (I : Set.powersetCard ι s) :
    exteriorOrthonormalBasis b s I = ιMulti_family ℂ s b I := by
  change (exteriorOrthonormalBasis b s).toBasis I = _
  rw [exteriorOrthonormalBasis_toBasis, basis_apply]
  rfl

end BostConjecture.Balanced
