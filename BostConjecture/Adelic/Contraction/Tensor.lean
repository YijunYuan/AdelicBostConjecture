/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicVectorBundle.Exterior.BaseChange
public import BostConjecture.Geometry.Determinant.BaseChange

/-!
# Exterior scalar-extension compatibility

The existing determinant embedding and AG determinant norms use the same
canonical scalar extension on exterior powers. This equality allows their
completed-fibre formulas to be combined without changing either construction.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Adelic.Contraction

open Module ArakelovGeometry
open scoped TensorProduct

variable (K L V : Type*) [Field K] [Field L] [Algebra K L]
  [AddCommGroup V] [Module K V]

/-- The exterior scalar extension used by the algebraic determinant map
agrees with the canonical scalar extension used by the adelic norm family. -/
theorem exteriorBaseChangeEquiv_eq (n : ℕ) :
    exteriorPower.baseChangeEquiv K V L n = exteriorBaseChangeEquiv K L V n := by
  apply LinearEquiv.toLinearMap_injective
  apply TensorProduct.AlgebraTensorModule.ext
  intro c z
  have h :
      ((exteriorPower.baseChangeEquiv K V L n).toLinearMap.restrictScalars K).comp
        (TensorProduct.mk K L (⋀[K]^n V) c) =
      ((exteriorBaseChangeEquiv K L V n).toLinearMap.restrictScalars K).comp
        (TensorProduct.mk K L (⋀[K]^n V) c) := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro x
    change exteriorPower.baseChangeEquiv K V L n (c ⊗ₜ[K] exteriorPower.ιMulti K n x) =
      exteriorBaseChangeEquiv K L V n (c ⊗ₜ[K] exteriorPower.ιMulti K n x)
    rw [show c ⊗ₜ[K] exteriorPower.ιMulti K n x =
      c • ((1 : L) ⊗ₜ[K] exteriorPower.ιMulti K n x) by
        simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
    simp only [map_smul, exteriorPower.baseChangeEquiv_apply_tmul,
      exteriorBaseChangeEquiv_tmul_ιMulti, one_smul, Function.comp_def,
      TensorProduct.mk_apply]
  exact LinearMap.congr_fun h z

end BostConjecture.Adelic.Contraction
