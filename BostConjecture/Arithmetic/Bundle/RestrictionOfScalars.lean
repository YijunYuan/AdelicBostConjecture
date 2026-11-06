/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Submodule.IntegralSubspace
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.Algebra.Module.Rat

/-!
# Restriction of an integral module to the integers

The generic fiber of an integral module is also its localization over `ℤ`.
Consequently restriction to `ℤ` multiplies generic rank by the degree of the
number field. No integral basis of the module over the ring of integers is
chosen or assumed.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace BostConjecture.Arithmetic

variable {K : Type*} [Field K] [NumberField K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]

/-- The usual generic map is localization also at the nonzero integers. -/
instance genericMap_int_isLocalizedModule :
    IsLocalizedModule (nonZeroDivisors ℤ)
      ((TensorProduct.mk (𝓞 K) K M 1).restrictScalars ℤ) :=
  IsLocalizedModule.restrictScalars (nonZeroDivisors ℤ) _

/-- Rational scalar extension of the underlying abelian group is the actual
generic fiber, including for nonfree integral modules. -/
def rationalGenericEquiv : ℚ ⊗[ℤ] M ≃ₗ[ℚ] K ⊗[𝓞 K] M := by
  let e := IsLocalizedModule.linearEquiv (nonZeroDivisors ℤ)
    (TensorProduct.mk ℤ ℚ M 1)
    ((TensorProduct.mk (𝓞 K) K M 1).restrictScalars ℤ)
  exact e.toAddEquiv.toLinearEquiv (fun q x => map_rat_smul e q x)

@[simp]
lemma rationalGenericEquiv_tmul (x : M) :
    rationalGenericEquiv ((1 : ℚ) ⊗ₜ[ℤ] x) = (1 : K) ⊗ₜ[𝓞 K] x :=
  IsLocalizedModule.linearEquiv_apply (nonZeroDivisors ℤ) _ _ x

/-- The integral module is finite after restriction to `ℤ`. -/
lemma finite_int [Module.Finite (𝓞 K) M] : Module.Finite ℤ M :=
  Module.Finite.trans (𝓞 K) M

/-- A finite projective integral module is free over the integers. -/
lemma free_int [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M] :
    Module.Free ℤ M := by
  let := finite_int (K := K) (M := M)
  let : Module.IsTorsionFree ℤ M := Module.IsTorsionFree.trans (𝓞 K)
  infer_instance

/-- Restriction of scalars multiplies generic rank by `[K : ℚ]`. -/
lemma finrank_int :
    Module.finrank ℤ M = Module.finrank ℚ K * Module.finrank K (K ⊗[𝓞 K] M) := by
  rw [← IsLocalizedModule.finrank_eq (nonZeroDivisors ℤ)
    ((TensorProduct.mk (𝓞 K) K M 1).restrictScalars ℤ) le_rfl,
    ← IsFractionRing.finrank_right_eq ℤ ℚ (K ⊗[𝓞 K] M),
    Module.finrank_mul_finrank]

end BostConjecture.Arithmetic
