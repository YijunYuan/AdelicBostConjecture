/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Line.Coordinates
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Inverse coefficient ideals of integral dual lines

An injective coordinate identifies the integral dual with the inverse
fractional ideal. Evaluation constructs the map; the inverse-ideal
membership condition constructs its preimages. No ideal is assumed principal.
-/

@[expose] public section

noncomputable section

open NumberField Module
open scoped nonZeroDivisors

namespace BostConjecture.Arithmetic

variable {K : Type*} [Field K] [NumberField K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]

/-- The generic coordinate on the dual line, recovered by evaluation at a section. -/
def dualCoordinate (q : M →ₗ[𝓞 K] K) (x : M) : Dual (𝓞 K) M →ₗ[𝓞 K] K :=
  (q x)⁻¹ • ((Algebra.linearMap (𝓞 K) K).comp (LinearMap.applyₗ x))

omit [NumberField K] in
@[simp]
lemma dualCoordinate_apply (q : M →ₗ[𝓞 K] K) (x : M) (f : Dual (𝓞 K) M) :
    dualCoordinate q x f = (f x : K) / q x := by
  simp [dualCoordinate, div_eq_mul_inv, mul_comm]

/-- Dual and original coordinates multiply to the actual integral evaluation. -/
lemma dualCoordinate_mul (q : M →ₗ[𝓞 K] K) (hq : Function.Injective q)
    {x : M} (hx : x ≠ 0) (f : Dual (𝓞 K) M) (y : M) :
    dualCoordinate q x f * q y = (f y : K) := by
  have he := linearMap_eq_smul_of_injective q ((Algebra.linearMap (𝓞 K) K).comp f) hq hx
  simpa only [dualCoordinate_apply, LinearMap.comp_apply, Algebra.linearMap_apply,
    LinearMap.smul_apply, smul_eq_mul] using (LinearMap.congr_fun he y).symm

lemma dualCoordinate_injective (q : M →ₗ[𝓞 K] K) (hq : Function.Injective q)
    {x : M} (hx : x ≠ 0) : Function.Injective (dualCoordinate q x) := by
  intro f g he
  apply LinearMap.ext
  intro y
  apply RingOfIntegers.coe_injective
  change (f y : K) = (g y : K)
  rw [← dualCoordinate_mul q hq hx f y, ← dualCoordinate_mul q hq hx g y, he]

variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M] [Nontrivial M]

/-- The coefficient ideal of the actual integral dual is the inverse coefficient ideal. -/
theorem coordinateIdeal_dualCoordinate (q : M →ₗ[𝓞 K] K) (hq : Function.Injective q)
    {x : M} (hx : x ≠ 0) :
    coordinateIdeal (dualCoordinate q x) = (coordinateIdeal q)⁻¹ := by
  have hq0 := coordinateIdeal_ne_zero q hq
  ext a
  rw [mem_coordinateIdeal, FractionalIdeal.mem_inv_iff hq0]
  constructor
  · rintro ⟨f, rfl⟩ _ ⟨y, rfl⟩
    rw [dualCoordinate_mul q hq hx]
    exact (FractionalIdeal.mem_one_iff (𝓞 K)⁰).mpr ⟨f y, rfl⟩
  · intro ha
    have hpre (y : M) : ∃ b : 𝓞 K, (b : K) = a * q y :=
      (FractionalIdeal.mem_one_iff (𝓞 K)⁰).mp (ha (q y) ⟨y, rfl⟩)
    choose v hv using hpre
    let f : Dual (𝓞 K) M :=
      { toFun := v
        map_add' := by
          intro y z
          apply RingOfIntegers.coe_injective
          change (v (y + z) : K) = (v y : K) + (v z : K)
          simp only [hv, map_add, mul_add]
        map_smul' := by
          intro b y
          apply RingOfIntegers.coe_injective
          change (v (b • y) : K) = (b : K) * (v y : K)
          simp only [hv, map_smul, Algebra.smul_def]
          ring }
    refine ⟨f, ?_⟩
    rw [dualCoordinate_apply]
    change (v x : K) / q x = a
    rw [hv, mul_div_cancel_right₀]
    exact fun he => hx (hq (by simpa using he))

/-- The finite logarithmic contribution changes sign under integral line duality. -/
theorem logIdealNorm_dualCoordinate (q : M →ₗ[𝓞 K] K) (hq : Function.Injective q)
    {x : M} (hx : x ≠ 0) :
    logIdealNorm (coordinateIdeal (dualCoordinate q x)) = -logIdealNorm (coordinateIdeal q) := by
  rw [coordinateIdeal_dualCoordinate q hq hx]
  simp [logIdealNorm, map_inv₀, Real.log_inv]

end BostConjecture.Arithmetic
