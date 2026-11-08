/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.WedgePairing
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import BostConjecture.ExternalCode.MathlibPRs.PR40948.LinearAlgebra.ExteriorPower.BaseChange

/-!
# Exterior products of two summands

The canonical map from two exterior powers to the exterior power of a
product module is constructed from Mathlib's graded wedge multiplication.
This is the integral map used by exact-sequence determinants.
-/

@[expose] public section

noncomputable section

open TensorProduct

namespace exteriorPower

variable (R M N : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]

/-- Wedge the two inclusions into a product module. -/
def prodMap (a b : ℕ) :
    (⋀[R]^a M) ⊗[R] (⋀[R]^b N) →ₗ[R] ⋀[R]^(a + b) (M × N) :=
  TensorProduct.lift ((wedge R (M × N) a b).compl₁₂
    (map a (LinearMap.inl R M N)) (map b (LinearMap.inr R M N)))

@[simp]
lemma prodMap_tmul (a b : ℕ) (x : ⋀[R]^a M) (y : ⋀[R]^b N) :
    prodMap R M N a b (x ⊗ₜ[R] y) =
      wedge R (M × N) a b (map a (LinearMap.inl R M N) x)
        (map b (LinearMap.inr R M N) y) := rfl

/-- On elementary wedges the product is concatenation in the prescribed order. -/
lemma prodMap_ιMulti (a b : ℕ) (x : Fin a → M) (y : Fin b → N) :
    prodMap R M N a b (ιMulti R a x ⊗ₜ[R] ιMulti R b y) =
      ιMulti R (a + b) (Fin.append (fun i => (x i, 0)) (fun j => (0, y j))) := by
  apply Subtype.ext
  simp only [prodMap_tmul, map_apply_ιMulti, wedge, DirectSum.gMulLHom_apply_apply,
    SetLike.coe_gMul]
  exact ExteriorAlgebra.ιMulti_mul_ιMulti (R := R) _ _

variable {M N}
variable {P Q : Type*} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]

variable (M N) (S : Type*) [CommRing S] [Algebra R S]

/-- Exterior product commutes with scalar extension on arbitrary integral wedges. -/
lemma prodMap_baseChange_section (a b : ℕ) (x : ⋀[R]^a M) (y : ⋀[R]^b N) :
    map (a + b) (TensorProduct.prodRight R S S M N).toLinearMap
      (baseChangeEquiv R (M × N) S (a + b) (1 ⊗ₜ[R] prodMap R M N a b (x ⊗ₜ[R] y))) =
    prodMap S (S ⊗[R] M) (S ⊗[R] N) a b
      (baseChangeEquiv R M S a (1 ⊗ₜ[R] x) ⊗ₜ[S]
        baseChangeEquiv R N S b (1 ⊗ₜ[R] y)) := by
  have hx : x ∈ Submodule.span R (Set.range (ιMulti R a (M := M))) := by
    rw [ιMulti_span]; trivial
  have hy : y ∈ Submodule.span R (Set.range (ιMulti R b (M := N))) := by
    rw [ιMulti_span]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, rfl⟩ := hy
      rw [prodMap_ιMulti, baseChangeEquiv_apply_tmul, baseChangeEquiv_apply_tmul,
        baseChangeEquiv_apply_tmul, map_apply_ιMulti, prodMap_ιMulti]
      congr 1
      funext i
      refine Fin.addCases ?_ ?_ i <;> intro j <;> simp
    | zero => simp
    | add x y hx hy ihx ihy => simp only [tmul_add, map_add, ihx, ihy]
    | smul c x hx ih =>
      simp only [tmul_smul, map_smul, ← IsScalarTower.algebraMap_smul S c, ih]
  | zero => simp
  | add x y hx hy ihx ihy => simp only [add_tmul, tmul_add, map_add, ihx, ihy]
  | smul c x hx ih =>
    simp only [smul_tmul, tmul_smul, map_smul, ← IsScalarTower.algebraMap_smul S c, ih]

end exteriorPower
