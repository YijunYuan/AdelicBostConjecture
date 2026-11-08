/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.ExternalCode.MathlibPRs.PR44845.LinearAlgebra.PiTensorProduct.Projective
public import BostConjecture.InvariantTheory.Polynomial.Basic
public import Mathlib.Algebra.Algebra.IsSimpleRing
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

/-!
# The tensor quotient onto intrinsic homogeneous polynomials

Multiplication of linear forms supplies the actual quotient map. It commutes
with linear pullback and with the canonical finite-projective tensor evaluation.
Invariant lifting through this quotient requires a further symmetrization proof.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Geometry

open Module PiTensorProduct InvariantTheory
open scoped TensorProduct

variable {F X Y : Type*} [Field F] [AddCommGroup X] [Module F X]
  [AddCommGroup Y] [Module F Y]

/-- Multiplication of the linear forms in an actual tensor power. -/
def polynomialTensorMap (F X : Type*) [Field F] [AddCommGroup X] [Module F X] (d : ℕ) :
    (⨂[F] (_ : Fin d), Dual F X) →ₗ[F] SymmetricAlgebra F (Dual F X) :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra F (Fin d)
    (SymmetricAlgebra F (Dual F X))).compLinearMap fun _ => SymmetricAlgebra.ι F _)

@[simp]
theorem polynomialTensorMap_tprod {d : ℕ} (ℓ : Fin d → Dual F X) :
    polynomialTensorMap F X d (tprod F ℓ) = ∏ i, SymmetricAlgebra.ι F _ (ℓ i) := by
  simp [polynomialTensorMap]

private theorem polynomialTensorMap_cons {d : ℕ} (ℓ : Dual F X)
    (u : ⨂[F] (_ : Fin d), Dual F X) :
    polynomialTensorMap F X (d + 1)
      (PiTensorProduct.lift ((tprod F (s := fun _ : Fin (d + 1) => Dual F X)).curryLeft ℓ) u) =
      SymmetricAlgebra.ι F _ ℓ * polynomialTensorMap F X d u := by
  induction u using PiTensorProduct.induction_on with
  | smul_tprod r x => simp [Fin.prod_univ_succ]
  | add u v hu hv => simp only [map_add, hu, hv, mul_add]

/-- The actual image is exactly the canonical degree subspace. -/
theorem range_polynomialTensorMap (d : ℕ) :
    LinearMap.range (polynomialTensorMap F X d) = homogeneousPolynomials F X d := by
  classical
  apply le_antisymm
  · rintro _ ⟨u, rfl⟩
    have hprod {n : ℕ} (ℓ : Fin n → Dual F X) :
        (∏ i, SymmetricAlgebra.ι F _ (ℓ i)) ∈ homogeneousPolynomials F X n := by
      induction n with
      | zero =>
        simp [homogeneousPolynomials]
      | succ n hn =>
        rw [Fin.prod_univ_succ]
        change _ ∈ (LinearMap.range (SymmetricAlgebra.ι F (Dual F X))) ^ (n + 1)
        rw [pow_succ']
        exact Submodule.mul_mem_mul ⟨ℓ 0, rfl⟩ (hn (fun i => ℓ i.succ))
    induction u using PiTensorProduct.induction_on with
    | smul_tprod r ℓ =>
      rw [map_smul, polynomialTensorMap_tprod]
      exact (homogeneousPolynomials F X d).smul_mem r (hprod ℓ)
    | add u v hu hv =>
      simpa only [map_add] using (homogeneousPolynomials F X d).add_mem hu hv
  · intro p hp
    induction hp using Submodule.pow_induction_on_left' with
    | algebraMap r =>
      refine ⟨r • tprod F (fun i : Fin 0 => Fin.elim0 i), ?_⟩
      simp [Algebra.algebraMap_eq_smul_one]
    | add p q d hp hq ihp ihq =>
      exact (LinearMap.range (polynomialTensorMap F X d)).add_mem ihp ihq
    | mem_mul m hm d p hp ih =>
      obtain ⟨ℓ, rfl⟩ := hm
      obtain ⟨u, rfl⟩ := ih
      exact ⟨_, polynomialTensorMap_cons ℓ u⟩

/-- Polynomial evaluation is the existing finite-projective tensor evaluation. -/
theorem polynomialEval_tensorMap [FiniteDimensional F X] {d : ℕ}
    (x : X) (u : ⨂[F] (_ : Fin d), Dual F X) :
    polynomialEval x (polynomialTensorMap F X d u) =
      dualDistribEquivOfProjective F (fun _ : Fin d => X) u
        (tprod F fun _ : Fin d => x) := by
  induction u using PiTensorProduct.induction_on with
  | smul_tprod r ℓ => simp [finprod_eq_prod_of_fintype]
  | add u v hu hv => simp only [map_add, LinearMap.add_apply, hu, hv]

end BostConjecture.Geometry
