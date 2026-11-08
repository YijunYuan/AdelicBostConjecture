/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Dual.Fiber
public import BostConjecture.Arithmetic.Determinant.Line

/-!
# Scalar extension of canonical exterior duality

The determinant evaluation pairing commutes with extension of scalars.
The proof checks elementary wedges and then uses their spanning property,
so it applies to nonfree finite projective modules.
-/

@[expose] public section

noncomputable section

open Module TensorProduct exteriorPower

namespace BostConjecture.Arithmetic

variable (R S M : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]

/-- Scalar extension preserves exterior evaluation on integral sections. -/
lemma exteriorPairing_baseChange_section (n : ℕ) (f : ⋀[R]^n (Dual R M)) (x : ⋀[R]^n M) :
    pairingDual S (S ⊗[R] M) n
        (map n (dualBaseChangeEquiv R S M).toLinearMap
          (baseChangeEquiv R (Dual R M) S n (1 ⊗ₜ[R] f)))
        (baseChangeEquiv R M S n (1 ⊗ₜ[R] x)) =
      algebraMap R S (pairingDual R M n f x) := by
  have hf : f ∈ Submodule.span R (Set.range (ιMulti R n (M := Dual R M))) := by
    rw [ιMulti_span]
    trivial
  have hx : x ∈ Submodule.span R (Set.range (ιMulti R n (M := M))) := by
    rw [ιMulti_span]
    trivial
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨v, rfl⟩ := hf
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, rfl⟩ := hx
      rw [baseChangeEquiv_apply_tmul, baseChangeEquiv_apply_tmul, map_apply_ιMulti,
        pairingDual_ιMulti_ιMulti, pairingDual_ιMulti_ιMulti]
      simp only [Function.comp_apply, LinearEquiv.coe_coe, TensorProduct.mk_apply,
        dualBaseChangeEquiv_tmul, one_mul]
      exact ((algebraMap R S).map_det (Matrix.of fun (i j : Fin n) => v j (w i))).symm
    | zero => simp only [TensorProduct.tmul_zero, LinearEquiv.map_zero, LinearMap.map_zero,
        map_zero (algebraMap R S)]
    | add x y hx hy ihx ihy => simp [tmul_add, ihx, ihy]
    | smul a x hx ih =>
      have ht : (1 : S) ⊗ₜ[R] (a • x) = (algebraMap R S a) • ((1 : S) ⊗ₜ[R] x) := by
        rw [TensorProduct.tmul_smul, ← IsScalarTower.algebraMap_smul S a]
      rw [ht]
      simp only [map_smul, ih, Algebra.smul_def, map_mul, Algebra.algebraMap_self_apply]
  | zero => simp only [TensorProduct.tmul_zero, LinearEquiv.map_zero, LinearMap.map_zero,
      LinearMap.zero_apply, map_zero (algebraMap R S)]
  | add f g hf hg ihf ihg => simp [tmul_add, ihf, ihg]
  | smul a f hf ih =>
    have ht : (1 : S) ⊗ₜ[R] (a • f) = (algebraMap R S a) • ((1 : S) ⊗ₜ[R] f) := by
      rw [TensorProduct.tmul_smul, ← IsScalarTower.algebraMap_smul S a]
    rw [ht]
    simp only [map_smul, LinearMap.smul_apply, ih, Algebra.smul_def, map_mul,
      Algebra.algebraMap_self_apply]

/-- Scalar extension preserves the canonical pairing on all scalar-extended vectors. -/
lemma exteriorPairing_baseChange (n : ℕ)
    (f : S ⊗[R] (⋀[R]^n (Dual R M))) (x : S ⊗[R] (⋀[R]^n M)) :
    dualBaseChangeEquiv R S (⋀[R]^n M) ((pairingDual R M n).baseChange S f) x =
      pairingDual S (S ⊗[R] M) n
        (map n (dualBaseChangeEquiv R S M).toLinearMap
          (baseChangeEquiv R (Dual R M) S n f)) (baseChangeEquiv R M S n x) := by
  induction f using TensorProduct.inductionOn with
  | tmul a f =>
    induction x using TensorProduct.inductionOn with
    | tmul b x =>
      rw [LinearMap.baseChange_tmul, dualBaseChangeEquiv_tmul]
      have hf : a ⊗ₜ[R] f = a • (1 ⊗ₜ[R] f) := by
        simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      have hx : b ⊗ₜ[R] x = b • (1 ⊗ₜ[R] x) := by
        simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hf, hx]
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul,
        exteriorPairing_baseChange_section]
      ring
    | add x y hx hy => simp only [map_add, hx, hy]
  | add f g hf hg => simp only [map_add, LinearMap.add_apply, hf, hg]

end BostConjecture.Arithmetic
