/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Geometry.Tensor.Permutation
public import BostConjecture.Geometry.Descent.Embedding
public import BostConjecture.Tensor.Algebra.ReindexBaseChange

/-!
# Position equivariance of the global finite-projective determinant map

The determinant-twisted embedding for finite projective modules commutes
with permutations of tensor positions. The local free-module identities
descend through the principal cover.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Geometry

open Module PiTensorProduct
open scoped TensorProduct

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [Module.Finite R M] [Module.Projective R M] {n a k : ℕ}

/-- The global map on determinant-lattice generators after a free scalar extension. -/
theorem projectiveDeterminantMap_scalarExtension_tmul
    {S : Type*} [CommRing S] [Algebra R S] (hk : 0 < k)
    (t : OAI.Saxl.Tableau n (Specht.rectangle a k))
    (ha : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = a)
    (b : Basis (Fin a) S (S ⊗[R] M))
    (η : ⨂[R] (_ : Fin k), ⋀[R]^a M) (x : Specht.orbitLattice t) :
    Tensor.scalarExtension R S (fun _ : Fin n => M)
      (projectiveDeterminantMap hk t ha (η ⊗ₜ[R] (1 ⊗ₜ[ℤ] x))) =
    freeDeterminantMap hk t b
      (determinantPowerScalarExtension k a η ⊗ₜ[S] (1 ⊗ₜ[ℤ] x)) := by
  have h := LinearMap.congr_fun
    (projectiveDeterminantMap_baseChange_of_basis hk t ha b)
    (1 ⊗ₜ[R] (η ⊗ₜ[R] (1 ⊗ₜ[ℤ] x)))
  have h' := congrArg (Tensor.baseChangeEquiv R S (fun _ : Fin n => M)) h
  simpa only [LinearMap.baseChange_tmul, determinantChart_tmul, one_smul,
    LinearEquiv.apply_symm_apply, Tensor.baseChangeEquiv_tmul_eq_scalarExtension] using h'

/-- Global equivariance is detected on the actual finite principal frame cover. -/
theorem projectiveDeterminantMap_reindex (hk : 0 < k)
    (t : OAI.Saxl.Tableau n (Specht.rectangle a k))
    (ha : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = a)
    (σ : Equiv.Perm (Fin n))
    (z : (⨂[R] (_ : Fin k), ⋀[R]^a M) ⊗[R] (R ⊗[ℤ] Specht.orbitLattice t)) :
    projectiveDeterminantMap hk t ha
      (TensorProduct.map LinearMap.id ((Specht.orbitAction t σ).baseChange R) z) =
    reindex R (fun _ : Fin n => M) σ (projectiveDeterminantMap hk t ha z) := by
  induction z using TensorProduct.inductionOn with
  | tmul η z =>
    induction z using TensorProduct.inductionOn with
    | tmul r x =>
      rw [TensorProduct.tmul_eq_smul_one_tmul r x, TensorProduct.tmul_smul]
      simp only [map_smul]
      congr 1
      obtain ⟨s, hs, hb⟩ := exists_finite_principal_frames ha
      apply Module.eq_of_isLocalized_span (s : Set R) hs _
        (fun i => TensorProduct.mk R (Localization.Away (i : R)) _ 1)
      intro i
      let b := (hb i i.property).some
      apply (Tensor.baseChangeEquiv R (Localization.Away (i : R))
        (fun _ : Fin n => M)).injective
      simp only [TensorProduct.mk_apply, Tensor.baseChangeEquiv_tmul_eq_scalarExtension,
        one_smul, TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.baseChange_tmul]
      rw [projectiveDeterminantMap_scalarExtension_tmul hk t ha b,
        Tensor.scalarExtension_reindex,
        projectiveDeterminantMap_scalarExtension_tmul hk t ha b]
      simpa only [TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.baseChange_tmul] using
        freeDeterminantMap_reindex hk t b σ
          (determinantPowerScalarExtension k a η ⊗ₜ[Localization.Away (i : R)]
            (1 ⊗ₜ[ℤ] x))
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

end BostConjecture.Geometry
