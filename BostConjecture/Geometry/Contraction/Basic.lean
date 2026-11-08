/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Geometry.Descent.Permutation
public import BostConjecture.Tensor.Dual.Regroup

/-!
# The canonical integral restricted tensor pairing

The actual projective determinant maps, canonical dual regrouping, and
finite-projective evaluation define the pairing over the base ring. Position
equivariance is proved for this composite. Metric contraction and nonvanishing
are separate subsequent theorems.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Geometry

open Module PiTensorProduct
open scoped TensorProduct

variable {R ι : Type*} [CommRing R] [Fintype ι]
  (E : ι → Type*) [∀ i, AddCommGroup (E i)] [∀ i, Module R (E i)]
  [∀ i, Module.Finite R (E i)] [∀ i, Module.Projective R (E i)]
  {n : ℕ} {a k : ι → ℕ}
  (hk : ∀ i, 0 < k i)
  (t : ∀ i, OAI.Saxl.Tableau n (Specht.rectangle (a i) (k i)))
  (ha : ∀ i (p : PrimeSpectrum R), Module.rankAtStalk (Dual R (E i)) p = a i)

/-- The dual determinant factors in the actual tensor power of the ambient dual. -/
def dualDeterminantMap :
    (⨂[R] i, (⨂[R] (_ : Fin (k i)), ⋀[R]^(a i) (Dual R (E i))) ⊗[R]
      (R ⊗[ℤ] Specht.orbitLattice (t i))) →ₗ[R]
      (⨂[R] (_ : Fin n), Dual R (⨂[R] i, E i)) :=
  (Tensor.dualRegroupEquiv R E).toLinearMap ∘ₗ
    PiTensorProduct.map (fun i => projectiveDeterminantMap (hk i) (t i) (ha i))

/-- Simultaneous orbit actions on all determinant factors become the ambient
position permutation after the actual dual regrouping. -/
theorem dualDeterminantMap_reindex (σ : Equiv.Perm (Fin n))
    (u : ⨂[R] i, (⨂[R] (_ : Fin (k i)), ⋀[R]^(a i) (Dual R (E i))) ⊗[R]
      (R ⊗[ℤ] Specht.orbitLattice (t i))) :
    dualDeterminantMap E hk t ha
      (PiTensorProduct.map (fun i => TensorProduct.map LinearMap.id
        ((Specht.orbitAction (t i) σ).baseChange R)) u) =
    reindex R (fun _ : Fin n => Dual R (⨂[R] i, E i)) σ
      (dualDeterminantMap E hk t ha u) := by
  simp only [dualDeterminantMap, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [← Tensor.dualRegroupEquiv_reindex]
  congr 1
  simp only [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
  congr 2
  funext i
  apply LinearMap.ext
  exact fun x => projectiveDeterminantMap_reindex (hk i) (t i) (ha i) σ x

variable {V : Type*} [AddCommGroup V] [Module R V]
  [Module.Finite R V] [Module.Projective R V] {s l : ℕ}
  (hl : 0 < l) (v : OAI.Saxl.Tableau n (Specht.rectangle s l))
  (hs : ∀ p : PrimeSpectrum R, Module.rankAtStalk V p = s)

/-- The canonical pairing is defined over the original ring using only the
constructed determinant maps, dual regrouping and projective evaluation. -/
def canonicalPairing (i : V →ₗ[R] (⨂[R] j, E j)) :
    (⨂[R] (_ : Fin l), ⋀[R]^s V) ⊗[R] (R ⊗[ℤ] Specht.orbitLattice v) →ₗ[R]
    Dual R (⨂[R] j, (⨂[R] (_ : Fin (k j)), ⋀[R]^(a j) (Dual R (E j))) ⊗[R]
      (R ⊗[ℤ] Specht.orbitLattice (t j))) :=
  (dualDeterminantMap E hk t ha).dualMap ∘ₗ
    Tensor.tensorPowerPairing i ∘ₗ projectiveDeterminantMap hl v hs

/-- The restriction formula involves the actual determinant maps on both sides. -/
@[simp]
theorem canonicalPairing_apply (i : V →ₗ[R] (⨂[R] j, E j))
    (z : (⨂[R] (_ : Fin l), ⋀[R]^s V) ⊗[R] (R ⊗[ℤ] Specht.orbitLattice v))
    (u : ⨂[R] j, (⨂[R] (_ : Fin (k j)), ⋀[R]^(a j) (Dual R (E j))) ⊗[R]
      (R ⊗[ℤ] Specht.orbitLattice (t j))) :
    canonicalPairing E hk t ha hl v hs i z u =
      Tensor.tensorPowerPairing i (projectiveDeterminantMap hl v hs z)
        (dualDeterminantMap E hk t ha u) := rfl

/-- Equivariance into the contragredient simultaneous permutation action. -/
theorem canonicalPairing_reindex_left (i : V →ₗ[R] (⨂[R] j, E j))
    (σ : Equiv.Perm (Fin n))
    (z : (⨂[R] (_ : Fin l), ⋀[R]^s V) ⊗[R] (R ⊗[ℤ] Specht.orbitLattice v))
    (u : ⨂[R] j, (⨂[R] (_ : Fin (k j)), ⋀[R]^(a j) (Dual R (E j))) ⊗[R]
      (R ⊗[ℤ] Specht.orbitLattice (t j))) :
    canonicalPairing E hk t ha hl v hs i
      (TensorProduct.map LinearMap.id ((Specht.orbitAction v σ).baseChange R) z) u =
    canonicalPairing E hk t ha hl v hs i z
      (PiTensorProduct.map (fun j => TensorProduct.map LinearMap.id
        ((Specht.orbitAction (t j) σ.symm).baseChange R)) u) := by
  simp only [canonicalPairing_apply, projectiveDeterminantMap_reindex,
    Tensor.tensorPowerPairing_reindex_left, dualDeterminantMap_reindex]

end BostConjecture.Geometry
