/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Geometry.Invariants.Dual
public import BostConjecture.Geometry.Invariants.DualSpecialLinear
public import BostConjecture.Geometry.Contraction.Basic

/-!
# Nonvanishing of the actual canonical determinant contraction

Invariant tensors detect a nonzero value of the canonical determinant
contraction. This gives the nonvanishing input for its injectivity proof.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Geometry

open Module PiTensorProduct InvariantTheory
open scoped TensorProduct

section Frame

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [Module.Finite R M] [Module.Projective R M] {n a k : ℕ}

/-- The already glued determinant map agrees with its actual free-frame formula. -/
theorem projectiveDeterminantMap_eq_free (hk : 0 < k)
    (t : OAI.Saxl.Tableau n (Specht.rectangle a k))
    (ha : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = a) (b : Basis (Fin a) R M) :
    projectiveDeterminantMap hk t ha = freeDeterminantMap hk t b := by
  apply (existsUnique_projectiveDeterminantMap hk t ha).unique
    (fun f c => projectiveDeterminantMap_baseChange hk t ha f c)
  intro f c
  apply LinearMap.ext
  intro x
  apply (Tensor.baseChangeEquiv R (Localization.Away f) (fun _ : Fin n => M)).injective
  simpa only [determinantChart, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply] using
      LinearMap.congr_fun (freeDeterminantMap_baseChange hk t b c) x

/-- The projective determinant map and the rectangular lattice have identical
images in a global frame. -/
theorem mem_range_projectiveDeterminantMap_iff (hk : 0 < k)
    (t : OAI.Saxl.Tableau n (Specht.rectangle a k))
    (ha : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = a) (b : Basis (Fin a) R M)
    (w : ⨂[R] (_ : Fin n), M) :
    w ∈ LinearMap.range (projectiveDeterminantMap hk t ha) ↔
      w ∈ LinearMap.range (freeLatticeMap hk t b) := by
  rw [projectiveDeterminantMap_eq_free hk t ha b]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(TensorProduct.lid R _)
      ((LinearEquiv.rTensor _ (determinantPowerCoordinates k b)) x), rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨tprod R (fun _ : Fin k => exteriorPower.ιMulti R a b) ⊗ₜ[R] x,
      freeDeterminantMap_basis hk t b x⟩

end Frame

variable (F : Type) [Field F] {ι : Type*} [Fintype ι]
  (E : ι → Type*) [∀ i, AddCommGroup (E i)] [∀ i, Module F (E i)]

/-- The actual independent special-linear action on the ambient tensor product. -/
def specialLinearTensorRepresentation :
    Representation F (∀ i, SpecialLinearGroup F (E i)) (⨂[F] i, E i) :=
  independentTensorRepresentation (fun i =>
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
      SpecialLinearGroup.toLinearEquiv : Representation F (SpecialLinearGroup F (E i)) (E i)))

variable {F E} [CharZero F] [IsAlgClosed F] [∀ i, FiniteDimensional F (E i)]
  {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]

attribute [local instance] tensorTargetAddCommGroup

/-- A nonzero actual invariant polynomial forces the already constructed
canonical determinant contraction to be nonzero over an algebraic closure. -/
theorem canonicalPairing_ne_zero_of_invariant
    (A : V →ₗ[F] (⨂[F] i, E i)) {n s l : ℕ} {a k : ι → ℕ}
    (hspos : 0 < s) (hapos : ∀ i, 0 < a i) (hl : 0 < l) (hk : ∀ i, 0 < k i)
    (t : ∀ i, OAI.Saxl.Tableau n (Specht.rectangle (a i) (k i)))
    (v : OAI.Saxl.Tableau n (Specht.rectangle s l))
    (ha : ∀ i (q : PrimeSpectrum F), Module.rankAtStalk (Dual F (E i)) q = a i)
    (hs : ∀ q : PrimeSpectrum F, Module.rankAtStalk V q = s)
    (bV : Basis (Fin s) F V) (bE : ∀ i, Basis (Fin (a i)) F (Dual F (E i)))
    {p : SymmetricAlgebra F (Dual F (V →ₗ[F] (⨂[F] i, E i)))}
    (hp : p ∈ homogeneousInvariants
      (homSpecialLinearRepresentation (specialLinearTensorRepresentation F E)) n)
    (hpA : polynomialEval A p ≠ 0) :
    canonicalPairing E hk t ha hl v hs A ≠ 0 := by
  let ρ := fun i =>
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
      SpecialLinearGroup.toLinearEquiv : Representation F (SpecialLinearGroup F (E i)) (E i))
  obtain ⟨x, w, hx, hw, hxw⟩ := exists_independent_dual_pairing ρ A hp hpA
  have hxmem : x ∈ LinearMap.range (projectiveDeterminantMap hl v hs) :=
    (mem_range_projectiveDeterminantMap_iff hl v hs bV x).mpr
      ((mem_range_freeLatticeMap_iff_specialLinear_fixed hspos hl v bV x).mpr hx)
  have hwmem (i) : w i ∈ LinearMap.range (projectiveDeterminantMap (hk i) (t i) (ha i)) := by
    apply (mem_range_projectiveDeterminantMap_iff (hk i) (t i) (ha i) (bE i) (w i)).mpr
    apply mem_range_freeLatticeMap_of_dual_specialLinear_fixed (hapos i) (hk i) (t i) (bE i)
    intro g
    simpa [ρ] using hw i g⁻¹
  obtain ⟨z, hz⟩ := hxmem
  choose u hu using hwmem
  intro hzero
  apply hxw
  have he := congrArg (fun B => B z (tprod F u)) hzero
  simpa only [canonicalPairing_apply, dualDeterminantMap, LinearMap.comp_apply,
    LinearEquiv.coe_coe, map_tprod, hu, hz, LinearMap.zero_apply] using he

end BostConjecture.Geometry
