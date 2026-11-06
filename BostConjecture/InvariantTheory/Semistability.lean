/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.InvariantTheory.Polynomial.Action
public import Mathlib.Analysis.Complex.Basic

/-!
# Polynomial orbit closure and geometric semistability

The closure is defined by all vanishing intrinsic polynomials. Geometric
semistability over ℂ means that zero is outside the orbit's Zariski closure.
The elementary invariant-to-semistability implication is proved here; the
converse and comparison with Euclidean closure are separate obligations.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.InvariantTheory

variable {K X : Type*} [Field K] [AddCommGroup X] [Module K X]

/-- The common zero locus of all polynomials vanishing on a set. -/
def polynomialZariskiClosure (A : Set X) : Set X :=
  {x | ∀ p : SymmetricAlgebra K (Module.Dual K X),
    (∀ y ∈ A, polynomialEval y p = 0) → polynomialEval x p = 0}

theorem subset_polynomialZariskiClosure (A : Set X) :
    A ⊆ polynomialZariskiClosure (K := K) A :=
  fun _ hx _ hp => hp _ hx

theorem polynomialZariskiClosure_mono {A B : Set X} (hAB : A ⊆ B) :
    polynomialZariskiClosure (K := K) A ⊆ polynomialZariskiClosure (K := K) B :=
  fun _ hx _ hp => hx _ (fun y hy => hp y (hAB hy))

@[simp]
theorem polynomialZariskiClosure_idem (A : Set X) :
    polynomialZariskiClosure (K := K) (polynomialZariskiClosure (K := K) A) =
      polynomialZariskiClosure (K := K) A := by
  apply Set.Subset.antisymm
  · intro x hx p hp
    exact hx p (fun y hy => hy p hp)
  · exact subset_polynomialZariskiClosure _

theorem polynomialEval_eq_on_closure {A : Set X}
    (p : SymmetricAlgebra K (Module.Dual K X)) (c : K)
    (hp : ∀ y ∈ A, polynomialEval y p = c) {x : X}
    (hx : x ∈ polynomialZariskiClosure (K := K) A) : polynomialEval x p = c := by
  have h := hx (p - algebraMap K _ c) (by intro y hy; simp [hp y hy])
  simpa only [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
    sub_eq_zero] using h

variable {G E : Type*} [Group G] [AddCommGroup E] [Module ℂ E]

/-- Geometric semistability of a vector under a complex linear group action. -/
def IsGeometricallySemistable (ρ : Representation ℂ G E) (x : E) : Prop :=
  (0 : E) ∉ polynomialZariskiClosure (K := ℂ) (Set.range (fun g => ρ g x))

theorem IsGeometricallySemistable.ne_zero {ρ : Representation ℂ G E} {x : E}
    (hx : IsGeometricallySemistable ρ x) : x ≠ 0 := by
  intro h
  apply hx
  apply subset_polynomialZariskiClosure
  exact ⟨1, by simp [h]⟩

/-- A positive-degree invariant nonzero at a vector excludes zero from its orbit closure. -/
theorem isGeometricallySemistable_of_homogeneousInvariant (ρ : Representation ℂ G E)
    (x : E) {d : ℕ} (hd : d ≠ 0) {p : SymmetricAlgebra ℂ (Module.Dual ℂ E)}
    (hp : p ∈ homogeneousInvariants ρ d) (hne : polynomialEval x p ≠ 0) :
    IsGeometricallySemistable ρ x := by
  intro hzero
  have hc : polynomialEval (0 : E) p = polynomialEval x p :=
    polynomialEval_eq_on_closure p (polynomialEval x p)
      (by rintro _ ⟨g, rfl⟩; exact polynomialEval_orbit_of_mem_invariants ρ hp.2 g x) hzero
  rw [polynomialEval_zero_of_mem_homogeneous hd hp.1] at hc
  exact hne hc.symm

/-- Geometric semistability is unchanged by multiplying a vector by a nonzero scalar. -/
theorem IsGeometricallySemistable.smul {ρ : Representation ℂ G E} {x : E}
    (hx : IsGeometricallySemistable ρ x) {c : ℂ} (hc : c ≠ 0) :
    IsGeometricallySemistable ρ (c • x) := by
  intro hz
  apply hx
  intro p hp
  have he := hz (polynomialPullback (c⁻¹ • LinearMap.id) p) (by
    rintro _ ⟨g, rfl⟩
    rw [polynomialEval_pullback]
    simpa only [LinearMap.smul_apply, LinearMap.id_apply, map_smul,
      smul_smul, mul_inv_cancel₀ hc, one_smul] using hp (ρ g x) ⟨g, rfl⟩)
  simpa only [polynomialEval_pullback, LinearMap.smul_apply, LinearMap.id_apply,
    smul_zero] using he

/-- Every nonzero vector on a semistable line is semistable. -/
theorem IsGeometricallySemistable.of_mem_span_singleton
    {ρ : Representation ℂ G E} {x y : E} (hx : IsGeometricallySemistable ρ x)
    (hy : y ∈ Submodule.span ℂ {x}) (hy0 : y ≠ 0) :
    IsGeometricallySemistable ρ y := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
  apply hx.smul
  intro hc
  exact hy0 (hc ▸ zero_smul ℂ x)

end BostConjecture.InvariantTheory
