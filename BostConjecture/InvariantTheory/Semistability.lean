module

public import BostConjecture.InvariantTheory.PolynomialAction
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

end BostConjecture.InvariantTheory
