module

public import BostConjecture.InvariantTheory.PolynomialAction
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Homogeneous components of intrinsic polynomials

The coordinate projections transport to the existing symmetric algebra of
the dual. Their degree characterization gives naturality under every linear
pullback and extraction of a positive-degree invariant.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.InvariantTheory

open Module

variable {K X ι : Type*} [Field K] [AddCommGroup X] [Module K X]
  [Fintype ι] [DecidableEq ι]

/-- The existing intrinsic degree space is exactly the usual coordinate degree space. -/
theorem map_homogeneousPolynomials_equivMvPolynomial (b : Basis ι K X) (d : ℕ) :
    (homogeneousPolynomials K X d).map
      (SymmetricAlgebra.equivMvPolynomial b.dualBasis).toLinearMap =
        MvPolynomial.homogeneousSubmodule ι K d := by
  have h₁ : (LinearMap.range (SymmetricAlgebra.ι K (Dual K X))).map
      (SymmetricAlgebra.equivMvPolynomial b.dualBasis).toLinearMap =
        MvPolynomial.homogeneousSubmodule ι K 1 := by
    rw [MvPolynomial.homogeneousSubmodule_one_eq_span_X]
    apply le_antisymm
    · rintro _ ⟨_, ⟨ℓ, rfl⟩, rfl⟩
      rw [← b.dualBasis.sum_repr ℓ, map_sum, map_sum]
      apply Submodule.sum_mem
      intro i _
      rw [map_smul, map_smul]
      apply Submodule.smul_mem
      exact Submodule.subset_span ⟨i, SymmetricAlgebra.equivMvPolynomial_ι_apply _ _ |>.symm⟩
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact ⟨SymmetricAlgebra.ι K _ (b.dualBasis i), ⟨b.dualBasis i, rfl⟩,
        SymmetricAlgebra.equivMvPolynomial_ι_apply _ _⟩
  unfold homogeneousPolynomials
  change Submodule.map (SymmetricAlgebra.equivMvPolynomial b.dualBasis).toAlgHom.toLinearMap
    ((LinearMap.range (SymmetricAlgebra.ι K (Dual K X))) ^ d) = _
  rw [Submodule.map_pow]
  change ((LinearMap.range (SymmetricAlgebra.ι K (Dual K X))).map
    (SymmetricAlgebra.equivMvPolynomial b.dualBasis).toLinearMap) ^ d = _
  rw [h₁, MvPolynomial.homogeneousSubmodule_one_pow]

/-- Projection onto the degree `d` part of the intrinsic polynomial algebra. -/
def polynomialHomogeneousComponent (b : Basis ι K X) (d : ℕ) :
    SymmetricAlgebra K (Dual K X) →ₗ[K] SymmetricAlgebra K (Dual K X) :=
  (SymmetricAlgebra.equivMvPolynomial b.dualBasis).symm.toLinearMap.comp
    ((MvPolynomial.homogeneousComponent d).comp
      (SymmetricAlgebra.equivMvPolynomial b.dualBasis).toLinearMap)

theorem polynomialHomogeneousComponent_mem (b : Basis ι K X) (d : ℕ)
    (p : SymmetricAlgebra K (Dual K X)) :
    polynomialHomogeneousComponent b d p ∈ homogeneousPolynomials K X d := by
  have h := MvPolynomial.homogeneousComponent_mem d
    (SymmetricAlgebra.equivMvPolynomial b.dualBasis p)
  rw [← map_homogeneousPolynomials_equivMvPolynomial b d] at h
  obtain ⟨q, hq, he⟩ := h
  change (SymmetricAlgebra.equivMvPolynomial b.dualBasis).symm
    (MvPolynomial.homogeneousComponent d (SymmetricAlgebra.equivMvPolynomial b.dualBasis p)) ∈ _
  change SymmetricAlgebra.equivMvPolynomial b.dualBasis q = _ at he
  rw [← he, AlgEquiv.symm_apply_apply]
  exact hq

theorem polynomialHomogeneousComponent_of_mem (b : Basis ι K X) {d n : ℕ}
    {p : SymmetricAlgebra K (Dual K X)} (hp : p ∈ homogeneousPolynomials K X n) :
    polynomialHomogeneousComponent b d p = if d = n then p else 0 := by
  have h : SymmetricAlgebra.equivMvPolynomial b.dualBasis p ∈
      MvPolynomial.homogeneousSubmodule ι K n := by
    rw [← map_homogeneousPolynomials_equivMvPolynomial b n]
    exact ⟨p, hp, rfl⟩
  change (SymmetricAlgebra.equivMvPolynomial b.dualBasis).symm
    (MvPolynomial.homogeneousComponent d (SymmetricAlgebra.equivMvPolynomial b.dualBasis p)) = _
  rw [MvPolynomial.homogeneousComponent_of_mem h]
  split <;> simp_all

/-- Every polynomial is a finite sum of its intrinsic homogeneous components. -/
theorem sum_polynomialHomogeneousComponent (b : Basis ι K X)
    (p : SymmetricAlgebra K (Dual K X)) :
    ∑ d ∈ Finset.range ((SymmetricAlgebra.equivMvPolynomial b.dualBasis p).totalDegree + 1),
      polynomialHomogeneousComponent b d p = p := by
  change ∑ d ∈ _, (SymmetricAlgebra.equivMvPolynomial b.dualBasis).symm
    (MvPolynomial.homogeneousComponent d (SymmetricAlgebra.equivMvPolynomial b.dualBasis p)) = _
  rw [← map_sum, MvPolynomial.sum_homogeneousComponent, AlgEquiv.symm_apply_apply]

/-- A degree-preserving linear map commutes with the component projections. -/
theorem polynomialHomogeneousComponent_comm
    {Y κ : Type*} [AddCommGroup Y] [Module K Y] [Fintype κ] [DecidableEq κ]
    (b : Basis ι K X) (c : Basis κ K Y)
    (T : SymmetricAlgebra K (Dual K Y) →ₗ[K] SymmetricAlgebra K (Dual K X))
    (hT : ∀ d p, p ∈ homogeneousPolynomials K Y d → T p ∈ homogeneousPolynomials K X d)
    (d : ℕ) (p : SymmetricAlgebra K (Dual K Y)) :
    polynomialHomogeneousComponent b d (T p) = T (polynomialHomogeneousComponent c d p) := by
  let D := Finset.range ((SymmetricAlgebra.equivMvPolynomial c.dualBasis p).totalDegree + 1)
  have hs : ∑ j ∈ D, polynomialHomogeneousComponent c j p = p :=
    sum_polynomialHomogeneousComponent c p
  calc
    _ = ∑ j ∈ D, polynomialHomogeneousComponent b d
        (T (polynomialHomogeneousComponent c j p)) := by rw [← map_sum, ← map_sum, hs]
    _ = ∑ j ∈ D, T (polynomialHomogeneousComponent c d
        (polynomialHomogeneousComponent c j p)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [polynomialHomogeneousComponent_of_mem b
          (hT j _ (polynomialHomogeneousComponent_mem c j p)),
        polynomialHomogeneousComponent_of_mem c (polynomialHomogeneousComponent_mem c j p)]
      split <;> simp
    _ = _ := by rw [← map_sum, ← map_sum, hs]

/-- Linear pullback commutes with every homogeneous projection. -/
theorem polynomialHomogeneousComponent_pullback
    {Y κ : Type*} [AddCommGroup Y] [Module K Y] [Fintype κ] [DecidableEq κ]
    (b : Basis ι K X) (c : Basis κ K Y) (f : X →ₗ[K] Y) (d : ℕ)
    (p : SymmetricAlgebra K (Dual K Y)) :
    polynomialHomogeneousComponent b d (polynomialPullback f p) =
      polynomialPullback f (polynomialHomogeneousComponent c d p) :=
  polynomialHomogeneousComponent_comm b c (polynomialPullback f).toLinearMap
    (fun _ _ hp => polynomialPullback_mem_homogeneous f hp) d p

/-- The component maps are independent of the basis used to construct them. -/
theorem polynomialHomogeneousComponent_eq
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (b : Basis ι K X) (c : Basis κ K X) (d : ℕ) :
    polynomialHomogeneousComponent b d = polynomialHomogeneousComponent c d := by
  ext p
  exact polynomialHomogeneousComponent_comm b c LinearMap.id (fun _ _ hp => hp) d p

/-- A component of an invariant is invariant for the existing representation. -/
theorem polynomialHomogeneousComponent_mem_invariants
    {G : Type*} [Group G] (ρ : Representation K G X) (b : Basis ι K X)
    {p : SymmetricAlgebra K (Dual K X)} (hp : p ∈ (polynomialRepresentation ρ).invariants)
    (d : ℕ) : polynomialHomogeneousComponent b d p ∈ homogeneousInvariants ρ d := by
  refine ⟨polynomialHomogeneousComponent_mem b d p, ?_⟩
  intro g
  change polynomialPullback (ρ g⁻¹) (polynomialHomogeneousComponent b d p) = _
  rw [← polynomialHomogeneousComponent_pullback b b]
  exact congrArg (polynomialHomogeneousComponent b d) (hp g)

/-- Intrinsic evaluation agrees with evaluation in dual-basis coordinates. -/
theorem polynomialEval_eq_aeval_equivMvPolynomial (b : Basis ι K X) (x : X)
    (p : SymmetricAlgebra K (Dual K X)) :
    polynomialEval x p = MvPolynomial.aeval (fun i => b.coord i x)
      (SymmetricAlgebra.equivMvPolynomial b.dualBasis p) := by
  have h : (MvPolynomial.aeval (fun i => b.coord i x)).comp
      (SymmetricAlgebra.equivMvPolynomial b.dualBasis).toAlgHom = polynomialEval x := by
    apply SymmetricAlgebra.algHom_ext
    apply b.dualBasis.ext
    intro i
    change MvPolynomial.aeval (fun i => b.coord i x)
      (SymmetricAlgebra.equivMvPolynomial b.dualBasis
        (SymmetricAlgebra.ι K _ (b.dualBasis i))) =
      polynomialEval x (SymmetricAlgebra.ι K _ (b.dualBasis i))
    rw [SymmetricAlgebra.equivMvPolynomial_ι_apply, MvPolynomial.aeval_X, polynomialEval_ι]
    simp
  exact (DFunLike.congr_fun h p).symm

/-- The constant component is exactly evaluation at the zero vector. -/
theorem polynomialHomogeneousComponent_zero (b : Basis ι K X)
    (p : SymmetricAlgebra K (Dual K X)) :
    polynomialHomogeneousComponent b 0 p =
      algebraMap K _ (polynomialEval (0 : X) p) := by
  change (SymmetricAlgebra.equivMvPolynomial b.dualBasis).symm
    (MvPolynomial.homogeneousComponent 0 (SymmetricAlgebra.equivMvPolynomial b.dualBasis p)) = _
  rw [MvPolynomial.homogeneousComponent_zero]
  change (SymmetricAlgebra.equivMvPolynomial b.dualBasis).symm (algebraMap K _ _) = _
  rw [AlgEquiv.commutes]
  congr 1
  rw [polynomialEval_eq_aeval_equivMvPolynomial b]
  simp
  rfl

/-- Extraction of a positive-degree invariant from a separating invariant.
No orbit-closure or averaging conclusion is assumed here. -/
theorem exists_homogeneousInvariant_of_invariant
    {G : Type*} [Group G] [FiniteDimensional K X] (ρ : Representation K G X)
    {p : SymmetricAlgebra K (Dual K X)} {x : X}
    (hp : p ∈ (polynomialRepresentation ρ).invariants)
    (h₀ : polynomialEval (0 : X) p = 0) (hx : polynomialEval x p ≠ 0) :
    ∃ d : ℕ, 0 < d ∧ ∃ q : homogeneousInvariants ρ d,
      polynomialEval x (q : SymmetricAlgebra K (Dual K X)) ≠ 0 := by
  classical
  let b := Module.finBasis K X
  have hs := congrArg (polynomialEval x) (sum_polynomialHomogeneousComponent b p)
  rw [map_sum] at hs
  obtain ⟨d, hd, hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hs.trans_ne hx)
  have hd₀ : d ≠ 0 := by
    rintro rfl
    rw [polynomialHomogeneousComponent_zero, h₀, map_zero, map_zero] at hv
    exact hv rfl
  exact ⟨d, Nat.pos_of_ne_zero hd₀,
    ⟨polynomialHomogeneousComponent b d p,
      polynomialHomogeneousComponent_mem_invariants ρ b hp d⟩, hv⟩

end BostConjecture.InvariantTheory
