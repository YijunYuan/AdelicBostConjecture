/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.InvariantTheory.Polynomial.HomogeneousComponents
public import BostConjecture.InvariantTheory.CompactAverage
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Haar averaging of intrinsic polynomials

The finite sum of homogeneous degree spaces carries a continuous pullback
representation. Point evaluations detect its finite-dimensional topology,
so the actual vector integral produces a polynomial with the expected
pointwise integral formula.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.InvariantTheory

open Module MeasureTheory

variable {K X : Type*} [Field K] [AddCommGroup X] [Module K X]

/-- Intrinsic polynomials of degree at most `N`. -/
def polynomialsOfDegreeLE (K X : Type*) [Field K] [AddCommGroup X] [Module K X]
    (N : ℕ) : Submodule K (SymmetricAlgebra K (Dual K X)) :=
  ⨆ d : Fin (N + 1), homogeneousPolynomials K X d.val

instance [FiniteDimensional K X] (N : ℕ) :
    FiniteDimensional K (polynomialsOfDegreeLE K X N) := by
  unfold polynomialsOfDegreeLE
  infer_instance

theorem homogeneousPolynomials_le_degreeLE {d N : ℕ} (h : d ≤ N) :
    homogeneousPolynomials K X d ≤ polynomialsOfDegreeLE K X N :=
  le_iSup_of_le ⟨d, Nat.lt_succ_of_le h⟩ le_rfl

theorem polynomialPullback_mem_degreeLE (f : X →ₗ[K] X) {N : ℕ}
    {p : SymmetricAlgebra K (Dual K X)} (hp : p ∈ polynomialsOfDegreeLE K X N) :
    polynomialPullback f p ∈ polynomialsOfDegreeLE K X N := by
  have h : polynomialsOfDegreeLE K X N ≤
      (polynomialsOfDegreeLE K X N).comap (polynomialPullback f).toLinearMap := by
    apply iSup_le
    exact fun d p hp => homogeneousPolynomials_le_degreeLE (Nat.le_of_lt_succ d.isLt)
      (polynomialPullback_mem_homogeneous f hp)
  exact h hp

theorem exists_mem_polynomialsOfDegreeLE [FiniteDimensional K X]
    (p : SymmetricAlgebra K (Dual K X)) : ∃ N, p ∈ polynomialsOfDegreeLE K X N := by
  classical
  let b := Module.finBasis K X
  let N := (SymmetricAlgebra.equivMvPolynomial b.dualBasis p).totalDegree
  refine ⟨N, ?_⟩
  rw [← sum_polynomialHomogeneousComponent b p]
  apply Submodule.sum_mem
  exact fun d hd => homogeneousPolynomials_le_degreeLE (Nat.le_of_lt_succ (Finset.mem_range.mp hd))
    (polynomialHomogeneousComponent_mem b d p)

/-- The actual inverse-pullback representation on bounded-degree polynomials. -/
def degreeLEPolynomialRepresentation {G : Type*} [Group G]
    (ρ : Representation K G X) (N : ℕ) : Representation K G (polynomialsOfDegreeLE K X N) :=
  (polynomialRepresentation ρ).subrepresentation (polynomialsOfDegreeLE K X N)
    (fun g _ hp => polynomialPullback_mem_degreeLE (ρ g⁻¹) hp)

@[simp]
theorem degreeLEPolynomialRepresentation_apply {G : Type*} [Group G]
    (ρ : Representation K G X) (N : ℕ) (g : G) (p : polynomialsOfDegreeLE K X N) :
    (degreeLEPolynomialRepresentation ρ N g p : SymmetricAlgebra K (Dual K X)) =
      polynomialPullback (ρ g⁻¹) p := rfl

/-- Over an infinite field, intrinsic polynomials are detected by all point evaluations. -/
theorem polynomialEval_ext [Infinite K] [FiniteDimensional K X]
    {p q : SymmetricAlgebra K (Dual K X)}
    (h : ∀ x, polynomialEval x p = polynomialEval x q) : p = q := by
  classical
  let b := Module.finBasis K X
  apply (SymmetricAlgebra.equivMvPolynomial b.dualBasis).injective
  apply MvPolynomial.funext
  intro a
  have hx := h (b.equivFun.symm a)
  simp only [polynomialEval_eq_aeval_equivMvPolynomial b] at hx
  have he : (fun i => b.coord i (b.equivFun.symm a)) = a := by
    funext i
    exact congrFun (b.equivFun.apply_symm_apply a) i
  simpa only [he, MvPolynomial.aeval_eq_eval] using hx

section Continuity

variable {T : Type*} [TopologicalSpace T]
  {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- A polynomial of a weakly continuous vector family is continuous. -/
theorem continuous_polynomialEval_family (f : T → E)
    (hf : ∀ ℓ : Dual ℂ E, Continuous fun t => ℓ (f t))
    (p : SymmetricAlgebra ℂ (Dual ℂ E)) :
    Continuous fun t => polynomialEval (f t) p := by
  induction p using SymmetricAlgebra.induction with
  | algebraMap c =>
    simpa only [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] using
      (continuous_const : Continuous fun _ : T => c)
  | ι ℓ => simpa only [polynomialEval_ι] using hf ℓ
  | mul p q hp hq =>
    simp only [map_mul]
    exact hp.mul hq
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq

/-- Evaluation detects continuity on every finite-dimensional polynomial subspace. -/
theorem continuous_polynomialSubspace_iff [FiniteDimensional ℂ E]
    (P : Submodule ℂ (SymmetricAlgebra ℂ (Dual ℂ E)))
    [TopologicalSpace P] [IsTopologicalAddGroup P] [ContinuousSMul ℂ P]
    [T2Space P] [FiniteDimensional ℂ P]
    (f : T → P) : Continuous f ↔
      ∀ x : E, Continuous fun t => polynomialEval x (f t : SymmetricAlgebra ℂ (Dual ℂ E)) := by
  let ev : P →ₗ[ℂ] (E → ℂ) :=
    LinearMap.pi (fun x => (polynomialEval x).toLinearMap.comp P.subtype)
  have hi : Function.Injective ev := by
    intro p q h
    apply Subtype.ext
    apply polynomialEval_ext
    exact fun x => congrFun h x
  have he := ev.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hi)
  rw [he.isEmbedding.continuous_iff]
  exact continuous_pi_iff

/-- Continuity of the concrete bounded-degree inverse-pullback orbit. -/
theorem continuous_degreeLEPolynomialRepresentation
    {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [FiniteDimensional ℂ E] (ρ : Representation ℂ H E)
    (hc : ∀ x (ℓ : Dual ℂ E), Continuous fun h => ℓ (ρ h x)) (N : ℕ)
    [TopologicalSpace (polynomialsOfDegreeLE ℂ E N)]
    [IsTopologicalAddGroup (polynomialsOfDegreeLE ℂ E N)]
    [ContinuousSMul ℂ (polynomialsOfDegreeLE ℂ E N)]
    [T2Space (polynomialsOfDegreeLE ℂ E N)]
    (p : polynomialsOfDegreeLE ℂ E N) :
    Continuous fun h => degreeLEPolynomialRepresentation ρ N h p := by
  apply (continuous_polynomialSubspace_iff _ _).mpr
  intro x
  simp only [degreeLEPolynomialRepresentation_apply, polynomialEval_pullback]
  exact continuous_polynomialEval_family (fun h => ρ h⁻¹ x)
    (fun ℓ => (hc x ℓ).comp continuous_inv) p

end Continuity

/-- Actual averaging of a polynomial in a continuous compact linear representation.
The resulting polynomial is fixed and satisfies the pointwise Haar integral formula. -/
theorem exists_compactInvariant_polynomial
    {H E : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CompactSpace H] [MeasurableSpace H] [BorelSpace H]
    [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (μ : Measure H) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (ρ : Representation ℂ H E)
    (hc : ∀ x (ℓ : Dual ℂ E), Continuous fun h => ℓ (ρ h x))
    (q : SymmetricAlgebra ℂ (Dual ℂ E)) :
    ∃ r : SymmetricAlgebra ℂ (Dual ℂ E),
      r ∈ (polynomialRepresentation ρ).invariants ∧
      ∀ x, polynomialEval x r = ∫ h, polynomialEval (ρ h⁻¹ x) q ∂μ := by
  obtain ⟨N, hq⟩ := exists_mem_polynomialsOfDegreeLE q
  let P := polynomialsOfDegreeLE ℂ E N
  let e := (Module.finBasis ℂ P).equivFun
  let : NormedAddCommGroup P := NormedAddCommGroup.induced _ _ e e.injective
  let : NormedSpace ℂ P := NormedSpace.induced ℂ _ _ e
  let σ := degreeLEPolynomialRepresentation ρ N
  let q' : P := ⟨q, hq⟩
  have hc' : Continuous fun h => σ h q' :=
    continuous_degreeLEPolynomialRepresentation ρ hc N q'
  let r := compactRepresentationAverage μ σ q'
  refine ⟨r.val, ?_, ?_⟩
  · intro h
    exact congrArg Subtype.val (compactRepresentationAverage_mem_invariants μ σ q' hc' h)
  · intro x
    simpa only [LinearMap.comp_apply, Submodule.subtype_apply, AlgHom.toLinearMap_apply,
      σ, degreeLEPolynomialRepresentation_apply, polynomialEval_pullback] using
      linearMap_compactRepresentationAverage μ σ q' hc'
        ((polynomialEval x).toLinearMap.comp P.subtype)

end BostConjecture.InvariantTheory
