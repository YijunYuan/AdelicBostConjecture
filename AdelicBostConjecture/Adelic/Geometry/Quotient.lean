/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import AdelicBostConjecture.Adelic.Geometry.Nonvanishing
public import AdelicBostConjecture.Adelic.Geometry.Dual
public import AdelicBostConjecture.Adelic.Geometry.ScalarExtension

/-!
# Geometric tensor quotients and original-field pairings

Geometric quotient semistability gives geometric semistability of the original
dual inclusion into the tensor product of dual factors. The proof uses the full
special-linear groups over the algebraic closure and the actual tensor and dual
base-change maps. Applying the subspace producer gives the pairings required by
the quotient consequence of this paper's Theorem 6.2.
-/

@[expose] public section

noncomputable section

namespace AdelicBostConjecture.Adelic.Geometry

open Module PiTensorProduct AdelicBostConjecture.Geometry
open ArakelovGeometry.InvariantTheory
open scoped TensorProduct

variable {K : Type*} [Field K] {ι : Type*}
  (E : ι → Type*) [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]
  [∀ i, FiniteDimensional K (E i)] [∀ i, Nontrivial (E i)]
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Nontrivial V]

/-- The geometric quotient predicate implies the geometric subspace predicate
for the original dual inclusion, with full SL groups on the dual factors. -/
theorem geometricSemistability_dualTensor_of_quotient [Finite ι]
    (q : (⨂[K] i, E i) →ₗ[K] V)
    (h : IsGeometricallySemistableTensorQuotient E q) :
    IsGeometricallySemistableTensorSubspace (fun i ↦ Dual K (E i))
      ((dualDistribEquivOfProjective K E).symm.toLinearMap ∘ₗ q.dualMap) := by
  let L := AlgebraicClosure K
  change IsQuotientSemistable (tensorSLRepresentation (fun i ↦ L ⊗[K] E i))
    ((q.baseChange L) ∘ₗ (ArakelovGeometry.tensorBaseChangeEquiv K L E).symm.toLinearMap) at h
  rw [tensorBaseChangeEquiv_eq] at h
  have hdual := isPluckerSemistable_dualTensor_of_isQuotientSemistable _ _ h
  change IsPluckerSemistable (tensorSLRepresentation (fun i ↦ L ⊗[K] Dual K (E i)))
    ((ArakelovGeometry.tensorBaseChangeEquiv K L (fun i ↦ Dual K (E i))).toLinearMap ∘ₗ
      ((dualDistribEquivOfProjective K E).symm.toLinearMap ∘ₗ q.dualMap).baseChange L)
  rw [tensorBaseChangeEquiv_eq]
  apply isPluckerSemistable_of_intertwining _ _ _ _
    (Arithmetic.dualBaseChangeEquiv K L V)
    (PiTensorProduct.congr (fun i ↦ Arithmetic.dualBaseChangeEquiv K L (E i))).toLinearMap
    _ _ hdual
  · intro g
    exact ⟨fun i ↦ SpecialLinearGroup.congr_linearEquiv
      (Arithmetic.dualBaseChangeEquiv K L (E i)) (g i),
      tensorSLRepresentation_congr _ _ g⟩
  · exact dualTensorInclusion_baseChange L E q

/-- A geometrically semistable quotient yields nonzero canonical pairings of
its original-field dual inclusion at every positive multiple of one degree. -/
theorem exists_canonicalPairing_nonzero_sequence_of_geometricQuotient [CharZero K] [Fintype ι]
    (q : (⨂[K] i, E i) →ₗ[K] V)
    (h : IsGeometricallySemistableTensorQuotient E q) :
    ∃ d₀ : ℕ, 0 < d₀ ∧ Module.finrank K (Dual K V) ∣ d₀ ∧
      (∀ i, Module.finrank K (Dual K (E i)) ∣ d₀) ∧
      ∀ r : ℕ, 0 < r → ∃ (l : ℕ) (k : ι → ℕ) (hl : 0 < l) (hk : ∀ i, 0 < k i)
        (t : ∀ i, OAI.Saxl.Tableau (d₀ * r)
          (Specht.rectangle (Module.finrank K (Dual K (E i))) (k i)))
        (v : OAI.Saxl.Tableau (d₀ * r)
          (Specht.rectangle (Module.finrank K (Dual K V)) l)),
        canonicalPairing (fun i ↦ Dual K (E i)) hk t (fun i p ↦ by simp)
          hl v (fun p ↦ by simp)
          ((dualDistribEquivOfProjective K E).symm.toLinearMap ∘ₗ q.dualMap) ≠ 0 :=
  exists_canonicalPairing_nonzero_sequence_of_geometricSemistability _ _
    (geometricSemistability_dualTensor_of_quotient E q h)

end AdelicBostConjecture.Adelic.Geometry
